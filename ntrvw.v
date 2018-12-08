(******************************************************************************)
(* This file provides a class of relations interpreted as multivalued         *)
(* functions. The main difference between relations and multivalued functions *)
(* is how they are composed, the composition for multivalued functions is     *)
(* Chosen such that it works well with realizability. The difference          *)
(* between multifunction and relational composition is that for the latter    *)
(* the whole image of s under f is required to be included in the domain of g *)
(* for f \o g s r to be true. Note that in ssreflect, \o is a notation for the*)
(* composition of regular functions, this notation is remapped to \o_f.       *)
(*            interview Q     == a type A and a multivalued function (i.e. a  *)
(*                               relation that assigns to each element q from *)
(*                               Q a set of answers a from A that answer the  *)
(*                               question q. The relation is called the       *)
(*                               conversation of the interview and the only   *)
(*                               requirement is that is that it is cototal,   *)
(*                               i.e. the interviewe can not spoken unasked.  *)
(*     a \is_response_to q    == where q is from a set Q and a is from an     *)
(*                               interview over Q means that the relation of  *)
(*                               the interview marks a as a valid answer to q *)
(*        get_question a      == gets a question that results in the answer a *)
(*        F \realizes f       == the usual realizability relation.            *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrfun seq.
Require Import all_mf.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module interview_mixin.
Structure type questions answers := Pack {
conversation: questions ->> answers;
only_respond : conversation \is_cototal;
}.
End interview_mixin.

Module interview.
Structure type (questions: Type) := Pack {
answers:> Type;
mixin: interview_mixin.type questions answers;
}.
End interview.
Coercion interview.answers: interview.type >-> Sortclass.
Coercion interview.mixin : interview.type >-> interview_mixin.type.
Definition conversation Q (C: interview.type Q) :=
	interview_mixin.conversation (interview.mixin C).
Notation "a '\is_response_to' q 'in' C" := (conversation C q a) (at level 2).
Notation "a \is_response_to q" := (a \is_response_to  q in _) (at level 2).
Definition only_respond Q (A: interview.type Q) := (interview_mixin.only_respond A).
Arguments only_respond {Q} {A}.
Notation get_question a := (only_respond a).
Notation interview := interview.type.

Section interviews.
Lemma id_sur S: (@mf_id S) \is_cototal.
Proof. by move => c; exists c. Qed.

Definition id_interview_mixin S: interview_mixin.type S S.
Proof. exists mf_id; exact/id_sur. Defined.

Definition id_interview S:= interview.Pack (id_interview_mixin S).

Definition fun_interview_mixin Q A (f: A -> Q): interview_mixin.type Q A.
Proof. exists (F2MF f\^-1); exact /cotot_tot_inv/F2MF_tot. Defined.

Definition fun_interview Q A (f: A -> Q):= interview.Pack (fun_interview_mixin f).
Arguments fun_interview: clear implicits.

Canonical sub_interview A (P: mf_subset.type A):= fun_interview A {a: A | P a} (@projT1 A P).

Context Q (A : interview Q).

Definition comp_conv (D: interview A):= (conversation D) \o_R (conversation A).

Lemma comp_conv_sur (D: interview A): (comp_conv D) \is_cototal.
Proof.
move => d''; have [d dnd'']:= get_question d''; have [q qnd]:= get_question d;by exists q; exists d.
Qed.

Definition combine_interview_mixin (D: interview A): interview_mixin.type Q D.
Proof. exists (comp_conv D); exact/comp_conv_sur. Defined.

Definition cmbn_ntrvw (D: interview A) := interview.Pack (combine_interview_mixin D).

Context Q' (A': interview Q').
Definition prod_conv := (conversation A) ** (conversation A').

Lemma prod_conv_sur: prod_conv \is_cototal.
Proof. by apply/fprd_cotot/only_respond/only_respond. Qed.

Definition prod_interview_mixin : interview_mixin.type (Q * Q') (A * A').
Proof. by exists prod_conv; exact/prod_conv_sur. Defined.

Canonical prod_interview := interview.Pack prod_interview_mixin.

Definition sum_conv:= (conversation A) +s+ (conversation A').

Lemma sum_conv_sur: sum_conv \is_cototal.
Proof.
move => [a | b] /=.
	by have [c cna]:= get_question a; exists (inl c).
by have [c cnab]:= get_question b; exists (inr c).
Qed.

Definition sum_interview_mixin: interview_mixin.type (Q + Q') (A + A').
Proof. by exists sum_conv; exact /sum_conv_sur. Defined.

Canonical sum_interview := interview.Pack sum_interview_mixin.

Fixpoint list_conv_prp (K: seq Q) (L: seq A) := match K with
	| nil => L = nil
	| (q :: K') => match L with
		| nil => False
		| (a :: L') => a \is_response_to q /\ list_conv_prp K' L'
	end
end.

Definition list_conv := make_mf list_conv_prp.

Lemma list_conv_sur: list_conv \is_cototal.
Proof.
elim => [ | a L [K lcKL]]; first by exists nil.
have [q qna] := get_question a.
by exists (q :: K).
Qed.

Definition list_interview_mixin: interview_mixin.type (seq Q) (seq A).
Proof. by exists list_conv; exact /list_conv_sur. Defined.

Definition list_interview := interview.Pack list_interview_mixin.
End interviews.

Section realizer.
Context Q (A: interview Q) Q' (A': interview Q').

Definition rlzr (F: Q ->> Q') (f: A ->> A') :=
		(forall q a, a \is_response_to q -> a \from dom f -> q \from dom F /\
		forall Fq, F q Fq -> exists fa, fa \is_response_to Fq /\ f a fa).
Notation "F '\realizes' f" := (rlzr F f) (at level 2).
Definition mf_rlzr := make_mf rlzr.

Global Instance rlzr_prpr:
	Proper (@equiv Q Q' ==> @equiv A A' ==> iff) (@rlzr).
Proof.
move => F G FeG f g feg.
split => rlzr q a aaq afd.
	have afd': a \from dom f by rewrite feg.
	split => [ | q' Gqq']; first by have [[q' Fqq'] _]:= rlzr q a aaq afd'; exists q'; rewrite -FeG.
	have [_ prp]:= rlzr q a aaq afd'.
	have [ | a' [a'aq' faa']]:= prp q' _; first by rewrite FeG.
	by exists a'; rewrite -feg.
have afd': a \from dom g by rewrite -feg.
split => [ | q' Gqq']; first by have [[q' Fqq'] _]:= rlzr q a aaq afd'; exists q'; rewrite FeG.
have [_ prp]:= rlzr q a aaq afd'.
have [ | a' [a'aq' faa']]:= prp q' _; first by rewrite -FeG.
by exists a'; rewrite feg.
Qed.

Lemma split_rlzr (F: Q ->> Q') (f: A ->> A'):
		(forall q a, a \is_response_to q -> a \from dom f -> q \from dom F) ->
		(forall q a, a\is_response_to q -> a \from dom f -> forall Fq, F q Fq -> exists fa, fa \is_response_to Fq /\ f a fa) -> F \realizes f.
Proof.
by move => dm val q a arq afd; split => [ | Fq FqFq]; [apply/dm/afd | apply/val/FqFq].
Qed.

Lemma rlzr_dom (F: Q ->> Q') (f: A ->> A') q a: F \realizes f ->
	a \is_response_to q -> a \from dom f -> q \from dom F.
Proof. by move => Frf arq qfd; have []:= Frf q a arq qfd. Qed.

Lemma rlzr_val (F: Q ->> Q') (f: A ->> A') q a Fq: F \realizes f ->
	a \is_response_to q -> a \from dom f -> F q Fq -> exists fa, fa \is_response_to Fq /\ f a fa.
Proof. by move => Frf arq qfd FqFq; have [_ prp]:= Frf q a arq qfd; apply prp. Qed.
End realizer.
Arguments mf_rlzr {Q} {A} {Q'} {A'}.
Notation "f '\is_realized_by' F" := (rlzr F f) (at level 2).
Notation "F '\realizes' f" := (rlzr F f) (at level 2).

Section realizers.
Lemma id_rlzr_tight Q Q' (F G: id_interview Q ->> id_interview Q'):
	F \realizes G <-> F \tightens G.
Proof.
split =>[rlzr s sfd | tight q a <- afd].
	split => [ | t Fst]; first exact /rlzr_dom/sfd.
	by have [ | Fs [<-]]// :=rlzr_val rlzr _ sfd Fst.
split => [ | Fq FqFq]; first exact/tight_dom/afd.
exists Fq; split => //; exact/tight_val/FqFq.
Qed.

Context Q (A: interview Q) Q' (A': interview Q').

Lemma rlzr_val_sing (f: A ->> A') F: f \is_singlevalued -> F \realizes f ->
	forall q a q' a', a \is_response_to q -> f a a' -> F q q' -> a' \is_response_to q'.
Proof.
move => sing rlzr q a q' a' aaq faa' Fqq'.
have [ | _ prp]:= rlzr q a aaq; first by exists a'.
have [d' [d'aq' fad']]:= prp q' Fqq'.
by rewrite (sing a a' d').
Qed.

Lemma rlzr_comp Q'' (A'': interview Q'') G F (f: A ->> A') (g: A' ->> A''):
	G \realizes g -> F \realizes f -> (G \o F) \realizes (g \o f).
Proof.
move => Grg Frf q a arq [gfa [[fa [fafa gfagfa]]] subs].
have afd: a \from dom f by exists fa.
split; last first.
	move => GFq [[Fq [FqFq GFqGFq]] subs'].
	have [d' [d'aq' fad']]:= rlzr_val Frf arq afd FqFq.
	have [d'' [d''aq'' gd'd'']]:= rlzr_val Grg d'aq' (subs d' fad') GFqGFq.
	by exists d''; split => //; split; first by exists d'.
have [[q' Fqq'] prp]:= Frf q a arq afd.
have [d' [d'aq' fad']]:= prp q' Fqq'.
have [[q'' Gq'q''] prp']:= Grg q' d' d'aq' (subs d' fad').
have [d'' [d''aq'' gd'd'']]:= prp' q'' Gq'q''.
exists q''; split => [ | p' Fqp']; first by exists q'.
have [e' [e'ap' fae']]:= prp p' Fqp'.
have [[z' Gpz']]:= Grg p' e' e'ap' (subs e' fae').
by exists z'.
Qed.

Lemma rlzr_tight F f (g: A ->> A'): F \realizes f -> f \tightens g -> F \realizes g.
Proof.
move => Frf tight q a arq afd.
have afd': a \from dom f by apply /tight_dom/afd.
split => [ | Fq FqFq]; first exact/rlzr_dom/afd'.
have [fa [farFq fafa]]:= rlzr_val Frf arq afd' FqFq.
by exists fa; split => //; apply/tight_val/fafa.
Qed.

Lemma tight_rlzr F G (f: A ->> A'): F \realizes f -> G \tightens F -> G \realizes f.
Proof.
move => Frf tight q a qna afd.
have [qfd prp]:= Frf q a qna afd.
split => [ | q' Gqq']; first by apply /tight_dom/qfd.
by have:= prp q' ((tight_val tight) qfd q' Gqq').
Qed.

Lemma icf_rlzr F (f: A ->> A'):
	F \realizes f -> forall g, g \is_choice_for F -> (F2MF g) \realizes f.
Proof. by move => Frf g /icf_spec tight; apply/tight_rlzr/tight. Qed.

Lemma F2MF_rlzr F (f: A ->> A'):
	(F2MF F) \realizes f <->
	(forall q a, a \is_response_to q -> a \from dom f ->
		exists a', a' \is_response_to (F q) /\ f a a').
Proof.
split => rlzr q a aaq afd; first by apply/rlzr_val; first apply rlzr; first apply aaq.
by split => [ | Fq <-]; [rewrite F2MF_dom | apply/rlzr].
Qed.

Lemma rlzr_F2MF F (f: A -> A'):
	F \realizes (F2MF f)
	<->
	forall q a, a \is_response_to q -> q \from dom F
		/\
	forall q', F q q' -> (f a) \is_response_to q'.
Proof.
split => [ | rlzr q a aaq _].
	split; first by apply/ rlzr_dom; [apply H | apply H0 | apply F2MF_tot ].
	by intros; apply/ rlzr_val_sing; [apply F2MF_sing | apply H | apply H0 | | ].
split => [ | q' Fqq']; first by have []:= rlzr q a aaq.
by exists (f a); split => //; apply (rlzr q a aaq).2.
Qed.

Lemma F2MF_rlzr_F2MF F (f: A -> A') :
	(F2MF F) \realizes (F2MF f) <-> forall q a, a \is_response_to q -> (f a) \is_response_to (F q).
Proof.
rewrite F2MF_rlzr.
split => ass phi x phinx; last by exists (f x); split => //; apply ass.
by have [ | fx [cd ->]]:= ass phi x phinx; first by apply F2MF_tot.
Qed.

Lemma sing_rlzr (f: A ->> A') F: F \is_singlevalued -> f \is_singlevalued ->
	F \realizes f
	<->
	(forall q a, a \is_response_to q -> a \from dom f -> q \from dom F)
		/\
	(forall q a q' a', a \is_response_to q -> f a a' -> F q q' -> a' \is_response_to q').
Proof.
move => Fsing fsing.
split; first by move => Frf; split => [q a arq afd |]; [exact/rlzr_dom/afd | exact/rlzr_val_sing].
move => [prp cnd] q a aaq afd.
split => [ | q' Fqq']; first by apply /prp/afd/aaq.
move: afd => [a' faa'].
by exists a'; split => //; apply /cnd/Fqq'/faa'.
Qed.
End realizers.
Notation "f '\is_realized_by' F" := (rlzr F f) (at level 2).
Notation "F '\realizes' f" := (rlzr F f) (at level 2).

Section morphisms.
Context Q Q' (A: interview Q) (A': interview Q').

Definition mf_morphism (f: A ->> A') := exists F, F \realizes f.

Definition mf_morphisms := {f: A ->> A' | mf_morphism f}.

Definition mf_mrph_conv:= make_mf (fun F (f: mf_morphisms) => F \realizes (projT1 f)).

Lemma mf_mrph_conv_sur : mf_mrph_conv \is_cototal.
Proof. by move => [f [F rlzr]]; exists F. Qed.

Definition morphisms_interview_mixin: interview_mixin.type (Q ->> Q') mf_morphisms.
Proof. exists mf_mrph_conv; exact/mf_mrph_conv_sur. Defined.

Canonical morphisms_interview:= interview.Pack morphisms_interview_mixin.

Definition morphism f := mf_morphism (F2MF f).

Definition morphisms := {f | morphism f}.

Definition mrph_conv:= make_mf (fun F (f: morphisms) => F \realizes (F2MF (projT1 f))).

Lemma mrph_conv_sur: mrph_conv \is_cototal.
Proof. by move => [f [F rlzr]]; exists F. Qed.

Definition mrph_interview_mixin: interview_mixin.type (Q ->> Q') morphisms.
Proof. exists mrph_conv; exact mrph_conv_sur. Defined.
End morphisms.

Section realizer_functions.
Context Q (A: interview Q).

Lemma id_rlzr: (@mf_id Q) \realizes (@mf_id A).
Proof. by move => q a qna [d /= eq]; split => [ | _ <-]; [exists q | exists a]. Qed.

Context Q' (A': interview Q').

Lemma cmbn_smbly_rlzr (A'': interview A) (A''': interview A') F G f:
	F \realizes G -> G \realizes f -> F \realizes (f: cmbn_ntrvw A'' ->> cmbn_ntrvw A''').
Proof.
move => FrG Grf q a [d [qnd dna]] afd.
have [dfd prp]:= Grf d a dna afd.
have [qfd prp']:= FrG q d qnd dfd.
split => // q' Fqq'.
have [d' [q'nd' Gdd']]:= prp' q' Fqq'.
have [d''' [d'nd''' fd'd''']]:= prp d' Gdd'.
by exists d'''; split => //; exists d'.
Qed.

Lemma fprd_rlzr Q'' (A'': interview Q'') Q''' (A''': interview Q''')
	F (f: A ->> A') G (g: A'' ->> A'''):
	F \realizes f -> G \realizes g -> (F ** G) \realizes (f ** g).
Proof.
move => Frf Grg [q q''] [a a''] [/=aaq a''aq''] [[a' a''']] [/=faa' ga''a'''].
have afd: a \from dom f by exists a'.
have afd': a'' \from dom g by exists a'''.
have [ex prp]:= Frf q a aaq afd.
have [ex' prp']:= Grg q'' a'' a''aq'' afd'.
split => [ | [q' q'''] /= [Fqq' Gq''q''']]; last first.
	 have [d' [d'aq' fad']]:= prp q' Fqq'.
	 have [d''' [d'''aq''' ga''d''']]:= prp' q''' Gq''q'''.
	 by exists (d', d''').
have [q' Fqq']:= ex; have [q''' Gq''q''']:= ex'.
by exists (q', q''').
Qed.

Lemma fst_rlzr:
	(@mf_fst Q Q') \realizes (@mf_fst A A': (prod_interview A A') ->> A).
Proof.
move => [q1 q2] a [/=aaq1 aaq2] ex; split; first by exists q1.
by move => q' <-; exists a.1.
Qed.

Lemma snd_rlzr:
	(@mf_snd Q Q') \realizes (@mf_snd A A': (prod_interview A A') ->> A').
Proof.
move => [q1 q2] a [/=aaq1 aaq2] ex; split; first by exists q2.
by move => q' <-; exists a.2.
Qed.

Lemma fsum_rlzr Q'' (A'': interview Q'') Q''' (A''': interview Q''')
	F (f: A ->> A') G (g: A'' ->> A'''):
	F \realizes f -> G \realizes g -> (F +s+ G) \realizes (f +s+ g).
Proof.
move => rlzr rlzr'.
case => q.
- case => a qra [[a' faa' | ]//].
  have [ | [q' Fqq'] prp]:= rlzr q a qra; first by exists a'.
  split => [ | []// Fq' val]; first by exists (inl q').
  by have [fa []]:= prp Fq' val; exists (inl fa).
case => a qra [[ | a' faa']//].
have [ | [q' Fqq'] prp]:= rlzr' q a qra; first by exists a'.
split => [ | []// Fq' val]; first by exists (inr q').
by have [fa []]:= prp Fq' val; exists (inr fa).
Qed.

Definition mf_inl S T:= F2MF (@ inl S T).

Lemma inl_rlzr:
  (@mf_inl Q Q') \realizes (@mf_inl A A': A ->> (sum_interview A A')).
Proof.
by move => q a; split => [ | []// _ [<-]]; [exact/F2MF_dom |exists (inl a)].
Qed.

Definition mf_inr S T:= F2MF (@inr S T).

Lemma inr_rlzr:
  (@mf_inr Q Q') \realizes (@mf_inr A A': A' ->> (sum_interview A A')).
Proof.
by move => q a; split => [ | []// _ [<-]]; [exact/F2MF_dom |exists (inr a)].
Qed.

Definition mf_cons Q := F2MF (fun aL => @cons Q aL.1 aL.2).

Lemma cons_rlzr:
	(@mf_cons Q) \realizes (@mf_cons A: (prod_interview A (list_interview A) ->> list_interview A)).
Proof.
move => [q K] [a L] [arq LrK] _ ; split; first exact/F2MF_tot.
by move => _ /= <-; exists (cons a L).
Qed.

Lemma diag_rlzr: (@mf_diag Q) \realizes (@mf_diag A: A ->> (prod_interview A A)).
Proof. by move => q a aaq _; split => [ | [_ _] [<- <-]]; [exists (q, q) | exists (a, a)]. Qed.

Lemma cnst_rlzr (q': Q') (a': A'):
	a' \is_response_to q' -> (@mf_cnst Q Q' q') \realizes (@mf_cnst A A' a').
Proof. by move => a'aq' q a aaq _; split => [ | _ <-]; [exists q' | exists a']. Qed.

(*
Lemma rlzr_comp_codom Q'' (D'': assembly Q'') G F (f: A ->> A') (g:  A'->> answers D''):
	G \realizes (g|_(codom f)) -> F \realizes f -> (G o F) \realizes (g o f).
Proof.
move => rlzr rlzr' q a aaq [a'' [[a' [faa' ga'a'']] subs]] q'' [[q' [Fqq' Gq'q'']] subs'].
have afd: a \from_dom f by exists a'.
have [d' [d'aq' fad']]:= rlzr' q a aaq afd q' Fqq'.
have afd': d' \from_dom (g|_(codom f)).
	have [b gbd']:= subs d' fad'.
	by exists b; split; first by exists a.
have [d'' [d''aq'' [d'fd gd'd'']]]:= rlzr q' d' d'aq' afd' q'' Gq'q''.
exists d''; split => //.
by split; first by exists d'.
Qed.
*)
End realizer_functions.
Arguments fst_rlzr {Q} A {Q'} A'.
Arguments snd_rlzr {Q} A {Q'} A'.