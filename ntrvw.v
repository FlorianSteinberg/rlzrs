(******************************************************************************)
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
From mf Require Import all_mf.
Import Morphisms.
Local Open Scope mf_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope rlzr_scope with rlzr.
Local Open Scope rlzr_scope.
Section interviews.
  Class Interview Q A :=
    {
      conversation: Q ->> A;
      only_respond : conversation \is_cototal;
    }.

  Local Notation conversation_from I:= (@conversation _ _ I).
  Context `{I: Interview}.

  Lemma conv_sur: conversation \is_cototal.
  Proof. exact/only_respond. Qed.

  Local Notation "a '\is_response_to' q 'in' I" := (conversation_from I q a) (at level 2).

  Lemma id_sur S: (@mf_id S) \is_cototal.
  Proof. by move => c; exists c. Qed.

  Definition id_interview S:= Build_Interview (@id_sur S).

  Lemma fun_conv_sur (f: A -> Q): (F2MF f\^-1) \is_cototal.
  Proof. exact/cotot_tot_inv/F2MF_tot. Qed.

  Definition  sub_interview (P: subset A): Interview Q {x | x \from P}.
    exists (make_mf (fun q a => conversation q (sval a))).
    by move => [a /=_]; apply/conv_sur.
  Defined.

  Definition cmbn_ntrvw `{I': Interview A}: Interview Q A0.
    exists ((conversation_from I') \o_R (conversation_from I)).
    exact/rcmp_cotot/conv_sur/only_respond.
  Defined.

  Context `{I0: Interview}.
  Definition prod_conv := (conversation_from I) ** (conversation_from I0).

  Lemma prod_conv_sur: prod_conv \is_cototal.
  Proof. by apply/fprd_cotot/only_respond/only_respond. Qed.

  Global Instance prod_interview: Interview (Q * Q0) (A * A0) := Build_Interview prod_conv_sur.
  
  Definition sum_conv:= (conversation_from I) +s+ (conversation_from I0).
  
  Lemma sum_conv_sur: sum_conv \is_cototal.
  Proof.
    move => [a | b] /=.
      by have [c cna]:= conv_sur a; exists (inl c).
    by have [c cnab]:= only_respond b; exists (inr c).
  Qed.

  Global Instance sum_interview: Interview (Q + Q0) (A + A0) := Build_Interview sum_conv_sur.

  Definition list_conv := mf_map (conversation_from I).

  Lemma list_conv_sur: list_conv \is_cototal.
  Proof. exact/map_sur/conv_sur. Qed.

  Global Instance list_interview: Interview (seq Q) (seq A) := Build_Interview list_conv_sur.
End interviews.
Notation conversation_from I := (@conversation _ _ I).
Notation "a '\is_response_to' q '\wrt' I" := (conversation_from I q a) (at level 2).
Arguments cmbn_ntrvw: clear implicits.
Arguments cmbn_ntrvw {Q} {A} (I) {A0} (I').
Notation "I \o_R I'" := (cmbn_ntrvw I I').
Arguments prod_interview: clear implicits.
Arguments prod_interview {Q} {A} (I) {Q0} {A0} (I0).
Notation "I * I0" := (prod_interview I I0): rlzr_scope.
Arguments sum_interview: clear implicits.
Arguments sum_interview {Q} {A} (I) {Q0} {A0} (I0).
Notation "I + I0" := (sum_interview I I0): rlzr_scope.
Arguments list_interview: clear implicits.
Arguments list_interview {Q} {A} (I).
Notation seq I := (list_interview I).

Section realizer.
  Context `{I: Interview} `{I0: Interview}.

  Definition realizer (F: Q ->> Q0) (f: A ->> A0) :=
    (forall q a, a \is_response_to q \wrt I -> a \from dom f ->
                 q \from dom F
                 /\
		 forall Fq, F q Fq -> exists fa, fa \is_response_to Fq \wrt I0 /\ f a fa).

  Local Notation "F '\realizes' f" := (realizer F f) (at level 2).
  
  Global Instance rlzr_prpr:
    Proper (@equiv Q Q0 ==> @equiv A A0 ==> iff) (@realizer).
  Proof.
    move => F G FeG f g feg.
    split => rlzr q a aaq afd.
    have afd': a \from dom f by rewrite feg.
    split => [ | q' Gqq'].
    - by have [[q' Fqq'] _]:= rlzr q a aaq afd'; exists q'; rewrite -FeG.
    have [_ prp]:= rlzr q a aaq afd'.
    have [ | a' [a'aq' faa']]:= prp q' _; first by rewrite FeG.
      by exists a'; rewrite -feg.
    have afd': a \from dom g by rewrite -feg.
    split => [ | q' Gqq'].
    - by have [[q' Fqq'] _]:= rlzr q a aaq afd'; exists q'; rewrite FeG.
    have [_ prp]:= rlzr q a aaq afd'.
    have [ | a' [a'aq' faa']]:= prp q' _; first by rewrite -FeG.
    by exists a'; rewrite feg.
  Qed.
  
  Lemma split_rlzr (F: Q ->> Q0) (f: A ->> A0):
		(forall q a, a \is_response_to q \wrt I -> a \from dom f -> q \from dom F) ->
		(forall q a, a \is_response_to q \wrt I -> a \from dom f -> forall Fq, F q Fq -> exists fa, fa \is_response_to Fq \wrt I0 /\ f a fa) ->
                F \realizes f.
  Proof.
    by move => dm val q a arq afd; split => [ | Fq FqFq]; [apply/dm/afd | apply/val/FqFq].
  Qed.

  Lemma rlzr_dom (F: Q ->> Q0) (f: A ->> A0) q a: F \realizes f ->
	a \is_response_to q \wrt I -> a \from dom f -> q \from dom F.
  Proof. by move => Frf arq qfd; have []:= Frf q a arq qfd. Qed.

  Lemma rlzr_val (F: Q ->> Q0) (f: A ->> A0) q a Fq: F \realizes f ->
	            a \is_response_to q \wrt I -> a \from dom f -> F q Fq ->
                    exists fa, fa \is_response_to Fq \wrt I0 /\ f a fa.
  Proof. by move => Frf arq qfd FqFq; have [_ prp]:= Frf q a arq qfd; apply prp. Qed.
End realizer.
Notation "f '\is_realized_by' F" := (realizer F f) (at level 2).
Arguments realizer: clear implicits.
Arguments realizer {Q} {A} (I) {Q0} {A0} (I0).
Notation "F '\realizes' f \wrt I \and I0" := (realizer I  I0 F f) (at level 2).

Section realizers.
  Lemma id_rlzr_tight Q Q' F G:
    F \realizes G \wrt (id_interview Q) \and (id_interview Q') <-> F \tightens G.
  Proof.
    split =>[rlzr s sfd | tight q a <- afd].
    - split => [ | t Fst]; first exact /(rlzr_dom rlzr)/sfd.
      by have [ | Fs [<-]]// :=rlzr_val rlzr _ sfd Fst.
    split => [ | Fq FqFq]; first exact/tight_dom/afd.
    by exists Fq; split => //; apply/tight_val/FqFq.
  Qed.

  Context `{I: Interview} `{I0: Interview}.

  Lemma rlzr_val_sing (f: A ->> A0) F: f \is_singlevalued -> F \realizes f \wrt I \and I0 ->
      forall q a q' a', a \is_response_to q \wrt I -> f a a' -> F q q' -> a' \is_response_to q' \wrt I0.
  Proof.
    move => sing rlzr q a q' a' aaq faa' Fqq'.
    have [ | _ prp]:= rlzr q a aaq; first by exists a'.
    have [d' [d'aq' fad']]:= prp q' Fqq'.
    by rewrite (sing a a' d').
  Qed.

  Lemma rlzr_comp `{I1: Interview} G F f g:
    G \realizes g \wrt I0 \and I1 ->
    F \realizes f \wrt I \and I0 ->
    (G \o F) \realizes (g \o f) \wrt I \and I1.
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

  Lemma rlzr_tight F f g: F \realizes f \wrt I \and I0 ->
                          f \tightens g -> F \realizes g \wrt I \and I0.
  Proof.
    move => Frf tight q a arq afd.
    have afd': a \from dom f by apply /tight_dom/afd.
    split => [ | Fq FqFq]; first exact/rlzr_dom/afd'.
    have [fa [farFq fafa]]:= rlzr_val Frf arq afd' FqFq.
    by exists fa; split => //; apply/tight_val/fafa.
  Qed.

  Lemma tight_rlzr F G f: F \realizes f \wrt I \and I0 -> G \tightens F ->
                          G \realizes f \wrt I \and I0.
  Proof.
    move => Frf tight q a qna afd.
    have [qfd prp]:= Frf q a qna afd.
    split => [ | q' Gqq']; first by apply /tight_dom/qfd.
    by have:= prp q' ((tight_val tight) qfd q' Gqq').
  Qed.

  Lemma icf_rlzr F f g: F \realizes f \wrt I \and I0 ->
                        g \is_choice_for F -> (F2MF g) \realizes f \wrt I \and I0.
  Proof. by move => Frf /icf_spec tight; apply/tight_rlzr/tight. Qed.

  Lemma F2MF_rlzr F f:
	(F2MF F) \realizes f \wrt I \and I0 <->
	(forall q a, a \is_response_to q \wrt I -> a \from dom f ->
		exists a', a' \is_response_to (F q) \wrt I0 /\ f a a').
  Proof.
    split => rlzr q a aaq afd; first by apply/rlzr_val; first apply rlzr; first apply aaq.
    by split => [ | Fq <-]; [rewrite F2MF_dom | apply/rlzr].
  Qed.

  Lemma rlzr_F2MF F f: F \realizes (F2MF f) \wrt I \and I0 <->
    forall q a, a \is_response_to q \wrt I -> q \from dom F
                   /\
	           forall q', F q q' -> (f a) \is_response_to q' \wrt I0.
  Proof.
    split => [ | rlzr q a aaq _].
    split; first by apply/ rlzr_dom; [apply H | apply H0 | apply F2MF_tot ].
    - by intros; apply/ rlzr_val_sing; [apply F2MF_sing | apply H | apply H0 | | ].
    split => [ | q' Fqq']; first by have []:= rlzr q a aaq.
    by exists (f a); split => //; apply (rlzr q a aaq).2.
  Qed.

  Lemma F2MF_rlzr_F2MF F f: (F2MF F) \realizes (F2MF f) \wrt I \and I0 <->
        forall q a, a \is_response_to q \wrt I -> (f a) \is_response_to (F q) \wrt I0.
  Proof.
    rewrite F2MF_rlzr.
    split => ass phi x phinx; last by exists (f x); split => //; apply ass.
    by have [ | fx [cd ->]]:= ass phi x phinx; first by apply F2MF_tot.
  Qed.

  Lemma sing_rlzr_sing F f: F \is_singlevalued -> f \is_singlevalued ->
	F \realizes f \wrt I \and I0
	<->
	(forall q a, a \is_response_to q \wrt I -> a \from dom f -> q \from dom F)
		/\
	        (forall q a q' a', a \is_response_to q \wrt I -> f a a' -> F q q' ->
                                   a' \is_response_to q' \wrt I0).
  Proof.
    move => Fsing fsing; split => [Frf | [prp cnd] q a aaq afd].
    - by split => [q a arq afd |]; [exact/rlzr_dom/afd | exact/rlzr_val_sing].
    split => [ | q' Fqq']; first by apply /prp/afd/aaq.
    by move: afd => [a' faa'];exists a'; split => //; apply /cnd/Fqq'/faa'.
  Qed.

  Lemma sing_rlzr_F2MF F f: F \is_singlevalued -> F \realizes (F2MF f) \wrt I \and I0
	<->
	(dom (conversation_from I) \is_subset_of dom F)
		/\
	(forall q a q', a \is_response_to q \wrt I -> F q q' -> (f a) \is_response_to q' \wrt I0).
  Proof.
    move => sing; split => [Frf | [prp cnd]].
    - split => [q [a aaq] | q a q' arq]; first by apply/(rlzr_dom Frf)/F2MF_dom; first exact/aaq.
      by apply/(rlzr_val_sing _ Frf)/eq_refl=>//; apply/F2MF_sing.
    apply/sing_rlzr_sing => //; try by apply/F2MF_sing.
    by split => [q a arq _ | q a q' _ arq' <-]; [apply/prp; exists a | apply/cnd].
  Qed.
End realizers.

Section morphisms.
  Context `{I: Interview} `{I0: Interview}.

  Definition mf_morphism f := exists F, F \realizes f \wrt I \and I0.

  Definition mf_morphisms := {f | mf_morphism f}.
  
  Definition mf_mrph_conv:= make_mf (fun F (f: mf_morphisms) => F \realizes (projT1 f) \wrt I \and I0).
  
  Lemma mf_mrph_conv_sur : mf_mrph_conv \is_cototal.
  Proof. by move => [f [F rlzr]]; exists F. Qed.

  Definition mf_morphisms_interview: Interview (Q ->> Q0) mf_morphisms :=
    Build_Interview mf_mrph_conv_sur.
  
  Definition morphism f := mf_morphism (F2MF f).
  
  Definition morphisms := {f | morphism f}.

  Definition mrph_conv:= make_mf (fun F (f: morphisms) => F \realizes (F2MF (projT1 f)) \wrt I \and I0).

  Lemma mrph_conv_sur: mrph_conv \is_cototal.
  Proof. by move => [f [F rlzr]]; exists F. Qed.
End morphisms.

Section realizer_functions.
  Context `{I : Interview}.
  
  Lemma id_rlzr: mf_id \realizes (@mf_id A) \wrt I \and I.
  Proof. by move => q a qna [d /= eq]; split => [ | _ <-]; [exists q | exists a]. Qed.

  Context `{I0: Interview}.
  
  Lemma cmbn_rlzr `{I1: Interview A} `{I2: Interview A0} F G f:
    F \realizes G \wrt I \and I0 -> G \realizes f \wrt I1 \and I2 ->
    F \realizes f \wrt (I \o_R I1) \and (I0 \o_R I2).
  Proof.
    move => FrG Grf q a [d [qnd dna]] afd.
    have [dfd prp]:= Grf d a dna afd.
    have [qfd prp']:= FrG q d qnd dfd.
    split => // q' Fqq'.
    have [d' [q'nd' Gdd']]:= prp' q' Fqq'.
    have [d''' [d'nd''' fd'd''']]:= prp d' Gdd'.
    by exists d'''; split => //; exists d'.
  Qed.

  Lemma fprd_rlzr `{I1: Interview} `{I2: Interview} F f G g:
    F \realizes f \wrt I \and I1 -> G \realizes g \wrt I0 \and I2 -> (F ** G) \realizes (f ** g) \wrt (I * I0) \and (I1 * I2).
  Proof.
    move => Frf Grg [q q''] [a a''] [/=aaq a''aq''] [[a' a''']] [/=faa' ga''a'''].
    have afd: a \from dom f by exists a'.
    have afd': a'' \from dom g by exists a'''.
    have [ex prp]:= Frf q a aaq afd.
    have [ex' prp']:= Grg q'' a'' a''aq'' afd'.
    split => [ | [q' q'''] /= [Fqq' Gq''q''']]; last first.
    - have [d' [d'aq' fad']]:= prp q' Fqq'.
      have [d''' [d'''aq''' ga''d''']]:= prp' q''' Gq''q'''.
      by exists (d', d''').
    have [q' Fqq']:= ex; have [q''' Gq''q''']:= ex'.
    by exists (q', q''').
  Qed.

  Lemma fst_rlzr: mf_fst \realizes mf_fst \wrt I * I0 \and I.
  Proof.
    move => [q1 q2] a [/=aaq1 aaq2] ex; split; first by exists q1.
    by move => q' <-; exists a.1.
  Qed.

  Lemma snd_rlzr: mf_snd \realizes mf_snd \wrt I * I0 \and I0.
  Proof.
    move => [q1 q2] a [/=aaq1 aaq2] ex; split; first by exists q2.
    by move => q' <-; exists a.2.
  Qed.

  Lemma fsum_rlzr `{I1: Interview} `{I2: Interview} F f G g:
    F \realizes f \wrt I \and I1 -> G \realizes g \wrt I0 \and I2 ->
    (F +s+ G) \realizes (f +s+ g) \wrt I + I0 \and (I1 + I2).
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
  Arguments mf_inl {S} {T}.

  Lemma inl_rlzr: mf_inl \realizes mf_inl \wrt I \and (I + I0).
  Proof. by move => q a; split => [ | []// _ [<-]]; [exact/F2MF_dom |exists (inl a)]. Qed.
  
  Definition mf_inr S T:= F2MF (@inr S T).
  Arguments mf_inr {S} {T}.

  Lemma inr_rlzr: mf_inr \realizes mf_inr \wrt I0 \and (I + I0).
  Proof. by move => q a; split => [ | []// _ [<-]]; [exact/F2MF_dom |exists (inr a)]. Qed.

  Definition mf_cons Q := F2MF (fun aL => @cons Q aL.1 aL.2).
  Arguments mf_cons {Q}.

  Lemma cons_rlzr: mf_cons \realizes mf_cons \wrt I * seq I \and (seq I).
  Proof.
    move => [q K] [a L] [arq LrK] _ ; split; first exact/F2MF_tot.
    by move => _ /= <-; exists (cons a L).
  Qed.

  Lemma diag_rlzr: mf_diag \realizes mf_diag \wrt I \and (I * I).
  Proof. by move => q a aaq _; split => [ | [_ _] [<- <-]]; [exists (q, q) | exists (a, a)]. Qed.

  Lemma cnst_rlzr q' a':
	a' \is_response_to q' \wrt I0 -> (mf_cnst q') \realizes mf_cnst a' \wrt I \and I0.
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