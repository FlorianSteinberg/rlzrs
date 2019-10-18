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
      conversation:> Q ->> A;
      only_respond : conversation \is_cototal
    }.

  Context Q A (I: Interview Q A).

  Lemma conv_sur: conversation \is_cototal.
  Proof. exact only_respond. Qed.

  Local Notation "a '\is_response_to' q" := (conversation q a) (at level 2).

  Lemma id_sur S: (@mf_id S) \is_cototal.
  Proof. by move => c; exists c. Qed.

  Definition id_interview S:= Build_Interview (@id_sur S).

  Lemma fun_conv_sur (f: A -> Q): (F2MF f\^-1) \is_cototal.
  Proof. exact/cotot_tot_inv/F2MF_tot. Qed.

  Ltac surjectivity := repeat mf.surjectivity || apply/conv_sur.

  Definition sub_conversation (P: subset A) :=
    make_mf (fun q (a: {x | x \from P})=> conversation q (sval a)).

  Lemma sub_conv_sur P: (sub_conversation P) \is_cototal.
  Proof. by move => [a Pa]; have [q]:= conv_sur a; exists q. Qed.
  
  Canonical sub_interview (P: subset A): Interview Q P.
    by exists (sub_conversation P); apply/sub_conv_sur.
  Defined.

  Definition combine_interviews A' (I': Interview A A'): Interview Q A'.
    by exists (conversation \o_R conversation); apply/rcmp_cotot; apply/only_respond.
  Defined.

  Global Instance list_interview: Interview (seq Q) (seq A).
    by exists (mf_map conversation); apply/map_sur/only_respond.
  Defined.
  Context Q' A' (I': Interview Q' A').

  Global Instance prod_interview: Interview (Q * Q') (A * A').
    by exists (conversation ** conversation); surjectivity; apply/only_respond.
  Defined.
    
  Global Instance sum_interview: Interview (Q + Q') (A + A').
    by exists (conversation +s+ conversation); surjectivity; apply/only_respond.
  Defined.
End interviews.
Coercion conversation: Interview >-> multifunction.

Ltac surjectivity := repeat mf.surjectivity || apply/conv_sur.


Section realizer.
  Local Notation "a \is_response_to q \wrt conversation" :=
    (a \from (conversation: _ ->> _) q) (at level 30).
  Context Q A (conv: Q ->> A) Q' A' (conv': Q' ->> A').
  
  Definition realizer (F: Q ->> Q') (f: A ->> A') :=
    (forall q a, a \is_response_to q \wrt conv -> a \from dom f ->
                 q \from dom F
                 /\
		 forall Fq, Fq \from F q -> exists fa, fa \from f a /\ fa \is_response_to Fq \wrt conv').

  Local Notation "F '\realizes' f" := (realizer F f) (at level 30).

  Lemma rlzr_spec_dep F f:
    F \realizes f <->
    forall (a: dom f) (q: conv\^-1 (sval a)), (sval q) \from dom F
                                         /\
                                         forall (Fq: F (sval q)), exists (fa: f (sval a)),
                                             (sval fa) \is_response_to (sval Fq) \wrt conv'.
  Proof.
    split => [rlzr [a afd] [q/= aaq] | rlzr q a aaq afd].
    - have [qfd prp]//:= rlzr q a aaq afd.
      split => //; case => Fq val.
      by have [fa [val' faaFq]]:= prp Fq val; exists (exist _ _ val').
    have aaq': q \from conv\^-1 a by trivial.  
    have [qfd prp]:= rlzr (exist _ _ afd) (exist _ _ aaq').
    by split => // Fq val; have [/=[fa]]:= prp (exist _ _ val); exists fa.
  Qed.

  Global Instance rlzr_prpr:
    Proper (@equiv Q Q' ==> @equiv A A' ==> iff) (@realizer).
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
  
  Lemma split_rlzr (F: Q ->> Q') (f: A ->> A'):
		(forall q a, a \is_response_to q \wrt conv -> a \from dom f -> q \from dom F) ->
		(forall q a, a \is_response_to q \wrt conv -> a \from dom f -> forall Fq, Fq \from F q -> exists fa, fa \from f a /\ fa \is_response_to Fq \wrt conv') ->
                F \realizes f.
  Proof. by move => dm val q a ? afd; split => [ | Fq FqFq]; [apply/dm/afd | apply/val/FqFq]. Qed.

  Lemma rlzr_dom (F: Q ->> Q') (f: A ->> A') q a:
    F \realizes f -> a \is_response_to q \wrt conv -> a \from dom f -> q \from dom F.
  Proof. by move => Frf arq qfd; have []:= Frf q a arq qfd. Qed.

  Lemma rlzr_val (F: Q ->> Q') (f: A ->> A') q a Fq: F \realizes f ->
	            a \is_response_to q \wrt conv -> a \from dom f -> Fq \from F q ->
                    exists fa, fa \from f a /\ fa \is_response_to Fq \wrt conv'.
  Proof. by move => Frf arq qfd FqFq; have [_ prp]:= Frf q a arq qfd; apply prp. Qed.
End realizer.
Notation "f '\realized_by' F \wrt conv \and conv'" := (realizer conv conv' F f) (at level 2).

Section realizers.
  Lemma id_rlzr_tight Q Q' (F G: Q ->> Q'):
    G \realized_by F \wrt mf_id \and mf_id <-> F \tightens G.
  Proof.
    split =>[rlzr s sfd | tight q a <- afd].
    - split => [ | t Fst]; first exact /(rlzr_dom rlzr)/sfd.
      by have [ | Fs [vl ->]] //:= rlzr_val rlzr _ sfd Fst.
    split => [ | Fq FqFq]; first exact/tight_dom/afd.
    by exists Fq; split => //; apply/tight_val/FqFq.
  Qed.

  Context Q A Q0 A0 (conv: Q ->> A) (conv0: Q0 ->> A0).
  
  Lemma rlzr_val_sing (f: A ->> A0) F: f \is_singlevalued -> f \realized_by F \wrt conv \and conv0 ->
      forall q a q' a', conv q a -> f a a' -> F q q' -> conv0 q' a'.
  Proof.
    move => sing rlzr q a q' a' aaq faa' Fqq'.
    have [ | _ prp]:= rlzr q a aaq; first by exists a'.
    have [d' [d'aq' fad']]:= prp q' Fqq'.
    by rewrite (sing a a' d').
  Qed.

  Lemma rlzr_comp Q1 A1 (conv1: Q1 ->> A1) G F f g:
    g \realized_by G \wrt conv0 \and conv1 ->
    f \realized_by F \wrt conv \and conv0 ->
    (g \o f) \realized_by (G \o F) \wrt conv \and conv1.
  Proof.
    move => Grg Frf q a arq [gfa [[fa [fafa gfagfa]]] subs].
    have afd: a \from dom f by exists fa.
    split; last first.
      move => GFq [[Fq [FqFq GFqGFq]] subs'].
      have [d' [d'aq' fad']]:= rlzr_val Frf arq afd FqFq.
      have [d'' [d''aq'' gd'd'']]:= rlzr_val Grg fad' (subs d' d'aq') GFqGFq.
      by exists d''; split => //; split; first by exists d'.
    have [[q' Fqq'] prp]:= Frf q a arq afd.
    have [d' [d'aq' fad']]:= prp q' Fqq'.
    have [[q'' Gq'q''] prp']:= Grg q' d' fad' (subs d' d'aq').
    have [d'' [d''aq'' gd'd'']]:= prp' q'' Gq'q''.
    exists q''; split => [ | p' Fqp']; first by exists q'.
    have [e' [e'ap' fae']]:= prp p' Fqp'.
    have [[z' Gpz']]:= Grg p' e' fae' (subs e' e'ap').
    by exists z'.
  Qed.

  Lemma rlzr_tight F f g: f \realized_by F \wrt conv \and conv0 ->
                          f \tightens g -> g \realized_by F \wrt conv \and conv0.
  Proof.
    move => Frf tight q a arq afd.
    have afd': a \from dom f by apply /tight_dom/afd.
    split => [ | Fq FqFq]; first exact/rlzr_dom/afd'/arq/Frf.
    have [fa [fafa farFq]]:= rlzr_val Frf arq afd' FqFq.
    by exists fa; split => //; apply/tight_val/fafa.
  Qed.

  Lemma tight_rlzr F G f: f \realized_by F \wrt conv \and conv0 -> G \tightens F ->
                          f \realized_by G \wrt conv \and conv0.
  Proof.
    move => Frf tight q a qna afd.
    have [qfd prp]:= Frf q a qna afd.
    split => [ | q' Gqq']; first by apply /tight_dom/qfd.
    by have:= prp q' ((tight_val tight) qfd q' Gqq').
  Qed.

  Lemma icf_rlzr F f g: f \realized_by F \wrt conv \and conv0 ->
                        g \is_choice_for F -> f \realized_by (F2MF g) \wrt conv \and conv0.
  Proof. by move => Frf /icf_spec tight; apply/tight_rlzr/tight. Qed.

  Lemma F2MF_rlzr F f:
	f \realized_by (F2MF F) \wrt conv \and conv0 <->
	(forall q a, a \from conv q -> a \from dom f ->
		exists fa, fa \from (f a) \n (conv0 (F q))).
  Proof.
    split => rlzr q a aaq afd; first by apply/rlzr_val; first apply/rlzr; first apply/aaq.
    by split => [ | Fq <-]; [rewrite F2MF_dom | apply/rlzr].
  Qed.
  
  Lemma rlzr_F2MF F f: (F2MF f) \realized_by F \wrt conv \and conv0 <->
    forall q a, a \from conv q -> q \from dom F
                   /\
	           forall q', q' \from F q -> (f a) \from conv0 q'.
  Proof.
    split => [ | rlzr q a aaq _].
    split; first by apply/ rlzr_dom; [apply H | apply H0 | apply F2MF_tot ].
    - by intros; apply/ rlzr_val_sing; [apply F2MF_sing | apply H | apply H0 | | ].
    split => [ | q' Fqq']; first by have []:= rlzr q a aaq.
    by exists (f a); split => //; apply (rlzr q a aaq).2.
  Qed.

  Lemma F2MF_rlzr_F2MF F f: (F2MF f) \realized_by (F2MF F) \wrt conv \and conv0 <->
        forall q a, a \from conv q -> (f a) \from conv0 (F q).
  Proof.
    rewrite F2MF_rlzr.
    split => ass phi x phinx; last by exists (f x); split => //; apply ass.
    by have [ | fx [->]]:= ass phi x phinx; first by apply F2MF_tot.
  Qed.

  Lemma sing_rlzr_sing F f: F \is_singlevalued -> f \is_singlevalued ->
	f \realized_by F \wrt conv \and conv0
	<->
	(forall q a, a \from conv q -> a \from dom f -> q \from dom F)
		/\
	        (forall q a q' a', a \from conv q -> a' \from f a -> q' \from F q ->
                                   a' \from conv0 q').
  Proof.
    move => Fsing fsing; split => [Frf | [prp cnd] q a aaq afd].
    - by split => [q a arq afd |]; [apply/rlzr_dom/afd/arq/Frf | exact/rlzr_val_sing].
    split => [ | q' Fqq']; first by apply /prp/afd/aaq.
    by move: afd => [a' faa'];exists a'; split => //; apply /cnd/Fqq'/faa'.
  Qed.

  Lemma sing_rlzr_F2MF F f: F \is_singlevalued -> (F2MF f) \realized_by F \wrt conv \and conv0
	<->
	(dom conv \is_subset_of dom F)
		/\
	(forall q a q', a \from conv q -> q' \from F q -> (f a) \from conv0 q').
  Proof.
    move => sing; split => [Frf | [prp cnd]].
    - split => [q [a aaq] | q a q' arq]; first by apply/(rlzr_dom Frf)/F2MF_dom; first exact/aaq.
      by apply/(rlzr_val_sing _ Frf)/eq_refl=>//; apply/F2MF_sing.
    apply/sing_rlzr_sing => //; try by apply/F2MF_sing.
    by split => [q a arq _ | q a q' _ arq' <-]; [apply/prp; exists a | apply/cnd].
  Qed.

  Lemma PF2MF_rlzr_F2MF F f: (F2MF f) \realized_by (PF2MF F) \wrt conv \and conv0
                             <->
                             dom conv \is_subset_of dom F
                             /\
                             (forall q a, a \from conv (sval q) -> (f a) \from conv0 (F q)).
  Proof.
    rewrite rlzr_F2MF.    
    split => [rlzr | [subs val] q a afd].
    - split => [q [a qna] | q a afd]; first by have []:= rlzr q a qna.
      have [[q' [qfd eq]] val]:= rlzr (sval q) a afd; apply/val.
      by case: q qfd eq afd val => q qfd; exists qfd.
    split => [ | Fq [qfd <-]]; first by apply/subs; exists a.
    exact/val.
  Qed.
End realizers.

Section morphisms.
  Context Q A (I: Interview Q A) Q' A' (I': Interview Q' A').
  
  Definition mf_morphism f := exists F, f \realized_by F \wrt I \and I'.

  Definition mf_morphisms:= make_subset mf_morphism.

  Definition mf_mrph_conv:=
    make_mf (fun F (f: mf_morphisms) => (projT1 f) \realized_by F \wrt I \and I').
  
  Global Instance mf_morphisms_Interview : Interview (Q ->> Q') mf_morphisms.
    by exists mf_mrph_conv; surjectivity; case => f [F]; exists F.
  Defined.
  
  Definition morphism f := mf_morphism (F2MF f).
  Definition morphisms := make_subset morphism.
  
  Definition mrph_conv:= make_mf (fun F (f: morphisms) =>
                                    (F2MF (projT1 f)) \realized_by F \wrt I \and I').

  Global Instance morphisms_Interview: Interview (Q ->> Q') morphisms.
  Proof. exists mrph_conv; by case => f [F rlzr]; exists F. Qed.
End morphisms.


Section realizer_functions.
  Context Q A (conv: Q ->> A).
  
  Lemma id_rlzr: mf_id \realized_by (@mf_id Q) \wrt conv \and conv.
  Proof. by move => q a qna [d /= eq]; split => [ | _ <-]; [exists q | exists a]. Qed.

  Definition mf_cons Q := F2MF (fun aL => @cons Q aL.1 aL.2).
  Arguments mf_cons {Q}.

  Lemma cons_rlzr: mf_cons \realized_by mf_cons \wrt conv ** mf_map conv \and (mf_map conv).
  Proof.
    move => [q K] [a L] [arq LrK] _ ; split; first exact/F2MF_tot.
    by move => _ /= <-; exists (cons a L).
  Qed.

  Lemma diag_rlzr: mf_diag \realized_by mf_diag \wrt conv \and (conv ** conv).
  Proof. by move => q a aaq _; split => [ | [_ _] [<- <-]]; [exists (q, q) | exists (a, a)]. Qed.

  Context Q0 A0 (conv0: Q0 ->> A0).

  Lemma cnst_rlzr q' a':
	a' \from conv0 q' -> (mf_cnst a') \realized_by (mf_cnst q') \wrt conv \and conv0.
  Proof. by move => a'aq' q a aaq _; split => [ | _ <-]; [exists q' | exists a']. Qed.

  Lemma fst_rlzr: mf_fst \realized_by mf_fst \wrt conv ** conv0 \and conv.
  Proof.
    move => [q1 q2] a [/=aaq1 aaq2] ex; split; first by exists q1.
    by move => q' <-; exists a.1.
  Qed.

  Lemma snd_rlzr: mf_snd \realized_by mf_snd \wrt conv ** conv0 \and conv0.
  Proof.
    move => [q1 q2] a [/=aaq1 aaq2] ex; split; first by exists q2.
    by move => q' <-; exists a.2.
  Qed.

  Definition mf_inl S T:= F2MF (@ inl S T).
  Arguments mf_inl {S} {T}.

  Lemma inl_rlzr: mf_inl \realized_by mf_inl \wrt conv \and (conv +s+ conv0).
  Proof. by move => q a; split => [ | []// _ [<-]]; [exact/F2MF_dom |exists (inl a)]. Qed.
  
  Definition mf_inr S T:= F2MF (@inr S T).
  Arguments mf_inr {S} {T}.

  Lemma inr_rlzr: mf_inr \realized_by mf_inr \wrt conv0 \and (conv +s+ conv0).
  Proof. by move => q a; split => [ | []// _ [<-]]; [exact/F2MF_dom |exists (inr a)]. Qed.

  Lemma cmbn_rlzr D D0 (conv': A ->> D) (conv0': A0 ->> D0) F G f:
    G \realized_by F \wrt conv \and conv0 -> f \realized_by G \wrt conv' \and conv0' ->
    f \realized_by F \wrt (conv' \o_R conv) \and (conv0' \o_R conv0).
  Proof.
    move => FrG Grf q a [d [qnd dna]] afd.
    have [dfd prp]:= Grf d a dna afd.
    have [qfd prp']:= FrG q d qnd dfd.
    split => // q' Fqq'.
    have [d' [Gdd' q'nd']]:= prp' q' Fqq'.
    have [d''' [d'nd''' fd'd''']]:= prp d' Gdd'.
    by exists d'''; split => //; exists d'.
  Qed.

  Context Q1 A1 Q2 A2 (conv1: Q1 ->> A1) (conv2: Q2 ->> A2).

  Lemma fprd_rlzr F f G g:
    f \realized_by F \wrt conv \and conv1 -> g \realized_by G \wrt conv0 \and conv2 ->
    (f ** g) \realized_by (F ** G) \wrt (conv ** conv0) \and (conv1 ** conv2).
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

  Lemma fsum_rlzr F f G g:
    f \realized_by F \wrt conv \and conv1 -> g \realized_by G \wrt conv0 \and conv2 ->
    (f +s+ g) \realized_by (F +s+ G) \wrt conv +s+ conv0 \and (conv1 +s+ conv2).
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
