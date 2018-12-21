From mathcomp Require Import ssreflect ssrfun.
Require Import all_mf ntrvw.
Import Morphisms.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module dictionary.
  Record mixin_of (I: interview) :=
    Mixin {
        answers_unique: (conversation I) \is_singlevalued;
        }.

  Notation class_of := mixin_of (only parsing).

  Structure type :=
    Pack {sort; _ :class_of sort}.
End dictionary.

Section dictionaries.
  Local Notation dictionary:= dictionary.type.
  Definition get_ntrvw (D: dictionary): interview.
    case: D => I; intros; apply/I.
  Defined.
  Local Coercion get_ntrvw: dictionary >-> interview.
  Local Notation description := conversation.
  Local Notation "a '\is_answer_to' q 'in' D" := (description D q a) (at level 2).
  Local Notation "a \is_answer_to q" := (a \is_answer_to  q in _) (at level 2).
  
  Lemma answers_unique (D: dictionary): (description D) \is_singlevalued.
    Proof. by case: D => [I []]. Qed.
  Arguments answers_unique {D}.
  Local Notation answer_unique := answers_unique.
  Definition make_dict Q A (conv: Q ->> A) (sur: conv \is_cototal) (sing: conv \is_singlevalued):=
    dictionary.Pack (@dictionary.Mixin (make_ntrvw sur) sing).

  Definition lift_ntrvw (I: interview) (sing: (conversation I) \is_singlevalued): dictionary:=
    dictionary.Pack (dictionary.Mixin sing).

  Definition id_dictionary (S: Type): dictionary.
    exists (id_interview S); split; exact/F2MF_sing.
  Defined.
  Context  (D D': dictionary).
  
  Lemma prod_conv_sing: (prod_conv D D') \is_singlevalued.
  Proof. exact/fprd_sing/answer_unique/answer_unique. Qed.
  
  Definition prod_dictionary_mixin := dictionary.Mixin prod_conv_sing.
  Canonical prod_dictionary:= dictionary.Pack prod_dictionary_mixin.

  Lemma sum_conv_sing: (sum_conv D D') \is_singlevalued.
  Proof. exact/fsum_sing/answer_unique/answer_unique. Qed.

  Definition sum_dictionary_mixin := dictionary.Mixin sum_conv_sing.
  Canonical sum_dictionary:= dictionary.Pack sum_dictionary_mixin.
  
  Lemma map_sing S T (f: S ->> T): f \is_singlevalued -> (mf_map f) \is_singlevalued.
  Proof.
    move => sing L K K'.
    elim : L K K' => [ | q L ih]; first by case => //; case.    
    case => // a K; case => // a' K' /=[fqa lst] [fqa' lst'].
    rewrite (sing q a a' fqa fqa'); f_equal.
    exact/ih.
  Qed.
  
  Lemma list_conv_sing: (list_conv D) \is_singlevalued.
  Proof. exact/map_sing/answers_unique. Qed.

  Definition list_dictionary_mixin:= dictionary.Mixin list_conv_sing.
  Canonical list_dictionary:= dictionary.Pack list_dictionary_mixin.

  Lemma rlzr_spec F f:
	F \realizes f <-> ((conversation D') \o F) \tightens (f \o (conversation D)).
  Proof.
    split => [Frf | tight].
    apply split_tight => q [a' [[a [aaq faa']] subs]].
    - have [[q' Fqq'] prp]:= Frf q a aaq (subs a aaq).
      have [d' [d'aq' fad']]:= prp q' Fqq'.
      exists d'; split => [ | r' Fqr']; first by exists q'.
      by have [e' [e'aq' fae']]:= prp r' Fqr'; exists e'.
    move => d' [[q' [Fqq' d'aq']] subs'].
    split => [ | d daq]; last exact/subs.
    - have [d'' [d''aq' fad'']]:= rlzr_val Frf aaq (subs a aaq) Fqq'.
      by exists a; split => //; rewrite (answer_unique q' d' d'').
    move => q a aaq [a' faa'].
    have qfd: q \from dom (f \o (conversation D)).
    - exists a'; split => [ | d daq]; first by exists a.
      by exists a'; rewrite (answer_unique q d a).
    split => [ | q' Fqq'].
    - by have [ | d' [[q' [Fqq' d'aq']] subs]]:= (tight_dom tight) q; last by exists q'.
    have [d' [[z' [Fqz' d'az']] subs]]:= (tight_dom tight) q qfd; have [e' e'aq']:= subs q' Fqq'.
    have [ | [d [daq fdd']] subs']:= (tight_val tight qfd) e'; first by split; first by exists q'.
    by exists e'; rewrite (answer_unique q a d); first split.
  Qed.
End dictionaries.
Notation dictionary:= dictionary.type.
Coercion get_ntrvw: dictionary >-> interview.
Notation description := conversation.
Notation "a '\is_answer_to' q 'in' D" := (description D q a) (at level 2).
Notation "a \is_answer_to q" := (a \is_answer_to  q in _) (at level 2).
Notation answer_unique := answers_unique.

Section mf_realizer.
  Context (D: dictionary) (I: interview).

  Lemma rlzr_F2MF_eq F (f g: answers I -> answers D):
    F \realizes (F2MF f) -> F \realizes (F2MF g) -> f =1 g.
  Proof.
    move => rlzr rlzr' a.
    have [q arq]:= conv_sur a.
    have [ | Fq FqFq]:= rlzr_dom rlzr arq; first exact/F2MF_dom.
    have [ | fa [farFq ->]]:= rlzr_val rlzr arq _ FqFq; first exact/F2MF_dom.
    have [ | ga [garFq ->]]:= rlzr_val rlzr' arq _ FqFq; first exact/F2MF_dom.
    by rewrite (@answers_unique D Fq fa ga).
  Qed.

  Lemma rlzr_sur: (@mf_rlzr D I) \is_cototal.
  Proof.
    move => f.
    exists (make_mf (fun q Fq => forall a, a \is_response_to q -> exists fa, fa \is_response_to Fq /\ f a fa)).
    move => q a qna [fa fafa]; split => [ | Fq FqFq]; last by have [a' []]:= FqFq a qna; exists a'.
    have [Fq Fqnfa]:= conv_sur fa; exists Fq => a' qna'.
    by exists fa; split => //; rewrite (@answers_unique D q a' a).
  Qed.

  Definition rlzrs_interview_mixin:= interview.Mixin rlzr_sur.
  Canonical rlzrs_interview_struc:= interview.Struc rlzrs_interview_mixin.
  Canonical rlzrs_interview:= interview.Pack rlzrs_interview_struc.
  End mf_realizer.