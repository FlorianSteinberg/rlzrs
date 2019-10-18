From mathcomp Require Import ssreflect ssrfun seq.
Require Import all_ntrvw.
Import Morphisms.
Require Import FunctionalExtensionality ProofIrrelevance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section dictionaries.
  Class Dictionary Q A :=
    {
      description: Q ->> A;
      only_respond: description \is_cototal;
      answer_unique: description \is_singlevalued;
    }.

  Coercion D2I Q A (D: Dictionary Q A): Interview Q A :=
    Build_Interview (@only_respond Q A D).

  Definition lift_interview Q A (I: Interview Q A): I \is_singlevalued -> Dictionary Q A.
    move => sing; exact/Build_Dictionary/sing/conv_sur.
  Defined.
  Arguments lift_interview: clear implicits.
  Arguments lift_interview {Q} {A}.
  
  Lemma id_sing S: (@mf_id S) \is_singlevalued.
  Proof. by determinism. Qed.

  Definition id_dictionary S:= lift_interview (id_interview S) (@id_sing S).

  Context Q A (D: Dictionary Q A).

  Lemma answers_unique: description \is_singlevalued.
  Proof. exact/answer_unique. Qed.

  Ltac determinism := repeat mf.determinism || apply answer_unique.

  Global Instance list_dictionary: Dictionary (seq Q) (seq A).
    by apply/(lift_interview (list_interview D)); determinism.
  Defined.

  Global Instance sub_dictionary (B: subset A): Dictionary Q B.
  apply/(lift_interview (sub_interview D B)) => q [a P] [a' P']/= val val'.
  suff eq: a = a'.
  - by move: P'; rewrite -eq => P'; have <-: P = P' by apply/proof_irrelevance.
  exact/answer_unique/val'.
  Defined.

  Definition combine_dictionaries A' (D': Dictionary A A') : Dictionary Q A'.
    by apply/(lift_interview (combine_interviews D D')); determinism.
  Defined.

  Context Q' A' (D': Dictionary Q' A').
  
  Lemma rlzr_spec F (f: A ->> A'): f \realized_by F \wrt description \and description
                       <-> (description \o F) \tightens (f \o description).
  Proof.
    split => [Frf | tight].
    apply split_tight => q [a' [[a [aaq faa']] subs]].
    - have [[q' Fqq'] prp]:= Frf q a aaq (subs a aaq).
      have [d' [d'aq' fad']]:= prp q' Fqq'.
      exists d'; split => [ | r' Fqr']; first by exists q'.
      by have [e' [e'aq' fae']]:= prp r' Fqr'; exists e'.
    move => d' [[q' [Fqq' d'aq']] subs'].
    split => [ | d daq]; last exact/subs.
    - have [d'' [fad'' d''aq']]:= rlzr_val Frf aaq (subs a aaq) Fqq'.
      by exists a; split => //; rewrite (answer_unique d'aq' d''aq').
      move => q a aaq [a' faa'].
    have qfd: q \from dom (f \o description).
    - exists a'; split => [ | d daq]; first by exists a.
      by exists a'; rewrite (answer_unique daq aaq).
    split => [ | q' Fqq'].
    - by have [ | d' [[q' [Fqq' d'aq']] subs]]:= (tight_dom tight) q; last by exists q'.
    have [d' [[z' [Fqz' d'az']] subs]]:= (tight_dom tight) q qfd; have [e' e'aq']:= subs q' Fqq'.
    have [ | [d [daq fdd']] subs']:= (tight_val tight qfd) e'; first by split; first by exists q'.
    by exists e'; rewrite (answer_unique aaq daq); first split.
  Qed.

  Global Instance product_dictionary: Dictionary (Q * Q') (A * A').
    by apply/(lift_interview (prod_interview D D')); determinism.
  Defined.
    
  Global Instance sum_dictionary: Dictionary (Q + Q') (A + A').
    by apply/(lift_interview (sum_interview D D')); determinism.
  Defined.
End dictionaries.

Section mf_realizer.
  Context Q A Q' A' (D: Dictionary Q A) (I: Interview Q' A').

  Lemma rlzr_F2MF_eq F f g:
    (F2MF f) \realized_by F \wrt conversation \and description ->
    (F2MF g) \realized_by F \wrt conversation \and description -> f =1 g.
  Proof.
    move => rlzr rlzr' a.
    have [q arq]:= conv_sur I a.
    have [ | Fq FqFq]:= rlzr_dom rlzr arq; first exact/F2MF_dom.
    have [ | fa [-> farFq]]:= rlzr_val rlzr arq _ FqFq; first exact/F2MF_dom.
    have [ | ga [-> garFq]]:= rlzr_val rlzr' arq _ FqFq; first exact/F2MF_dom.
    exact/answer_unique/garFq/farFq.
  Qed.

  Lemma rlzr_sur: (make_mf (realizer description conversation)) \is_cototal.
  Proof.
    move => f.
    exists (make_mf (fun q Fq => forall a, a \from description q -> exists fa, fa \from conversation Fq /\ fa \from f a)).
    move => q a qna [fa fafa]; split => [ | Fq FqFq]; last by have [a' []]:= FqFq a qna; exists a'.
    have [Fq Fqnfa]:= conv_sur I fa; exists Fq => a' qna'.
    by exists fa; split => //; rewrite (answers_unique qna' qna).
  Qed.

  Definition rlzrs_interview : Interview _ _ := Build_Interview rlzr_sur.
End mf_realizer.
