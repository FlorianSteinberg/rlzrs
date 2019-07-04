From mathcomp Require Import ssreflect ssrfun.
Require Import all_ntrvw.
Import Morphisms.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section dictionaries.
  Class Dictionary Q A:=
    {
      description: Q ->> A;
      only_respond: description \is_cototal;
      answer_unique: description \is_singlevalued;
    }.

  Global Instance D2I `{D: Dictionary}: Interview Q A := Build_Interview only_respond.

  Coercion D2I: Dictionary >-> Interview.

  Definition I2D Q A
        (I: Interview Q A) (sing: (conversation_from I) \is_singlevalued): Dictionary Q A.
    by exists (conversation_from I); first exact/conv_sur.
  Defined.

  Lemma id_sing S: (@mf_id S) \is_singlevalued.
  Proof. exact/F2MF_sing. Qed.
  
  Definition id_dictionary T: Dictionary T T := Build_Dictionary (@id_sur T) (@id_sing T).

  Context `{D: Dictionary}.

  Lemma answers_unique: conversation \is_singlevalued.
  Proof. exact/answer_unique. Qed.

  Context  `{D0: Dictionary}.

  Global Instance prod_dictionary: Dictionary (Q * Q0) (A * A0).
  Proof. exact/I2D/fprd_sing/answer_unique/answer_unique. Defined.
    
  Global Instance sum_dictionary: Dictionary (Q + Q0) (A + A0).
  Proof. exact/I2D/fsum_sing/answer_unique/answer_unique. Defined.

  Lemma map_sing S T (f: S ->> T): f \is_singlevalued -> (mf_map f) \is_singlevalued.
  Proof.
    move => sing L K K'.
    elim : L K K' => [ | q L ih]; first by case => //; case.    
    case => // a K; case => // a' K' /=[fqa lst] [fqa' lst'].
    rewrite (sing q a a' fqa fqa'); f_equal.
    exact/ih.
  Qed.

  Global Instance list_dictionary: Dictionary (list Q) (list A).
  Proof. exact/I2D/map_sing/answer_unique. Defined.

  Lemma rlzr_spec F f: F \realizes f \wrt D \and D0
                       <-> ((conversation_from D0) \o F) \tightens (f \o (conversation_from D)).
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
      by exists a; split => //; rewrite (answer_unique d'aq' d''aq').
      move => q a aaq [a' faa'].
    have qfd: q \from dom (f \o (conversation_from D)).
    - exists a'; split => [ | d daq]; first by exists a.
      by exists a'; rewrite (answer_unique daq aaq).
    split => [ | q' Fqq'].
    - by have [ | d' [[q' [Fqq' d'aq']] subs]]:= (tight_dom tight) q; last by exists q'.
    have [d' [[z' [Fqz' d'az']] subs]]:= (tight_dom tight) q qfd; have [e' e'aq']:= subs q' Fqq'.
    have [ | [d [daq fdd']] subs']:= (tight_val tight qfd) e'; first by split; first by exists q'.
    by exists e'; rewrite (answers_unique aaq daq); first split.
  Qed.
End dictionaries.
Notation "a '\is_answer_to' q '\wrt' D" := (description D q a) (at level 2).

Section mf_realizer.
  Context `{D: Dictionary} `{I: Interview}.

  Lemma rlzr_F2MF_eq F f g:
    F \realizes (F2MF f) \wrt I \and D -> F \realizes (F2MF g) \wrt I \and D -> f =1 g.
  Proof.
    move => rlzr rlzr' a.
    have [q arq]:= conv_sur a.
    have [ | Fq FqFq]:= rlzr_dom rlzr arq; first exact/F2MF_dom.
    have [ | fa [farFq ->]]:= rlzr_val rlzr arq _ FqFq; first exact/F2MF_dom.
    have [ | ga [garFq ->]]:= rlzr_val rlzr' arq _ FqFq; first exact/F2MF_dom.
    exact/answer_unique/garFq/farFq.
  Qed.

  Lemma rlzr_sur: (make_mf (realizer D I)) \is_cototal.
  Proof.
    move => f.
    exists (make_mf (fun q Fq => forall a, a \is_response_to q \wrt D -> exists fa, fa \is_response_to Fq \wrt I /\ f a fa)).
    move => q a qna [fa fafa]; split => [ | Fq FqFq]; last by have [a' []]:= FqFq a qna; exists a'.
    have [Fq Fqnfa]:= conv_sur fa; exists Fq => a' qna'.
    by exists fa; split => //; rewrite (@answers_unique Q A D q a' a).
  Qed.

  Definition rlzrs_interview := Build_Interview rlzr_sur.
End mf_realizer.