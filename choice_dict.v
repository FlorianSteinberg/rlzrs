From mathcomp Require Import ssreflect ssrfun.
From mf Require Import classical_mf.
Require Import all_ntrvw dict.
Import Morphisms.
Require Import FunctionalExtensionality ChoiceFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section mf_rlzr_f.
  Context Q A (I: Interview Q A) Q' A' (D: Dictionary Q' A').
  
  Definition mf_rlzr_f := make_mf (fun F f => (F2MF f) \realized_by F \wrt conversation \and description).
  
  Lemma mf_rlzr_f_sing: mf_rlzr_f \is_singlevalued.
  Proof.
    move => F f g /rlzr_F2MF Frf /rlzr_F2MF Frg.
    apply functional_extensionality => a.
    have [q qna]:= conv_sur I a.
    have [[Fq FqFq] prp]:= Frf q a qna.
    specialize (prp Fq FqFq).
    have [_ prp']:= Frg q a qna.
    specialize (prp' Fq FqFq).
    exact/answer_unique/prp'/prp.
  Qed.
End mf_rlzr_f.

Section realizer_functions.
  Context `{D: Dictionary} `{D0: Dictionary}.

  Definition frlzr := make_mf (fun F f => (F2MF f) \realized_by (F2MF F) \wrt D \and D0).

  Context (q0: Q0).

  Lemma frlzr_sur: FunctionalChoice_on Q Q0 -> frlzr \is_cototal.
  Proof.
    move => choice f.
    have [F Frf]//:= rlzr_sur D D0 (F2MF f).
    have [g gcF]:= exists_choice F q0 choice.
    by exists g; apply /icf_rlzr/gcF.
  Qed.

  Lemma frlzr_sing: frlzr \is_singlevalued.
  Proof. by move => F f g Frf Frg; exact/(mf_rlzr_f_sing Frf Frg). Qed.

  Global Instance frlzrs: FunctionalChoice_on Q Q0 -> Dictionary (Q -> Q0) (A -> A0).
    by move => choice; exists (frlzr); first exact/frlzr_sur; exact/frlzr_sing.
  Defined.

  Lemma exte_tot S T: (@mf_exte S T) \is_total.
  Proof. by move => f; exists f => /= s t. Qed.

  (*
    Lemma tight_rlzr: (@mf_tight Q Q') \realizes (@mf_tight A A').
    Proof.
    move => F f fcF _; split => [ | G tight]; first by exists F.
    by exists f; split; first exact/tight_rlzr/tight.
    Qed.*)
End realizer_functions.
