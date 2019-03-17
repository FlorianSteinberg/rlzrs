From mathcomp Require Import ssreflect ssrfun.
From mf Require Import choice_mf.
Require Import all_ntrvw dict.
Import Morphisms.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section mf_rlzr_f.
Context (I: interview) (D: dictionary).

Definition mf_rlzr_f := make_mf (fun F (f: answers I -> answers D) => F \realizes (F2MF f)).

Lemma mf_rlzr_f_sing: mf_rlzr_f \is_singlevalued.
Proof.
move => F f g /rlzr_F2MF Frf /rlzr_F2MF Frg.
apply functional_extensionality => a.
have [q qna]:= conv_sur a.
have [[Fq FqFq] prp]:= Frf q a qna.
specialize (prp Fq FqFq).
have [_ prp']:= Frg q a qna.
specialize (prp' Fq FqFq).
by rewrite (@answers_unique D Fq (f a) (g a)).
Qed.
End mf_rlzr_f.

Section realizer_functions.
Context (D D': dictionary).

Definition frlzr := make_mf (fun F (f: answers D -> answers D') => (F2MF F) \realizes (F2MF f)).

Context (q': questions D').

Lemma frlzr_sur: frlzr \is_cototal.
Proof.
move => f.
have [F Frf]//:= rlzr_sur (F2MF f).
have [g gcF]:= exists_choice F q'.
by exists g; apply /icf_rlzr/gcF.
Qed.

Canonical frlzrs:= make_ntrvw frlzr_sur.

Lemma frlzr_sing: frlzr \is_singlevalued.
Proof. by move => F f g Frf Frg; exact/(mf_rlzr_f_sing Frf Frg). Qed.

Canonical frlzrs_dict:= @lift_ntrvw frlzrs frlzr_sing.

Lemma exte_tot S T: (@mf_exte S T) \is_total.
Proof. by move => f; exists f => /= s t. Qed.

(*
Lemma tight_rlzr: (@mf_tight Q Q') \realizes (@mf_tight A A').
Proof.
move => F f fcF _; split => [ | G tight]; first by exists F.
by exists f; split; first exact/tight_rlzr/tight.
Qed.*)
End realizer_functions.