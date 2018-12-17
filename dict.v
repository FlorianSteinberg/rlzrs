From mathcomp Require Import ssreflect ssrfun.
Require Import all_mf ntrvw.
Import Morphisms.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module dictionary_mixin.
Structure type Q (A: interview.type Q):= Pack {
answer_unique: (conversation A) \is_singlevalued;
}.
End dictionary_mixin.

Module dictionary.
Structure type Q:= Pack {
A :> interview Q;
mixin: dictionary_mixin.type A;
}.
End dictionary.
Coercion dictionary.A: dictionary.type >-> interview.type.
Coercion dictionary.mixin: dictionary.type >-> dictionary_mixin.type.
Notation dictionary := (dictionary.type).
Canonical make_modest_set Q (D: interview Q) (mixin: dictionary_mixin.type D) :=
	dictionary.Pack mixin.
Definition dictates Q (D: dictionary.type Q) :=
	interview_mixin.conversation (interview.mixin D).
Notation "a '\is_answer_to' q 'in' D" := (dictates D q a) (at level 2).
Notation "a \is_answer_to q" := (a \is_answer_to  q in _) (at level 2).
Definition answer_unique Q (A: dictionary Q) :=
	(@dictionary_mixin.answer_unique Q A A).
Arguments answer_unique {Q} {A}.
Definition make_dictm Q A (conv: Q ->> A) (sur: conv \is_cototal) (sing: conv \is_singlevalued):
  dictionary_mixin.type (make_ntrvw sur).
Proof. split; exact/sing. Defined.

Definition make_dict Q A (conv: Q ->> A) (sur: conv \is_cototal) (sing: conv \is_singlevalued):=
  dictionary.Pack (make_dictm sur sing).

Section dictionaries.
Context Q (A: dictionary Q).

Definition id_dictionary_mixin S: dictionary_mixin.type (id_interview S).
Proof. split; exact/F2MF_sing. Defined.

Definition id_dictionary S:= @dictionary.Pack S (id_interview S) (id_dictionary_mixin S).

Lemma comp_conv_sing (D: dictionary A): (comp_conv D) \is_singlevalued.
Proof. exact/rcmp_sing/answer_unique/answer_unique. Qed.

Definition combine_dictionaries_mixin (D: dictionary A):
	dictionary_mixin.type (@cmbn_ntrvw Q A D).
Proof. by split; exact/comp_conv_sing. Defined.

Canonical cmbn_dict (D'': dictionary A) :=
	dictionary.Pack (@combine_dictionaries_mixin D'').

Context  Q' (A': dictionary Q').

Lemma prod_conv_sing: (prod_conv A A') \is_singlevalued.
Proof. exact/fprd_sing/answer_unique/answer_unique. Qed.

Definition prod_dictionary_mixin: dictionary_mixin.type (prod_interview A A').
Proof. by split; exact/prod_conv_sing. Defined.

Canonical prod_dictionary := dictionary.Pack prod_dictionary_mixin.

Lemma sum_conv_sing: (sum_conv A A') \is_singlevalued.
Proof. exact/fsum_sing/answer_unique/answer_unique. Qed.

Definition sum_dictionary_mixin: dictionary_mixin.type (sum_interview A A').
Proof. split; exact/sum_conv_sing. Defined.

Canonical dictionary_sum := dictionary.Pack sum_dictionary_mixin.

Lemma list_conv_sing: (list_conv A) \is_singlevalued.
Proof.
elim => [L K -> -> | q R ih [ | a L] [ | b K]]//= [arq LnR] [brq KnR].
by rewrite (answer_unique q a b) // (ih L K).
Qed.

Definition list_dictionary_mixin: dictionary_mixin.type (list_interview A).
Proof. split; exact/list_conv_sing. Defined.

Canonical dictionary_list := dictionary.Pack list_dictionary_mixin.

Lemma rlzr_spec (F: Q ->> Q') f:
	F \realizes f <-> ((conversation A') \o F) \tightens (f \o (conversation A)).
Proof.
split => [Frf | tight].
	apply split_tight => q [a' [[a [aaq faa']] subs]].
		have [[q' Fqq'] prp]:= Frf q a aaq (subs a aaq).
		have [d' [d'aq' fad']]:= prp q' Fqq'.
		exists d'; split => [ | r' Fqr']; first by exists q'.
		by have [e' [e'aq' fae']]:= prp r' Fqr'; exists e'.
	move => d' [[q' [Fqq' d'aq']] subs'].
	split => [ | d daq]; last exact/subs.
	have [d'' [d''aq' fad'']]:= rlzr_val Frf aaq (subs a aaq) Fqq'.
	by exists a; split => //; rewrite (answer_unique q' d' d'').
move => q a aaq [a' faa'].
have qfd: q \from dom (f \o (conversation A)).
	exists a'; split => [ | d daq]; first by exists a.
	by exists a'; rewrite (answer_unique q d a).
split => [ | q' Fqq'].
	by have [ | d' [[q' [Fqq' d'aq']] subs]]:= (tight_dom tight) q; last by exists q'.
have [d' [[z' [Fqz' d'az']] subs]]:= (tight_dom tight) q qfd; have [e' e'aq']:= subs q' Fqq'.
have [ | [d [daq fdd']] subs']:= (tight_val tight qfd) e'; first by split; first by exists q'.
by exists e'; rewrite (answer_unique q a d); first split.
Qed.
End dictionaries.

Section mf_realizer.
Context Q (A: dictionary Q) Q' (A': interview Q').

Lemma rlzr_F2MF_eq F (f g: A' -> A):
	F \realizes (F2MF f) -> F \realizes (F2MF g) -> f =1 g.
Proof.
move => rlzr rlzr' a.
have [q arq]:= get_question a.
have [ | Fq FqFq]:= rlzr_dom rlzr arq; first exact/F2MF_dom.
have [ | fa [farFq ->]]:= rlzr_val rlzr arq _ FqFq; first exact/F2MF_dom.
have [ | ga [garFq ->]]:= rlzr_val rlzr' arq _ FqFq; first exact/F2MF_dom.
by rewrite (answer_unique Fq fa ga).
Qed.

Lemma rlzr_sur: (@mf_rlzr Q A Q' A') \is_cototal.
Proof.
move => f.
exists (make_mf (fun q Fq => forall a, a \is_response_to q -> exists fa, fa \is_response_to Fq /\ f a fa)).
move => q a qna [fa fafa]; split => [ | Fq FqFq]; last by have [a' []]:= FqFq a qna; exists a'.
have [Fq Fqnfa]:= get_question fa; exists Fq => a' qna'.
by exists fa; split => //; rewrite (answer_unique q a' a).
Qed.

Definition rlzr_interview_mixin: interview_mixin.type (Q ->> Q') (A ->> A').
Proof. exists mf_rlzr; exact rlzr_sur. Defined.

Canonical rlzrs := interview.Pack rlzr_interview_mixin.
End mf_realizer.