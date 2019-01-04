(******************************************************************************)
(* This file provides some lemmas about multivalued functions that are only   *)
(* true if the Axiom of choice (or different choice axioms) are assumed. It   *)
(* is not exported by the all_mpf file and has to be imported separately.     *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrfun.
Require Import mf_set mf.
Import Morphisms.
Require Import Classical ChoiceFacts.

Axiom choice: FunctionalChoice.
Arguments choice {A} {B} {R}.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope mf_scope.

Section choice_mf.
  Context (S T: Type).
  Lemma exists_choice (F: S ->> T) (t: T):
    exists f, f \is_choice_for F.
  Proof.
    pose R s t := forall Fs, F s Fs -> F s t.
    have [s | f tot]:= @choice _ _ R; last by exists f => s; apply /tot.
    case: (classic (s \from dom F)) => [[] t' fst | false]; first by exists t'.
    by exists t => t' fst'; exfalso; apply false; exists t'.
  Qed.

  Lemma fun_spec (f: S ->> T) (t: T): f \is_function <->
     f \is_singlevalued /\ f \is_total.
  Proof.
    split => [ [g eq] | [sing tot]].
    - by split; rewrite -eq; [apply F2MF_sing | apply F2MF_tot].
    have [g icf]:= exists_choice f t.
    by exists g; apply/sing_tot_F2MF_icf.
  Qed.

  Lemma icf_tight (g f: S ->> T): (forall s, exists t', ~ f s t')
    -> (forall h, (h \is_choice_for g -> h \is_choice_for f)) -> (g \tightens f).
  Proof.
    move => ex prop s [t fst].
    split => [ | t' gst'].
    - have [t' nfst']:= (ex s).
      pose g' := make_mf (fun x y => (x <> s -> g x y) /\ (x = s -> y = t')).
      have [h icf'] := (exists_choice g' t).
      apply NNPP => nex.
      have ngst': ~g s t' by move => gst'; apply nex; exists t'.
      have icf: h \is_choice_for g.
      + move => s' t'' gs't''.
	case (classic (s' = s)) => [eq | neq].
	* by exfalso; apply nex; exists t''; rewrite -eq.
	have g's't'': g' s' t'' by split => // eq; exfalso; apply neq.
	exact: ((icf' s' t'' g's't'').1 neq).
      suffices eq: h s = t' by apply nfst'; rewrite -eq; apply: (prop h icf s t).
      have g'st': g' s t' by trivial.
      by apply (icf' s t' g'st').2.
    pose g' := make_mf (fun x y => g x y /\ (x = s -> y = t')).
    have gtg: g' \tightens g.
    - move => x xfd.
      split => [ | y g'xy]; last by apply g'xy.1.
      case (classic (x = s)) => [ eq | neq ]; first by exists t'; rewrite eq.
      by have [y gxy]:= xfd; exists y; by split.
    have [h icf']:= (exists_choice g' t).
    have icf: h \is_choice_for g.
    - apply icf_spec.
      apply/ tight_trans; first by apply/ gtg.
      by apply icf_spec; apply icf'.
    suffices val: h s = t' by rewrite -val; apply/ (prop h icf s t).
    have val': g s t' /\ (s = s -> t' = t') by split.
    by apply: (icf' s t' val').2.
  Qed.
End choice_mf.

Lemma pfun_spec S T (f: S ->> T): f \is_partial_function <-> f \is_singlevalued.
Proof.
  split => [[g <-] | sing]; first exact/PF2MF_sing.
  pose F:= make_mf (fun s t =>
    (exists t', t = Some t' /\ f s t') \/ (~ s \from dom f /\ t = None)).
  have [g icf]:= exists_choice F None.
  have: F \is_total => [s' | tot].
  - case: (classic (s' \from dom f)) => [[fs' fs'fs'] | neg]; last by exists None; right.
    by exists (Some (fs')); left; exists fs'.
  exists g => s t /=; have [fs fsfs]:= tot s.
  case E: (g s) => [gs |].
  - have [[t' []] | []]:= icf s (fs) fsfs; last by rewrite E.
    by rewrite E => [[<- fsgs]]; split => [<- | fst]//; apply/sing/fst.
  by split => // fst; have [[t' []] | [ndm _]]:= icf s fs fsfs; [rewrite E |apply ndm; exists t].
Qed.