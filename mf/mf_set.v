(******************************************************************************)
(* This file provides a wrapper for functions of type S -> Prop which are     *)
(* interpreted as subsets of S. The wrapper is to allow nice notations that   *)
(* are only used in the appropriate places. The type is coerced into the      *)
(* sigma types.                                                               *)
(*                                                                            *)
(*       mf_subset.type S == The elements are functions S -> Prop.            *)
(*                          Coerced both into these functions and into        *)
(*                          the sigma types.                                  *)
(*          make_subset  == Notation for the constructor mf_subset.Pack       *)
(*           s \from A   == Elementhood relation. Notation for A s.           *)
(*            A === B    == equality of sets, i.e. notation for               *)
(*                          "s \from A <-> s \from B". The same as usual      *)
(*                          if propositional extensionality is assumed.       *)
(*             All       == constant function s => True where S is implicit.  *)
(*            empty      == constant function s => False where S is implicit. *)
(*          singleton s  == the singleton set containing only s, i.e.         *)
(*                          t \from S <-> t = s.                              *)
(*    A \is_subset_of B  == usual set inclusion, i.e.                         *)
(*                          "s \from A -> s \from B"                          *)
(*           A \n B      == set intersection                                  *)
(*           A \x B      == carthesian product of sets                        *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrfun.
Require Import Morphisms Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module mf_subset.
Structure type S := Pack {
P :> S -> Prop;
}.
End mf_subset.
Coercion mf_subset.P: mf_subset.type >-> Funclass.
Definition make_subset S (P: S -> Prop):= (mf_subset.Pack P).
Notation subset S := (mf_subset.type S).
Definition mf_sig S (P: subset S) := {s | P s}.
Coercion mf_sig: mf_subset.type >-> Sortclass.

Section mf_subsets.
Context (S: Type).

Definition set_equiv (P Q: subset S) := forall s, P s <-> Q s.
Notation "P === Q" := (set_equiv P Q) (at level 50).

Global Instance sqv_equiv: Equivalence set_equiv.
Proof.
split => // [P Q eq s | P Q R eq eq' s]; first by split => [Ps | Qs]; apply (eq s).
by split => [Ps | Rs]; [apply /eq' /eq | apply /eq /eq'].
Qed.

Notation "s '\from' P" := (P s) (at level 50).

Global Instance from_prpr:
	Proper (set_equiv ==> (@eq S) ==> iff) (@mf_subset.P S).
Proof. by move => P Q eq s _ <-; apply eq. Qed.

Definition subs (P Q : subset S) := forall s, P s -> Q s.
Notation "P '\is_subset_of' Q" := (subs P Q) (at level 50).

Global Instance subs_prpr:
	Proper (set_equiv ==> set_equiv ==> iff) subs.
Proof.
by move => P Q PeQ P' Q' P'eQ'; split => subs s; intros; apply /P'eQ' /subs /PeQ.
Qed.

Global Instance subs_ref: Reflexive subs.
Proof. by move => P P'. Qed.

Global Instance subs_trans: Transitive subs.
Proof. by move => P P' P'' PsP' P'sP'' s Ps; apply/P'sP''/PsP'. Qed.

Lemma set_eq_subs P Q:
	P === Q <-> (P \is_subset_of Q /\ Q \is_subset_of P).
Proof.
split; first by move => eq; split => s Ps; apply eq.
move => [subs subs'] s.
split => Ps; try apply subs => //.
by apply subs'.
Qed.

Lemma split_set_eq (P Q: subset S): P \is_subset_of Q -> Q \is_subset_of P -> P === Q.
Proof. by move => subs subs' s; split; [apply subs | apply subs']. Qed.

Definition All := make_subset (fun (_: S) => True).

Lemma subs_all P: P \is_subset_of All.
Proof. done. Qed. 

Definition empty := make_subset (fun (_: S) => False).

Lemma subs_empty P : empty \is_subset_of P.
Proof. done. Qed.

Definition singleton (s: S) := make_subset (fun t => s = t).

Definition intersects (P Q: subset S) := exists s, P s /\ Q s.
Notation "P '\intersects' Q" := (intersects P Q) (at level 50).

Lemma ntrsct_sym P Q: P \intersects Q <-> Q \intersects P.
Proof. by split; move => [s []]; exists s. Qed.

Definition intersection (P Q: subset S) := make_subset (fun s => P s /\ Q s).

Definition union T P P':= make_subset (fun (q: T) => P q \/ P' q).
Notation "P \n Q" := (intersection P Q) (at level 2).
End mf_subsets.
Notation "s \from P" := ((P: mf_subset.type _) s) (at level 70).
Notation "P === Q" := (set_equiv P Q) (at level 50).
Notation "P '\is_subset_of' Q" := (subs P Q) (at level 50).
Notation "P '\intersects' Q" := (intersects P Q) (at level 50).
Notation "P \n Q" := (intersection P Q) (at level 2).
Notation "P \u Q" := (union P Q) (at level 2).
Arguments All {S}.
Arguments empty {S}.

Section products.
Definition set_prod S T (P: mf_subset.type S) (Q: mf_subset.type T) :=
	make_subset (fun st => P st.1 /\ Q st.2).
Notation "P \x Q" := (set_prod P Q) (at level 40).

Global Instance sprd_prpr S T:
	Proper (@set_equiv S ==> @set_equiv T ==> @set_equiv (S*T)) (@set_prod S T).
Proof.
move => P P' eq Q Q' eq' s /=.
by rewrite eq eq'.
Qed.

Lemma sprd_All S T (P: mf_subset.type S) (Q: mf_subset.type T):
	P === All /\ Q === All -> P \x Q === All.
Proof. by move => [eq eq'] s /=; rewrite eq eq'. Qed.

Lemma sprd_All_inv S T (P: mf_subset.type S) (Q: mf_subset.type T) somes somet:
	P somes -> Q somet -> P \x Q === All -> P === All /\ Q === All.
Proof.
move => Ps Qt eq.
split => [s | t]; first by have [/= _ []]//:= eq (s, somet).
by have [/= _ []]//:= eq (somes, t).
Qed.

Lemma empty_prod S T : @empty (S * T) === empty \x empty.
Proof. by move => [s t]; split => // [[]]. Qed.

Lemma prod_eq S T (a c : subset S) (b d : subset T)
  : a === c -> b === d -> a \x b === c \x d.
Proof. by move => eq eq'; rewrite eq eq'. Qed.

Lemma prod_empty_l S T (A : subset S) (B : subset T)
  : A === empty -> (A \x B) === @empty (S * T).
Proof. by move => -> s; split => [[] | ]. Qed.
End products.
Notation "P \x Q" := (set_prod P Q) (at level 40).