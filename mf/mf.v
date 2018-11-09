(******************************************************************************)
(* This file provides a class of relations interpreted as multivalued         *)
(* functions. The main difference between relations and multivalued functions *)
(* is how they are composed, the composition for multivalued functions is     *)
(* Chosen such that it works well with realizability. The difference          *)
(* between multifunction and relational composition is that for the latter    *)
(* the whole image of s under f is required to be included in the domain of g *)
(* for f \o g s r to be true. Note that in ssreflect, \o is a notation for the*)
(* composition of regular functions, this notation is remapped to \o_f.       *)
(*                                                                            *)
(*            S ->> T    == The elements are functions S -> subset T.         *)
(*                          Coerced into the functions of type S -> T -> Prop *)
(*            make_mf    == Notation for the constructor mf.Pack.             *)
(*            f =~= g    == equality of multivalued functions, i.e.           *)
(*                          "forall s, f s === g s" or                        *)
(*                          "forall s t, f s t <-> g s t"                     *)
(*             F2MF      == "function to multifunction" sends a function      *)
(*                          f: S -> T to the multifunction s => singleton f s *)
(*                          i.e. F2MF f s t <-> f s = t                       *)
(*            f\^-1      == inverse multifunction, i.e. f s t <-> f\^-1 t s   *)
(*            dom f      == set of elements s such that f s is not empty.     *)
(*           codom f     == dom f\^-1                                         *)
(*             mf_id     == F2MF id i.e. mf_id s === singleton s              *)
(*           empty_mf    == constant function returning the empty set.        *)
(*             f|_A      == restriction of f to the subset A, i.e.            *)
(*                          "f|_A s = if s \from A then f s else empty"       *)
(*             f|^A      == corestriction, i.e. "f|^A = (f\^-1|_A)\^-1"       *)
(*           f \o_R g    == relational composition of f and g, i.e. of        *)
(*                          f: S ->> T and g: R ->> S, i.e. f \o_R g s r      *)
(*                          <-> forall s, f s intersects g\^-1 r              *)
(*            f \o g     == The composition of multivalued functions          *)
(*                          i.e. if f: S ->> T and g: R ->> S, then           *)
(*                          f \o g : R ->> T and f \o g r t <->               *)
(*                          f s \is_subset_of dom g /\ f \o_R g r t           *)
(*        f \is_total    == "forall s, s \from dom f" or "dom f === All"      *)
(*      f \is_cototoal   == forall s, s \from codom f equivalent to           *)
(*                          surjectivity when f comes from a function.        *)
(*    f \is_singlevalued == "forall s t t', f s t -> f s t' -> t = t'"        *)
(*                          i.e. fs is a singleton or empty (classically)     *)
(*      f \extends g     == subset inclusion in the sense of relations        *)
(*                          for functions this reduces to the usual notion    *)
(*                          of extensions, however for multivalued functions  *)
(*                          the next is the better generaliztaion             *)
(*      f \tightens g    == f has a bigger domain but less values when        *)
(*                          restricted to the domain of g. Interpreted as a   *)
(*                          computational task, this means that g is easier   *)
(*                          to solve.                                         *)
(*   f \is_choice_for g  == equivalent to (F2MF f) \tightens g. It means that *)
(*                          f selects trough g, i.e. f(s) \from g s whenever  *)
(*                          the latter is non-empty.                          *)
(*           f ** g      == is the product "f ** g (s, t) === f s \x g t"     *)
(*                          its function version **_f is given by             *)
(*                          "f **_f g (s, t) = (f(s), g(t))" and satisfies    *)
(*                          "(F2MF f) ** (F2MF g) =~= F2MF (f **_f g)".       *)
(*           f +s+ g     == same as above with sums.                          *)
(* Some other standardfunctions are given shortcuts like mf_id to avoid lots  *)
(* of bracketing.                                                             *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrfun seq.
Require Import mf_set.
Require Import Morphisms.
 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope mf_scope.
Module mf.
  Structure type S T :=
    Pack {
        value:> S -> (mf_subset.type T);
      }.
End mf.

Notation mf := mf.type.
Coercion mf.value: mf >-> Funclass.
Notation "S ->> T" := (mf S T) (at level 50): mf_scope.
Definition make_mf S T (f: S -> T -> Prop) := mf.Pack (fun s => mf_subset.Pack (fun t => f s t)).
Canonical get_mf S T (f: S -> subset T) := mf.Pack f.

(* The following should be considered to define equality as multivalued functions *)
Definition equiv S T (f g: S ->> T) := (forall s, f s === g s).

Definition mf_iff S T f g := forall (s: S) (t: T), f s t <-> g s t.
Global Instance make_mf_prpr S T: Proper (@mf_iff S T ==> @equiv S T) (@make_mf S T).
Proof. done. Qed.

Global Instance eqiuv_equiv S T: Equivalence (@equiv S T).
Proof.
split => // [f g eq s t | f g h feg geh s t]; first by split => [gst | fst]; apply eq.
by split => [fst | hst]; [apply geh; apply feg | apply feg; apply geh].
Qed.
Notation "f =~= g" := (equiv f g) (at level 70): mf_scope.

Global Instance value_prpr S T:
	Proper (@equiv S T ==> eq ==> (@set_equiv T)) (@mf.value S T).
Proof. by move => P Q eq s _ <-; apply eq. Qed.

Section Basics.
  Definition F2MF S T (f : S -> T) : (S ->> T) := make_mf (fun s => singleton (f s)).

  Lemma F2MF_spec S T (f: S -> T) s t: F2MF f s t <-> f s = t.
  Proof. done. Qed.

  Global Instance F2MF_prpr S T: Proper (@eqfun T S ==> @equiv S T) (@F2MF S T).
  Proof. by move => f g eq s t; rewrite /F2MF /= eq. Qed.

  Lemma F2MF_eq S T (f g: S -> T): f =1 g <-> (F2MF f) =~= (F2MF g).
  Proof. by split => [eq s t/= | eq s]; [split => <-; rewrite (eq s) | have ->:= (eq s (f s)).1]. Qed.

  Definition PF2MF S T (f: S -> option T): (S ->> T) :=
    make_mf (fun s => match f s with
	              |	None => empty
	              | Some fs => singleton fs
                      end).
  
  Lemma P2MF_spec S T (f: S -> option T) s t: PF2MF f s t <-> f s = Some t.
  Proof. by rewrite /PF2MF; split => /=[ | ->]//; case: (f s)=> // _ ->. Qed.

  Global Instance PF2MF_prpr S T: Proper (@eqfun (option T) S ==> @equiv S T) (@PF2MF S T).
  Proof. by move => f g eq s t; rewrite /F2MF /= eq. Qed.

  Lemma PF2MF_eq S T (f g: S -> option T): f =1 g <-> PF2MF f =~= PF2MF g.
  Proof.
    split => [eq s /= t | eq s].
    - case E: (f s) => [t' | ]//; case E': (g s) => [t''| ]//; try by move: E'; rewrite -eq E.
      by split => <-; apply/Some_inj; rewrite -E' -E eq.
    have /=:= eq s; case E: (f s) => [fs | ]; case E': (g s) => [gs | ] // eq'; first by rewrite (eq' fs).1.
    - by have []:= (eq' fs).1.
    by have []:= (eq' gs).2.
  Qed.
  
  Lemma F2MF_PF2MF S T (f: S -> T): F2MF f =~= PF2MF (Some \o f).
  Proof. done. Qed.

  Definition inverse S T (f: S ->> T) := make_mf (fun t s => f s t).
  Local Notation inv f := (inverse f).
  Local Notation "f '\inverse'" := (inverse f) (at level 50).
  Local Notation "f '\^-1'" := (inverse f) (format "f '\^-1'", at level 50).
  Definition mf_inverse S T := F2MF (@inverse S T).

  Lemma inv_inv S T (f: S ->> T): (f\^-1)\^-1 =~= f.
  Proof. done. Qed.

  Global Instance inv_prpr S T: Proper ((@equiv S T) ==> (@equiv T S)) (@inverse S T).
  Proof. by move => f g eq s t; apply (eq t s). Qed.

  Definition inv_img S T (f: S ->> T) (P: mf_subset.type T) := make_subset (fun s => exists t, f s t /\ P t).
  Lemma invimg_spec S T (f: S ->> T) P s : inv_img f P s <-> intersects P (f s).
  Proof. by split; move => [t []]; exists t. Qed.
  
  Definition img S T (f: S ->> T) P := inv_img (inv f) P.

  (* The domain of a multifunctions is the set of all inputs such that the value set
     is not empty. *)
  Definition dom S T (f: S ->> T) := make_subset (fun s => exists t, f s t).
  
  Lemma dom_crct S T f (s: S): s \from dom (make_mf f) <-> exists (t: T), f s t.
  Proof. done. Qed.
  
  Lemma dom_spec S T (f: S ->> T): dom f === (inv_img f All).
  Proof. by split => [[t] | [t []]]; exists t. Qed.
  
  Global Instance dom_prpr S T: Proper ((@equiv S T) ==> (@set_equiv S)) (@dom S T).
  Proof. by move => f g eq s; split; move => [t]; exists t; apply (eq s t). Qed.
  
  Lemma F2MF_dom S T (f: S -> T): dom (F2MF f) === All.
  Proof. by move => s; split => // _; exists (f s). Qed.
  
  Definition codom S T (f: S ->> T):= make_subset (fun t => exists s, f s t).
  (* the codomain of a multi-valued function is the union of all its value sets. It should
     not be understood as the range, as very few of its elements may be hit by a choice function. *)
  Lemma codom_spec S T (f: S ->> T): codom f === (img f All).
  Proof. by split => [[t] | [t []]]; exists t. Qed.

  Lemma codom_crct S T (f: S ->> T) t : t \from codom f <-> exists s, f s t.
  Proof. done. Qed.
  
  Lemma codom_dom_inv S T (f: S ->> T): codom f === dom (f\^-1).
  Proof. done. Qed.
  
  Lemma inv_dom_codom S T (f: S ->> T) t:
    t \from codom f <-> t \from dom (f\^-1).
  Proof. exact/codom_dom_inv. Qed.

  Global Instance codom_prpr S T: Proper ((@equiv S T) ==> (@set_equiv T)) (@codom S T).
  Proof. by move => f g eq; rewrite !codom_dom_inv eq. Qed.
  
  Definition mf_id S:= F2MF (@id S).
  
  Arguments mf_id {S}.

  Lemma id_inv S: mf_id\^-1 =~=@mf_id S.
  Proof. done. Qed.

  Definition mf_empty S T := make_mf (fun (s: S) => @empty T).
  Arguments mf_empty {S} {T}.

  Lemma empty_inv S T: mf_empty \inverse =~= (@mf_empty T S).
  Proof. done. Qed.
  
  Lemma empty_dom S T (f : S ->> T): dom f === empty <-> f =~= mf_empty.
  Proof.
    split => [eq s t | eq]; last by split => // [[t fst]]; apply/eq/fst.
    by split => // fst; apply/eq; exists t; apply/fst. 
  Qed.

  Definition corestr S T (f: S ->> T) (P: mf_subset.type T) := make_mf (fun s t => P t /\ f s t).
  Local Notation "f '\corestricted_to' P" := (corestr f P) (at level 2).
  Local Notation "f '|^' P" := (corestr f P) (format "f '|^' P", at level 2).

  Lemma corestr_crct S T (f: S ->> T) P s t: f|^P s t <-> P t /\ f s t.
  Proof. done. Qed.

  Lemma corestr_spec S T (f: S ->> T) P s: (f|^P) s  === intersection P (f s).
  Proof. done. Qed.

  Lemma corestr_all S T (f: S ->> T): f =~= (f|^All).
  Proof. by move => s t; split => // [[]]. Qed.

  Global Instance corestr_prpr S T:
    Proper (@equiv S T ==> @set_equiv T ==> @equiv S T) (@corestr S T).
  Proof.
    move => f g feqg P Q PeqQ s t.
    by split => [[Ps fst] | [Qs gst]]; split => //; try apply PeqQ; try apply feqg.
  Qed.

  Definition restr S T (f: S ->> T) (P: mf_subset.type S) := make_mf (fun s t => P s /\ f s t).
  Local Notation "f '\restricted_to' P" := (restr f P) (at level 2).
  Local Notation "f '|_' P" := (restr f P) (format "f '|_' P", at level 2).

  Lemma restr_dom S T (f: S ->> T): f|_(dom f) =~= f.
  Proof. by move => s t; split => [[] | fst] //; split => //; exists t. Qed.

  Lemma dom_restr_spec S T (f: S ->> T) P s:
    s \from dom (f|_P) <-> s \from dom f /\ P s.
  Proof. by split => [[t []] | [[t]]]; first split; try by exists t. Qed.

  Lemma dom_restr_subs S T (f: S ->> T) P Q:
    P \is_subset_of Q -> dom (f|_P) \is_subset_of dom (f|_Q).
  Proof. by move => subs s [t [fst Pt]]; exists t; split; first apply/subs. Qed.
  
  Lemma corestr_restr_inv S T (f: S ->> T) P: f|_P =~= ((f\^-1)|^P)\^-1.
  Proof. done. Qed.

  Lemma restr_crct S T (f: S ->> T) P s t: (f \restricted_to P) s t <-> P s /\ f s t.
  Proof. done. Qed.

  Lemma restr_all S T (f: S ->> T): f =~= (f|_All).
  Proof. by move => s t; split => // [[]]. Qed.
  
  Global Instance restr_prpr S T: Proper (@equiv S T ==> @set_equiv S ==> @equiv S T) (@restr S T).
  Proof.
    move => f g feqg P Q PeqQ s t.
    by split => [[Ps fst] | [Qs gst]]; split => //; try apply PeqQ; try apply feqg.
  Qed.

  Lemma restr_eq_r {S T : Type} (f : S ->> T) (P Q : subset S): P === Q -> f|_P =~= f|_Q.
  Proof. by move ->. Qed.

  Lemma restr_inv S T (f: S ->> T) P: (f|_P)\^-1 =~= (f\^-1)|^P.
  Proof. done. Qed.
End Basics.
Notation "f =~= g" := (equiv f g) (at level 70): mf_scope.
Notation inv f := (inverse f).
Notation "f '\inverse'" := (inverse f) (at level 70): mf_scope.
Notation "f '\^-1'" := (inverse f) (format "f '\^-1'", at level 30): mf_scope.
Notation "f '\corestricted_to' P" := (corestr f P) (at level 2): mf_scope.
Notation "f '|^' P" := (corestr f P) (format "f '|^' P", at level 2): mf_scope.
Notation "f '\restricted_to' P" := (restr f P) (at level 2): mf_scope.
Notation "f '|_' P" := (restr f P) (format "f '|_' P", at level 2): mf_scope.
Arguments mf_id {S}.

Section relational_composition.
  Definition mf_rel_comp R S T (f : S ->> T) (g : R ->> S) :=
    make_mf (fun r t => (exists s, g r s /\ f s t)).
  Local Notation "f '\o_R' g" := (mf_rel_comp f g) (at level 50).

  Global Instance rcmp_prpr R S T:
    Proper ((@equiv S T) ==> (@equiv R S) ==> (@equiv R T)) (@mf_rel_comp R S T).
  Proof.
    move => f f' eqf g g' eqg r t.
      by split; move => [s [grs fst]]; exists s; by split; [apply /eqg | apply /eqf].
  Qed.

  Lemma rcmp_assoc S T S' T' (f: S' ->> T') g (h: S ->> T):
    ((f \o_R g) \o_R h) =~= (f \o_R (g \o_R h)).
  Proof.
    split; last by move => [t' [[s' []]]]; exists s'; split => //; exists t'.
    by move => [t' [hst [s'[]]]]; exists s'; split => //; exists t'.
  Qed.

  Lemma rcmp_inv R Q Q' (f: Q ->> Q') (g: R ->> Q):
    (f \o_R g)\^-1 =~= (g\^-1) \o_R (f\^-1).
  Proof. by move => r q'; split; move =>[q []]; exists q. Qed.

  Notation "f \o_f g" := (f \o g) (at level 30).
  Lemma rcmp_F2MF R S T (f: S ->> T) (g: R -> S):
    (f \o_R (F2MF g)) =~= make_mf (fun r => f (g r)).
  Proof. by move => r t /=; split => [[s [-> fst]] | fgrt]//; exists (g r). Qed.

  Lemma F2MF_rcmp_F2MF R S T (f: S -> T) (g: R -> S):
    (F2MF f \o_R F2MF g) =~= F2MF (f \o_f g).
  Proof. by move => s t; rewrite rcmp_F2MF /=. Qed.

  Local Notation "f '\o_p' g" := (pcomp f g) (at level 50).

  Lemma PF2MF_rcmp_PF2MF R S T (f: S -> option T) (g: R -> option S):
    (PF2MF f \o_R PF2MF g) =~= PF2MF (f \o_p g).
  Proof.
    move => r t; split => [[s [/=]] | ].
    - by rewrite /pcomp; case: (g r) => //= _ -> ; case: (f s) => // t' <- .
    by rewrite /pcomp/=; case (g r) => // s; exists s.
  Qed.

  Lemma rcmp_dom R Q Q' (f: Q ->> Q') (g: R ->> Q):
    dom (f \o_R g) \is_subset_of dom g.
  Proof. by move => r [q' [q []]]; exists q. Qed.

  Lemma rcmp_dom_codom R S T (f: S ->> T) (g: T ->> R):
    codom f \is_subset_of dom g -> dom f === dom (g \o_R f).
  Proof.
    move => dm r; split => [[t ftr] | ]; last by apply rcmp_dom.
    have [ | r' gtr']:= dm t; first by exists r.
    by exists r'; exists t.
  Qed.

  Lemma rcmp_id_restr S T (f: S ->> T) P: f \o_R mf_id|_P =~= f|_P.
  Proof.
    move => s t.
    split; first by move => [_ [[Ps/= <-] ]].
    by move => [ps fst]; exists s.
  Qed.

  Lemma rcmp_id_l S T (f: S ->> T):
    mf_id \o_R f =~= f.
  Proof. by move => s t; split => [[t' [fst' <-]] | fst]//; exists t. Qed.

  Lemma rcmp_id_r S T (f: S ->> T):
    f \o_R mf_id =~= f.
  Proof. by move => s t; split => [[t' [-> fst']] | fst]//; exists s. Qed.
End relational_composition.
Notation "f '\o_R' g" := (mf_rel_comp f g) (at level 2): mf_scope.
Notation "f \o_f g" := (f \o g) (at level 30): mf_scope.
Notation "f '\o_p' g" := (pcomp f g) (at level 50): mf_scope.

Lemma restr_rcmp_equiv S T S' T' (f f': S ->> T) (g: S' ->> S) (g': T' ->> S') (q: T') a:
  g' q a -> f|_(g \o_R g' q) =~= f'|_(g \o_R g' q) -> f|_(g a) =~= f'|_(g a).
Proof.
  move => gqa eq s t.
  split => [[gas fst] | [gas f'st]]; first by split => //; apply (eq s t).1; split; first by exists a.
  by split => //; apply (eq s t).2; split; first by exists a.
Qed.

Section composition.
  Definition composition R S T (f : S ->> T) (g : R ->> S) :=
    make_mf (fun r t => (f \o_R g) r t /\ (g r) \is_subset_of (dom f)).
  Local Notation "f '\o' g" := (composition f g) (at level 50).

  Global Instance comp_prpr R S T: Proper ((@equiv S T) ==> (@equiv R S) ==> (@equiv R T)) (@composition R S T).
  Proof.
    move => f f' eqf g g' eqg s t; split; case.
    - split; last by move => r g'sr; rewrite -eqf; apply/b/eqg.
      by move: a => [r stf]; exists r; rewrite -(eqf r t) -(eqg s r).
    split; last by move => r g'sr; rewrite eqf; apply/b/eqg.
    by move: a => [r stf]; exists r; rewrite (eqf r t) (eqg s r).
  Qed.
  
  Lemma comp_F2MF R S T (f: S ->> T) (g: R -> S):
    (f \o (F2MF g)) =~= make_mf (fun r => f (g r)).
  Proof.
    split => [[[r [/=-> fst]] prop] | fgrt] //.
    by split => [ | r eq]; [exists (g s) | exists s0; rewrite -eq].
  Qed.

  Lemma comp_F2MF_eq_r S T R (f g : T ->> R) (h : S -> T)
    : f =~= g -> f \o (F2MF h) =~= g \o (F2MF h).
  Proof. by move => ->. Qed.

  Lemma F2MF_comp_F2MF R S T (f: S -> T) (g: R -> S): (F2MF f \o F2MF g) =~= F2MF (f \o_f g).
  Proof. by move => s t; rewrite comp_F2MF /=. Qed.

  Lemma PF2MF_comp_PF2MF R S T (f: S -> option T) (g: R -> option S):
    (PF2MF f \o PF2MF g) =~= PF2MF (f \o_p g).
  Proof.
    move => r t.
    split.
    - rewrite <- PF2MF_rcmp_PF2MF.
      intros [A _].
      exact A.
    rewrite /pcomp/obind/oapp/=.
    case E: (g r) => [s | ]//.
    case E': (f s) => // eq.
    split; first by exists s; split => //; rewrite E'.
    by move => k /= <-; exists t; rewrite E'.
Qed.

  Lemma comp_rcmp_corestr R S T (f: R ->> S) (g: S ->> T):
    g \o_R f =~= g \o f|^(dom g).
  Proof.
    move => r t; split => [[s [frs gst]] | [[s [[]]]]]; last by exists s.
    by split => [ | s' []]//; exists s; split => //; split => //; exists t.
  Qed.

  Lemma comp_eq_r {S T U : Type} (f : S ->> T) (g h : T ->> U)
    : g =~= h -> (g \o f) =~= (h \o f).
  Proof. by move ->. Qed.
  
  Lemma comp_val_eq S T R (f : S ->> T) (g h : T ->> R) s
    : g|_(f s) =~= h|_(f s) -> (g \o f) s === (h \o f) s.
  Proof.
    move => eq r.
    split; case => [[t [fsr grt] ] subs].
    - split => [ | t' fst']; first by exists t; split =>//; have [[]]//:= eq t r.
    by have [ | r' gt'r']//:= subs t'; exists r'; have [[]]//:= eq t' r'.
    split => [ | t' fst']; first by exists t; split =>//; have [_ []]//:= eq t r.
    by have [ | r' gt'r']//:= subs t'; exists r'; have [_ []]//:= eq t' r'.
  Qed.

  Local Notation "f '\is_section_of' g" := (f \o g =~= F2MF id) (at level 2).

  Lemma sec_cncl S T (f: S -> T) g:
    (F2MF f) \is_section_of (F2MF g) <-> cancel g f.
  Proof.
    split; last by intros; rewrite comp_F2MF /F2MF => s t; split => <-.
    by move => eq s; move: (eq s s); rewrite (comp_F2MF _ g _ s) /F2MF /= => ->.
  Qed.

  Lemma sec_pcncl S T (f: S -> option T) g: (PF2MF f) \is_section_of (F2MF g) <-> pcancel g f.
  Proof.
    split => [sec t | cncl t t']; first by have /=[|[_ [<-]]]//:= (sec t t).2; case E: (f (g t)) => [t'|] // ->.
    rewrite /=; split => [[[_ [<-]]] | <-]; first by rewrite (cncl t).
    by split => [ | _ <- /=]; [exists (g t) | exists t]; rewrite (cncl t).
  Qed.

  Lemma sec_ocncl S T (f: S -> T) g: (F2MF f) \is_section_of (PF2MF g) -> ocancel g f.
  Proof.
    rewrite !F2MF_PF2MF PF2MF_comp_PF2MF -PF2MF_eq/pcomp/obind/oapp => sec t.
    by have /=:= sec t; case E: (g t) => [s' | ]// => [[<-]].
  Qed.

  Lemma comp_dom R Q Q' (f: Q ->> Q') (g: R ->> Q):
    dom (f \o g) \is_subset_of dom g.
  Proof. by move => r [s [[t[]]]]; exists t. Qed.

  Lemma comp_subs_dom R S T (f: S ->> T) (g: T ->> R) s:
    f s \is_subset_of dom g -> s \from dom f <-> s \from dom (g \o f).
  Proof.
    move => subs.
    split; last by move => [r [[t [fst]]]]; exists t.
    move => [t fst].
    have [r gtr]:= subs t fst.
    by exists r; split; first by exists t.
  Qed.

  Lemma comp_dom_codom R S T (f: S ->> T) (g: T ->> R):
    codom f \is_subset_of dom g -> dom f === dom (g \o f).
  Proof.
    move => subs s; apply /comp_subs_dom => t fst.
    by apply subs; exists s.
  Qed.

  Lemma comp_codom R S T (f: S ->> T) (g: T ->> R):
    codom (g \o f) \is_subset_of codom g.
  Proof. by move=> r /codom_crct [s] [[t [fst gtr]] _]; exists t. Qed.

  Lemma comp_codom_dom R S T (f: S ->> T) (g: T ->> R):
    codom f \is_subset_of dom g -> codom g|_(codom f) === codom (g \o f).
  Proof.
    move => subs r.
    split.
    - move => /codom_crct [t [/codom_crct [s fst] gtr]].
      rewrite codom_crct; exists s.
      split => [ | t' fst']; first by exists t.
      by apply subs; exists s.
    move => /codom_crct [s [[t [fst gtr]]] subs'].
    by rewrite codom_crct; exists t; split; first exists s.
  Qed.

  (* This operation is associative *)
  Lemma comp_assoc S T S' T' (f: S' ->> T') g (h: S ->> T):
    ((f \o g) \o h) =~= (f \o (g \o h)).
  Proof.
    move => r q.
    split => [ [] [] s [] hrs [] [] t []| [] [] t [] [] [] s [] ].
    - split => [ | t' [] [] s' [] hrs'].
      + exists t; split => //; split => [ | s' hrs']; first by exists s.
        by move: (b1 s' hrs') => [] x [] [] t' []; exists t'.
      by move: (b1 s' hrs') => [] q' comp gs't _; apply comp.2.
    split => [ | s' hrs'].
    - exists s; split => //.
      split => [ | t' gst']; first by exists t.
      suffices ghrs: (g \o h) r t' by apply (b2 t' ghrs).
      by split => [ | s' hrs']; [exists s | apply b0].
    move: (b0 s' hrs') => [] t' gs't'.
    have ghrt': (g \o h) r t' by split => [ | s'' hrs'']; [exists s' | apply b0].
    move: (b2 t' ghrt') => [] q' ft'q'; exists q'.
    split => [ | t'' gs't'']; first by exists t'.
    suffices ghrt'': (g \o h) r t'' by apply b2.
    by split => [ | s'' hrs'']; [exists s' | apply b0].
  Qed.

  Lemma comp_id_restr S T (f: S ->> T) P: f \o mf_id|_P =~= f|_P.
  Proof.
    by move => s t; split => [[[_ [[Ps <-]]]] | []] //; split => [ | t' [_ <-]]; [exists s | exists t].
  Qed.

  Lemma comp_id_l S T (f: S ->> T):
    mf_id \o f =~= f.
  Proof.
    split => [[[t' [fst <-]] _] | fst] //; by split => [ | t' fst']; [exists s0 | exists t'].
  Qed.

  Lemma comp_id_r S T (f: S ->> T):
    f \o mf_id =~= f.
  Proof.
    by split => [[[t' [<- fst]] _] | fst] //; split => [| t' <- ]; [exists s|exists s0].
  Qed.

  Lemma comp_empty_l S T R (f: S ->> T): (@mf_empty T R) \o f =~= (@mf_empty S R).
  Proof. by split => //=; move => [[a []]]. Qed.
  
  Lemma comp_empty_r S T R (f: S ->> T): f \o (@mf_empty R S) =~= (@mf_empty R T).
  Proof. by split => //=; move => [[a []]]. Qed.
End composition.
Notation "f '\o' g" := (composition f g) (at level 50): mf_scope.

Section totals.
  Definition total S T (f: S ->> T):= forall s, s \from dom f.    
  Definition totals S T := make_subset (fun (f: S ->> T) => total f).  
  Local Notation "f \is_total" := (total f) (at level 30).

  Global Instance tot_prpr S T: Proper ((@equiv S T) ==> iff) (@total S T).
  Proof.
    by move => f g eq; split => tot s; have [t]:= tot s; exists t; [rewrite -eq| rewrite eq].
  Qed.

  Context (S T S' T': Type).

  Lemma tot_spec Q Q' (f: Q ->> Q'): f \is_total <-> (dom f === All).
  Proof. by split => prp s; [have /=:= prp s | rewrite prp]. Qed.

  Lemma rcmp_tot_dom R (f: S ->> T) (g: T ->> R):
    g \is_total -> (dom f) === (dom (g \o_R f)).
  Proof.
    move => tot s; split => [[t frt] | [r [t []]]]; last by exists t.
    by have[r gtr]:= tot t; exists r; exists t.
  Qed.

  Lemma comp_tot_dom R (f: S ->> T) (g: T ->> R):
    g \is_total -> (dom f) === (dom (g \o f)).
  Proof.
    move => /tot_spec tot.
    apply comp_dom_codom.
    rewrite tot; exact/subs_all.
  Qed.

  Lemma comp_tot R (f: S ->> T) (g: T ->> R):
    f \is_total -> g \is_total -> (g \o f) \is_total.
  Proof. by move => /tot_spec tot tot'; apply/tot_spec; rewrite -comp_tot_dom. Qed.

  Lemma rcmp_tot R (f: S ->> T) (g: T ->> R):
    f \is_total -> g \is_total -> (g \o_R f) \is_total.
  Proof. by move => /tot_spec tot tot'; apply/tot_spec; rewrite -rcmp_tot_dom. Qed.

  Lemma tot_subs_dom R (f: S ->> T) (g: S ->> T) (h: T ->> R):
    codom g \is_subset_of dom h-> dom (h \o g) \is_subset_of dom (h \o f) -> dom g \is_subset_of dom f.
  Proof.
    move => tot dm s [t gst].
    have [ | r [[t' []]]]:= dm s; last by exists t'.
    have [ | r htr] //:= tot t; first by exists s.
    by exists r; split => [ | t' gst']; [exists t | apply tot; exists s].
  Qed.

  Lemma F2MF_tot (f: S -> T): (F2MF f) \is_total.
  Proof. by move => s; exists (f s). Qed.

  (* For total multi valued functions, the relational composition is identical to the multi-
     function composition.  *)
  Lemma comp_rcmp R  (f : S ->> T) (g : R ->> S):
    f \is_total -> f \o g =~= f \o_R g.
  Proof.
    move => /tot_spec tot s t; split => [ | comp]; first by case.
    by split => //; rewrite tot; exact/ subs_all.
  Qed.

  Definition surjective S T (f: S -> T) := forall t, exists s, f s = t.
  Definition surjectives S T:= make_subset (fun (f: S -> T) => surjective f).
  Local Notation "f '\is_surjective'" := (surjective f) (at level 30).

  Definition psurjective S T f := forall (t: T), exists (s: S), f s = some t.
  Definition psurjectives S T := make_subset (fun (f: S -> option T) => psurjective f).
  Local Notation "f '\is_psurjective'":= (psurjective f) (at level 30).

  Lemma sur_psur (f: S -> T): f \is_surjective <-> (Some \o_f f) \is_psurjective.
  Proof.
    by split => sur t; have [s val]:= sur t; exists s; [rewrite -val | have[]:= val].
  Qed.

  Definition cototal S T (f: S ->> T) := forall t, t \from codom f.
  Definition cototals S T := make_subset (fun (f: S ->> T) => cototal f).
  Local Notation "f '\is_cototal'" := (cototal f) (at level 30).

  Lemma F2MF_cotot (f: S -> T): f \is_surjective <-> (F2MF f) \is_cototal.
  Proof. done. Qed.

  Lemma PF2MF_cotot (f: S -> option T): f \is_psurjective <-> (PF2MF f) \is_cototal.
  Proof.
    split => sur t; first by have [s eq]:= sur t; exists s; rewrite /= eq.
    by have [s /=]:= sur t; case E: (f s) => // eq; exists s; rewrite -eq.
  Qed.

  Lemma cotot_spec (f: S ->> T): f \is_cototal <-> codom f === All.
  Proof. by split => ass s; first split => // _; apply/ass. Qed.
  
  Lemma cotot_tot_inv (f: S ->> T):
    f \is_cototal <-> (f \inverse) \is_total.
  Proof. by rewrite cotot_spec codom_dom_inv tot_spec. Qed.

  Global Instance cotot_prpr: Proper (@equiv S T ==> iff) (@cototal S T).
  Proof. by move => f g eq; rewrite cotot_tot_inv eq. Qed.
End totals.
Notation "f '\is_total'" := (total f) (at level 2): mf_scope.
Notation "f '\is_cototal'" := (cototal f) (at level 2): mf_scope.
Notation "f \is_surjective" := (surjective f) (at level 2): mf_scope.
Notation "f \is_psurjective":= (psurjective f) (at level 2): mf_scope.

Section forces.
  Context (S T: Type).
  Definition forces (f: S ->> T) := make_mf (fun s t => forall t', f s t' -> t' = t).

  Global Instance frcs_prpr: Proper ((@equiv S T) ==> @equiv S T) (forces).
  Proof. by move => f g eq s t; split => frcs t'; [rewrite -eq | rewrite eq]; exact/frcs. Qed.

  Lemma F2MF_frcs (f: S -> T): forces (F2MF f) =~= F2MF f.
  Proof. by move => s t /=; split => [prp | <- t' <-]//; rewrite (prp (f s)). Qed.

  (* The same does not hold for PF2MF: PF2MF relates elements outside of the domain to
     all of T. *)  
End forces.

Section singlevalueds.
  Context (S T S' T': Type).
  (* For representations we should sieve out the single valued surjective partial functions. *)
  Definition singlevalued S T (f: S ->> T) := forall s t t', f s t -> f s t' -> t = t'.
  Definition singlevalueds S T := make_subset (fun (f: S ->> T) => singlevalued f).
  Notation "f '\is_singlevalued'" := (singlevalued f) (at level 2).

  Lemma sing_spec (f: S ->> T): f \is_singlevalued <-> (dom f) \is_subset_of dom (forces f).
  Proof.
    split => [sing s [t fst] | sing s t t' fst fst']; first by exists t => t' fst'; apply/sing/fst/fst'.
    by have [ | t'' det]:= sing s; [exists t | rewrite (det t) //(det t')].
  Qed.

  Lemma dom_frcs (f: S ->> T): f|_(dom (forces f)) \is_singlevalued.
  Proof. by move => s t t' [[t'' frcs] fst] [_ fst']; rewrite (frcs t) // (frcs t'). Qed.

  Global Instance sing_prpr S T: Proper ((@equiv S T) ==> iff) (@singlevalued S T).
  Proof. by split => sing s t t' fst fst'; apply /(sing s t t'); apply /H. Qed.

  Lemma empty_sing: (@mf_empty S T) \is_singlevalued.
  Proof. done. Qed.
  
  Lemma F2MF_sing (f: S-> T): (F2MF f) \is_singlevalued.
  Proof. by move => s t t' H H0; rewrite -H0. Qed.

  Lemma PF2MF_sing R R' (f: R -> option R'): (PF2MF f) \is_singlevalued.
  Proof. by move => s t t' /=; case: (f s) => //t'' <- <-. Qed.

  Lemma sing_rcmp R Q Q' (f: Q ->> Q') (g: R ->> Q):
    g \is_singlevalued -> f \o g =~= f \o_R g.
  Proof.
    move => sing s r.
    split => [ | [t [gst ftr]]]; first by case.
    split => [ | t' gst']; first by exists t.
    by rewrite (sing s t' t) => //; exists r.
  Qed.

  Lemma rcmp_cotot R (f: R ->> T) (g: S ->> R):
    f \is_cototal -> g \is_cototal -> (f \o_R g) \is_cototal.
  Proof. by move => fct gct t; have [r frt]:= fct t; have [s gsr]:= gct r; exists s; exists r. Qed.

  Lemma comp_cotot R (f: R ->> T) (g: S ->> R):
    g \is_singlevalued -> f \is_cototal -> g \is_cototal -> (f \o g) \is_cototal.
  Proof.
    move => sing fct gct t.
    have [r frt]:= fct t; have [s gsr]:= gct r.
    exists s; split => [ | r' gsr']; first by exists r.
    by rewrite (sing s r' r) => //; exists t.
  Qed.

  Lemma comp_sur R (f: R -> T) (g: S -> R):
    f \is_surjective -> g \is_surjective -> (f \o_f g) \is_surjective.
  Proof.
    by move => sur sur' s; have [r fsr]:= sur s; have [t grt]:= sur' r; exists t; rewrite/= -fsr grt.
  Qed.

  Lemma comp_psur R (f: R -> option T) (g: S -> option R):
    f \is_psurjective -> g \is_psurjective -> (f \o_p g) \is_psurjective.
  Proof.
    move => /PF2MF_cotot cotot /PF2MF_cotot cotot'.
    by rewrite PF2MF_cotot -PF2MF_comp_PF2MF; apply/comp_cotot/cotot'/cotot/PF2MF_sing.
  Qed.

  Lemma sing_inj_comp_inv R Q Q' (f: Q ->> Q') (g: R ->> Q):
    g \is_singlevalued -> f\^-1 \is_singlevalued -> (f \o g)\^-1 =~= (g\^-1) \o (f\^-1).
  Proof. by move => gsing finj; rewrite !sing_rcmp //; apply/rcmp_inv. Qed.

  Lemma corestr_inv (f: S ->> T) P: (f|^P)\^-1 =~= f\^-1|_P.
  Proof. done. Qed.

  Lemma sing_comp_inv (f: S ->> T):
    f \is_singlevalued -> f \o (f\^-1) =~= mf_id|_(codom f).
  Proof.
    move => sing.
    split => [[[r [frs frt]] dm] | [[t' fst'] <-]]; first by split; [exists r | apply /sing/frt].
    by split => [ | s']; [exists t' | exists s].
  Qed.

  Lemma mfinv_inj_sing (f: S -> T): injective f <-> (F2MF f)\^-1 \is_singlevalued.
  Proof. by split => [inj s t t' eq eq' | sing s t eq]; [apply/inj; rewrite eq eq' | apply/sing]. Qed.

  Lemma restr_sing_w (f: S ->> T) P: f \is_singlevalued -> (f \restricted_to P) \is_singlevalued.
  Proof. by move => sing s t t' [_ fst [_ fst']]; apply (sing s t t'). Qed.

  Lemma restr_sing (f: S ->> T) P Q:
    P \is_subset_of Q -> f|_Q \is_singlevalued -> f|_P \is_singlevalued.
  Proof.
   by move => subs sing s t t' [Ps fst [_ fst']]; apply/sing; split; try apply/subs; try apply/fst.
  Qed.

  Lemma comp_sing (f: T ->> T') (g : S ->> T) :
    f \is_singlevalued -> g \is_singlevalued -> (f \o g) \is_singlevalued.
  Proof.
    move => fsing gsing r t t' [[] s [] grs fst _ [][] s' [] grs' fs't' _].
    by rewrite (fsing s t t') => //; rewrite (gsing r s s').
  Qed.

  Lemma rcmp_sing (f: T ->> T') (g : S ->> T) :
    f \is_singlevalued -> g \is_singlevalued -> (f \o_R g) \is_singlevalued.
  Proof.
    move => fsing gsing r t t' [s [grs fst]] [s' [grs' fs't]].
    by rewrite (fsing s t t') => //; rewrite (gsing r s s').
  Qed.

  Lemma sing_comp R (f : S ->> T) (g : R ->> S):
    g \is_singlevalued -> g \is_total -> f \o g =~= make_mf (fun r t => forall y, g r y -> f y t).
  Proof.
    move => sing tot.
    split => [[[r [grs fst]] prop] y gsy | fgrt ]; first by rewrite (sing s y r).
    split => [ | r gsr]; last by exists s0; apply/ (fgrt r).
    by have [r gsr] := tot s; by exists r; split; last by apply fgrt.
  Qed.
End singlevalueds.
Notation "f '\is_singlevalued'" := (singlevalued f) (at level 2): mf_scope.

Section epi_mono.
  Context (S T S' T': Type).
  (* the following are taken from category theory. *)
  Definition epimorphism (f: S ->> T) := forall Q (g h: T ->> Q), g \o f =~= h \o f -> g =~= h.
  Definition epimorphisms:= make_subset (fun (f: S ->> T) => epimorphism f).
  Local Notation "f '\is_epi'" := (epimorphism f) (at level 2).
  Definition monomorphism (f: S ->> T):= forall Q (g h: Q ->> S), f \o g =~= f \o h -> g =~= h.
  Definition monomorphisms := make_subset (fun (f: S ->> T) => monomorphism f).
  Local Notation "f '\is_mono'" := (monomorphism f) (at level 2).

  Lemma empty_not_mono (s: S): ~(@mf_empty S T) \is_mono.
  Proof.
    move => inj.
    pose g := F2MF (fun (b: bool) => s).
    pose h := @mf_empty bool S.
    suff eq: g =~= h by have /=<-:= eq true s.
    apply inj.
    by rewrite !comp_empty_l.
  Qed.

  Lemma inj_F2MF_mono (f : S -> T): injective f -> (F2MF f) \is_mono.
  Proof.
    move => inj R g h.
    rewrite !comp_rcmp => [ eq s t | | ]; try exact/F2MF_tot.
    split => [gst | hst]; have []:= eq s (f t).
    - move => []; first by exists t.
      by move => t' [] hst' /inj <-.
    move => _ []; first by exists t.
    by move => t' [] gst' /inj <-.
  Qed.

  (* Classically, being an epimorphism implies being cototal (see file classical_mf.v).
     The opposite implication does not hold in general *)
  Lemma cotot_notepi (f: S ->> T) (s: S) (t t': T):
    ~ t = t' -> exists f, f \is_cototal /\ ~ f \is_epi.
  Proof.
    move => neq.
    pose f' := @make_mf S T (fun s t => True).
    exists f'; split => [ | sur ]; first by exists s.
    pose g := make_mf (fun k b => k = t /\ b = true).
    pose h := make_mf (fun k b => k = t /\ b = false).
    suffices eq: g \o f' =~= h \o f'.
    - have [a b]:= (((sur bool g h) eq) t false).
      + by suffices htt: h t false by move: (b htt).2.
      by split; move => [ [] _ [] _ [] _ _ prop];
    by have [ | b' [eq]]:= (prop t' _); last by exfalso; apply neq.
  Qed.

  (* Again Classically, the inverse is true for singlevalud functions (see classical_mf.v).
     Thus the following is named correctly. *)
  Definition surjective_partial_functions:= intersection (singlevalueds S T) (cototals S T).

  Definition functions := make_subset (fun F => exists (f: S -> T), F2MF f =~= F).

  Definition partial_functions:= make_subset (fun (F: S ->> T) => exists f, PF2MF f =~= F).
End epi_mono.
Notation "f '\is_mono'" := (monomorphism f) (at level 2): mf_scope.
Notation "f '\is_epi'" := (epimorphism f) (at level 2): mf_scope.
Notation "f '\is_surjective_partial_function'" := (f \from (surjective_partial_functions _ _)) (at level 2): mf_scope.
Notation "f '\is_function'" := (f \from (functions _ _ )) (at level 2): mf_scope.
Notation "f '\is_partial_function'":= (f \from (partial_functions _ _)) (at level 2): mf_scope.

Section tightenings.
  Definition extends S T (f g: S ->> T) := forall s, f s \is_subset_of g s.
  Notation "g '\extends' f" := (extends f g) (at level 50): mf_scope.
  Definition mf_exte S T := make_mf (@extends S T).
  Arguments mf_exte {S} {T}.
  
  Global Instance exte_refl S T: Reflexive (@extends S T).
  Proof. by move => s t fst. Qed.

  Global Instance exte_trans S T: Transitive (@extends S T).
  Proof. by move => f g h gef heg s t fst; apply/heg/gef. Qed.

  Definition pextends S T (f g: S -> option T):= forall s t, f s = some t -> g s = some t.

  Lemma PF2MF_pexte_PF2MF S T (f g: S -> option T):
    (PF2MF g) \extends (PF2MF f) <-> pextends f g.
  Proof.
    split => exte s t /=; first by move => E; have /=:= exte s t; rewrite E; case: (g s) => // gs ->.
    by case E: (f s) => [fs | ]// <-; case E': (g s) => [gs | ]//; have := exte _ _ E; rewrite E' //; case.
  Qed.

  Global Instance exte_prpr S T: Proper (@equiv S T ==> @equiv S T ==> iff) (@extends S T).
  Proof. by move => f f' feq g g' geq; split => exte s t gst; apply/geq/exte/feq. Qed.

  Definition tight S T (g f: S ->> T):=
    forall s, s \from dom g -> s \from dom f /\ forall t, f s t -> g s t.
  Notation "f '\is_tightened_by' g" := (tight f g) (at level 2).
  Notation "g '\tightens' f" := (tight f g) (at level 2).
  Definition mf_tight S T:= make_mf (@tight S T).
  Arguments mf_tight {S} {T}.

  Global Instance tight_prpr S T:
    Proper ((@equiv S T) ==> (@equiv S T) ==> iff) (@tight S T).
  Proof.
    move => f f' eqf g g' eqg.
    split => tight s sfd; split => [ | t gst].
          by rewrite -eqg; have [ | fd prp]:= tight s; first by rewrite eqf.
        by have [ | fd prp]:= tight s; [rewrite eqf| rewrite -(eqf s t); apply prp; rewrite (eqg s t)].
      by rewrite eqg; have [ | fd prp]:= tight s; first by rewrite -eqf.
    by have [ | fd prp]:= tight s; [rewrite -eqf| rewrite (eqf s t); apply prp; rewrite -(eqg s t)].
  Qed.

  Context (S T: Type).

  Lemma split_tight (f g: S ->> T):
    (dom g) \is_subset_of (dom f) -> (forall s, s \from dom g -> (f s) \is_subset_of (g s)) ->
    f \tightens g.
  Proof. by move => dm val; split; [apply/dm | apply/val]. Qed.
  
  Lemma tight_dom (f g: S ->> T):
    f \tightens g -> (dom g) \is_subset_of (dom f).
  Proof. by move => tight s sfd; have []:= tight s sfd. Qed.
  
  Lemma tight_val (f g: S ->> T) s:
    f \tightens g -> s \from dom g -> (f s) \is_subset_of (g s).
  Proof. by move => tight sfd; have []:= tight s sfd. Qed.
  
  Lemma tight_spec (f g: S ->> T):
    f \tightens g <-> dom g \is_subset_of dom f /\ g \extends f|_(dom g).
  Proof.
    split => [tight | [subs exte]]; last by apply/split_tight => // s sfd t' fst'; apply/exte.
    by split => [ | s t [sfd]]; [apply/tight_dom | apply/tight_val].
  Qed.

  Lemma tight_equiv (f g: S ->> T): f \tightens g -> g \tightens f -> f =~= g.
  Proof.
    move => tight tight' s t; split => [fst | gst].
      by apply /(tight_val tight); first by apply /(tight_dom tight'); exists t.
    by apply /(tight_val tight'); first by apply /(tight_dom tight); exists t.
  Qed.

  Lemma exte_equiv (f g: S ->> T) : f =~= g <-> f \extends g /\ g \extends f.
  Proof.
    split => [eq | [gef feg] s t]; first by split => s t val; apply/eq.
    by split => ass; [apply/feg | apply/gef].
  Qed.

  Lemma exte_restr (f: S ->> T) P Q: P \is_subset_of Q -> f|_Q \extends f|_P.
  Proof. by move => subs s t []; split => //; apply subs. Qed.

  Lemma restr_exte (f g: S ->> T) P P':
    P \is_subset_of P' -> f|_P' \extends g|_P' -> f|_P \extends g|_P.
  Proof. by move => subs eq s t [Ps gst]; split => //; apply eq; split => //; apply/subs. Qed.

  Lemma restr_equiv (f g: S ->> T) P P':
    P \is_subset_of P' -> f|_P' =~= g|_P' -> f|_P =~= g|_P.
  Proof.
    by rewrite !exte_equiv => subs [exte1 exte2]; split; apply/restr_exte; try apply/subs.
  Qed.

  (* tight is almost an equivalence relation, it only fails to be symmetric *)
  Global Instance tight_ref: Reflexive (@tight S T).
  Proof. done. Qed.
  
  Global Instance tight_trans: Transitive (@tight S T).
  Proof.
    move => f g h tight tight'.
    apply /split_tight => [ | s sfd]; first exact/subs_trans/tight_dom/tight'/tight_dom.
    exact/subs_trans/tight_val/sfd/tight/tight_val/tight_dom/sfd.
  Qed.
  
  Lemma sing_tight_exte (f: S ->> T) g:
    f \is_singlevalued -> g \tightens f -> g \extends f.
  Proof.
    move => sing tight s t fst.
    have sfd: s \from dom f by exists t.
    have [t' gst']:= tight_dom tight sfd.
    rewrite (sing s t t') //.
    exact/tight_val/gst'.
  Qed.
  
  Lemma mf_tight_exte:
    mf_exte|_(singlevalueds S T) \extends mf_tight|_(singlevalueds S T).
  Proof. by move => f [g] []; split; last apply/sing_tight_exte. Qed.

  Lemma exte_dom (f g: S ->> T):
    g \extends f -> (dom f) \is_subset_of (dom g).
  Proof. by move => exte s [t fst]; exists t; apply exte. Qed.

  Lemma sing_exte_tight (f: S ->> T) g:
    g \is_singlevalued -> g \extends f -> g \tightens f.
  Proof.
    move => gsing exte.
    apply split_tight => s [t]; first by exists t; apply exte.
    move => fst t' gst'; have gst := exte s t fst.
    by rewrite (gsing s t' t).
  Qed.

  Lemma mf_exte_tight:
    mf_tight|^(singlevalueds S T) \extends mf_exte|^(singlevalueds S T).
  Proof. by move => f [g] []; split; last apply/sing_exte_tight. Qed.
  
  Lemma exte_tight (f: S ->> T) g:
    f \is_singlevalued -> g \is_singlevalued -> (g \extends f <-> g \tightens f).
  Proof. split; [exact: sing_exte_tight | exact: sing_tight_exte] . Qed.

  Lemma exte_sing (f: S ->> T) (g: S ->> T):
    f \extends g -> f \is_singlevalued -> g \is_singlevalued.
  Proof. move => exte sing s t t' gst gst'; apply /sing; apply exte; [apply gst | apply gst']. Qed.

  Lemma exte_comp R (f f': T ->> R) (g: S ->> T):
    f \extends f' -> (f \o g) \extends (f' \o g).
  Proof.
    move => fef s r [[t [gst ftr] prop]].
    split => [ | t' gst']; first by exists t; split => //; apply fef.
    specialize (prop t' gst').
    have [r' f't'r']:= prop.
    by exists r'; apply fef.
  Qed.

  Lemma tight_restr_w (f: S ->> T) P: f \tightens (f|_P).
  Proof. by move => s [t [Ps fst]]; by split; first by exists t. Qed.

  Lemma tight_restr_r (f g: S ->> T) P Q:
    P \is_subset_of Q -> f \tightens (g|_Q) -> f \tightens (g|_P).
  Proof.
    move => subs tight s dm.
    split => [ | t fst /=]; first by apply/tight_dom; first exact/tight; first exact/dom_restr_subs/dm.
    split; first by move: dm => [t' /= []].
    suff: g|_Q s t by rewrite /= => [[]].
    by apply /tight_val /fst/dom_restr_subs/dm.
  Qed.

  Lemma tight_restr_l (f g: S ->> T) P Q:
    P \is_subset_of Q -> (f|_P) \tightens g -> (f|_Q) \tightens g.
  Proof.
    move => subs tight s [t gst].
    have [ | [t' [Ps fst'] prp]]:= tight s; first by exists t.
    split => [ | t'' [Qs fst'']]; first by exists t'; split; try apply subs.
    by apply prp.
  Qed.

  Lemma tight_restr (f: S ->> T) P Q:
    P \is_subset_of Q -> (f|_Q) \tightens (f|_P).
  Proof. by move => subs; apply /(tight_restr_l subs)/tight_ref. Qed.

  Lemma tight_comp_r R (f: T ->> R) g (g': S ->> T):
    g \tightens g' -> (f \o g) \tightens (f \o g').
  Proof.
    move => gtg' s [r [[t [g'st ftr]] prop]].
    have sfd: s \from dom g' by exists t.
    have [t' gst']:= (gtg' s sfd).1.
    have g'st': g' s t' by apply (gtg' s sfd).2.
    move: (prop t' g'st') => [r' fgsr'].
    split; first exists r'.
    - split => [ | t'' gst'']; first by exists t'.
      by apply prop; apply (gtg' s sfd).2.
    move => r'' [[t'' [gst'' ft''r'']] prop'].
    split => //; by exists t''; split => //; apply (gtg' s sfd).2.
  Qed.

  Lemma tight_exte_dom (f g: S ->> T):
    g \extends f -> f \tightens (g \restricted_to (dom f)).
  Proof.
    move => exte.
    apply split_tight => [s | s]; first by rewrite dom_restr_spec => [[]].
    by rewrite dom_restr_spec => [[sfdf sfdg]] t fst; split; last apply exte.
  Qed.
End tightenings.
Notation "g '\extends' f" := (extends f g) (at level 50): mf_scope.
Notation "f '\is_tightened_by' g" := (tight f g) (at level 2): mf_scope.
Notation "g '\tightens' f" := (tight f g) (at level 2): mf_scope.

Section tight_comp.
  Lemma tight_id_inv S T (f: S ->> T): mf_id \tightens (f\^-1 \o f).
  Proof.
    apply split_tight => [ | s [s' [[t [fst fs't]]] subs]]; first by rewrite F2MF_dom; apply subs_all.
    by move => _ <-; split; first by exists t.
  Qed.

  Arguments tight_id_inv {S} {T} (f).

  Lemma tight_comp_l_codom R S T (f f': T ->> R) (g: S ->> T):
    f \tightens (f' \restricted_to (codom g)) -> (f \o g) \tightens (f' \o g).
  Proof.
    move => ftf' s [r [[t [gst f'tr]] prop]].
    have tfd: t \from dom (f' \restricted_to (codom g)) by exists r; split => //; exists s.
    have [r' ftr']:= (ftf' t tfd).1.
    have f'tr': f' t r' by apply (ftf' t tfd).2.
    split; first exists r'.
    - split => [ | t'' gst'']; first by exists t.
      apply ftf'; have [r'' f't''r'']:= prop t'' gst''.
      by exists r''; split => //; exists s.
    move => r'' [[t'' [gst'' ft''r'']] prop'].
    split => //; exists t''; split => //.
    apply ftf'; have [r''' f't''r'']:= prop t'' gst'' => //.
    by exists r'''; split => //; exists s.
  Qed.
  
  Lemma tight_comp_l R S T (f f': T ->> R) (g: S ->> T):
    f \tightens f' -> (f \o g) \tightens (f' \o g).
  Proof.
    move => tight; apply tight_comp_l_codom.
    by apply /tight_trans; first apply /tight_restr_w.
  Qed.

  Lemma cotot_tight_comp_l R S T (f f': T ->> R) (g: S ->> T):
    g \is_singlevalued -> dom f' \is_subset_of codom g -> (f \o g) \tightens (f' \o g) ->
    f \tightens f'.
  Proof.
    move => sing subs tight.
    apply split_tight => [t [r ftr] | t [r' f'tr'] r ftr].
    - have [ | s gst]:= subs t; first by exists r.
      have sfd: s \from dom (f' \o g) by rewrite sing_rcmp => //; exists r; exists t.
      have [r' [[t' [gst' ft'r']] _]]:= tight_dom tight sfd.
      by rewrite (sing s t t') =>//; exists r'.
    have [ | s gst]:= subs t; first by exists r'.
    have sfd: s \from dom (f' \o g) by rewrite sing_rcmp => //; exists r'; exists t.
    have subs':= tight_val tight sfd.
    have fgsr: (f \o g) s r by rewrite sing_rcmp => //; exists t.
    have [[t' [gst' f't'r]]]:= subs' r fgsr.
    by rewrite (sing s t t').
  Qed.

  Lemma tight_comp R S T (f f': T ->> R) (g g': S ->> T):
    f \tightens f' -> g \tightens g' -> (f \o g) \tightens (f' \o g').
  Proof.
    intros; apply/tight_trans/tight_comp_l; last by apply H.
    apply/tight_trans/tight_comp_r; last by apply H0.
    exact/tight_ref.
  Qed.
  
  Lemma tight_comp_codom R S T (f f': T ->> R) (g g': S ->> T):
    f \tightens (f' \restricted_to (codom g')) -> g \tightens g' -> (f \o g) \tightens (f' \o g').
  Proof.
    move => tight tight'.
    apply/tight_trans; first by apply /tight_comp_l_codom/tight.
    by apply/tight_trans/tight_comp_r; [apply/tight_ref | apply tight'].
  Qed.

  Lemma tight_inv_comp R S T (f: S ->> R) (g: T ->> R) (h: S ->> T):
    (f \o (h\^-1)) \tightens g -> f \tightens (g \o h).
  Proof.
    move => tight; rewrite -(comp_id_r f).
    apply /tight_trans; last apply /tight_comp_r/(tight_id_inv h).
    by rewrite -comp_assoc; apply tight_comp_l.
  Qed.

  Lemma tight_comp_inv R S T (f: S ->> R) (g: T ->> R) (h: S ->> T):
    h \is_surjective_partial_function -> f \tightens (g \o h) <-> (f \o (h\^-1)) \tightens g.
  Proof.
    move => [sing /cotot_spec eq]; split => tight; last exact/tight_inv_comp.
    rewrite (restr_all g) -eq -comp_id_restr -sing_comp_inv // -comp_assoc.
    exact/tight_comp_l.
  Qed.
End tight_comp.

Section choice_functions.
  Context (S T: Type).
  Definition icf S T (g: S -> T) (f: S ->> T) := forall s t, f s t -> f s (g s).
  Local Notation "g '\is_choice_for' f" := (icf g f) (at level 2).

  Definition ipcf S T (g: S -> option T) (f: S ->> T):=
    forall s t, f s t -> exists t', g s = some t' /\ f s t'.

  Local Notation "g '\is_partial_choice_for' f" := (ipcf g f) (at level 2).

  Lemma icf_spec (g: S -> T) f: g \is_choice_for f <->
	                        (F2MF g) \tightens f.
  Proof.
    split => [ icf s [] t fst | tight s t fst].
    - by split => [ | gs eq ]; [exists (g s) | rewrite -eq; apply: (icf s t)].
    have ex: s \from dom f by exists t.
    by apply ((tight s ex).2 (g s)).
  Qed.

  Lemma ipcf_spec (g: S -> option T) f: g \is_partial_choice_for f <->
	                                (PF2MF g) \tightens f.
  Proof.
    split => [ipcf s [t fst] | tight s t fst].
    - by have [t' [/= -> fst']]:= ipcf s t fst; split => [ | _ <-]; first exists t'.
    have [ |[t' /=]]:= tight s; first by exists t.
    by case: (g s) => // _ -> prp; exists t'; split => //; apply prp.
  Qed.

  Global Instance icf_prpr: Proper (@eqfun T S ==> @equiv S T ==> iff) (@icf S T).
  Proof.
    move => f f' fe g g' ge; rewrite !icf_spec ge.
    by have ->: F2MF f =~= F2MF f' by move => s t /=; rewrite (fe s).
  Qed.

  Lemma id_icf_inv (f: S ->> T): id \is_choice_for ((f\^-1) \o f).
  Proof. by move => s s' [[t [fst _]] _]; split; [exists t | exists s]. Qed.

  Lemma sing_tot_F2MF_icf (f: S ->> T) g:
    f \is_singlevalued -> f \is_total -> (g \is_choice_for f <-> F2MF g =~= f).
  Proof.
    move => sing tot.
    split => [icf s t| eq s t fst]; last by by rewrite ((eq s t).2 fst).
    split => [ eq | fst ]; last by rewrite (sing s t (g s)); last by apply (icf s t fst).
    by have [t' fst']:= (tot s); by rewrite -eq; apply (icf s t').
  Qed.

  Lemma tight_icf (g f: S ->> T):
    g \tightens f -> forall h, (h \is_choice_for g -> h \is_choice_for f).
  Proof. by move => tight h icf; apply/icf_spec/tight_trans/icf_spec/icf. Qed.
End choice_functions.
Notation "g '\is_choice_for' f" := (icf g f) (at level 2): mf_scope.
Notation "g '\is_partial_choice_for' f" := (ipcf g f) (at level 2): mf_scope.

Lemma icf_comp R S T g (f: T ->> R) g' (f': S ->> T):
  g \is_choice_for f -> g' \is_choice_for f'
  -> (g \o_f g') \is_choice_for (f \o f').
Proof.
  by move => icf icf'; rewrite icf_spec -F2MF_comp_F2MF; apply/tight_comp; apply/icf_spec.
Qed.

Section products.
  Context (S T S' T': Type).
  Definition fprd_mf S T S' T' (f : S ->> T) (g : S' ->> T') :=
    make_mf (fun s => (f s.1) \x (g s.2)).
  Local Notation "f '**' g" := (fprd_mf f g) (at level 50).

  Global Instance fprd_prpr S T S' T':
    Proper ((@equiv S T) ==> (@equiv S' T') ==> (@equiv (S * S') (T * T'))) (@fprd_mf S T S' T').
  Proof.
    move => f f' eq g g' eq' r t.
      by rewrite /fprd_mf /= eq eq'.
  Qed.
  
  Definition fprd S T S' T' (f: S -> T) (g: S' -> T') := fun p => (f p.1, g p.2).
  Local Notation "f **_f g" := (fprd f g) (at level 50).

  Lemma F2MF_fprd (f: S -> T) (g: S' -> T'): F2MF (f **_f g) =~= (F2MF f) ** (F2MF g).
  Proof. by move => s [t1 t2]; rewrite /fprd/=; split; move => [-> ->]. Qed.

  Definition pfprd S T S' T' (f: S -> option T) (g: S' -> option T'):=
    fun p => match f p.1 with
             | None => None
             |Some fp => match g p.2 with
                         |None => None
                         |Some gp => Some (fp, gp)
                         end
             end.
  Local Notation "f **_p g" := (pfprd f g) (at level 50).

  Lemma PF2MF_fprd (f: S -> option T) (g: S' -> option T'):
    PF2MF (f **_p g) =~= (PF2MF f) ** (PF2MF g).
  Proof.
    move => s [t1 t2]; rewrite /=/pfprd.
    case: (f s.1) => [fs | ]; case: (g s.2) => [gs | ]; try by split; case.
    by split; case => [-> ->].
  Qed.
  
  Definition fprd_p1 (fg: (S * S') ->> (T * T')) :=
    make_mf (fun s t => exists s' p, fg (s,s') p /\ p.1 = t).
  
  Definition fprd_p2 (fg: (S * S') ->> (T * T')) :=
    make_mf (fun s' t' => exists s p, fg (s, s') p /\ p.2 = t').
  
  Lemma fprd_proj1 (f: S ->> T) (g: S' ->> T'):
    (exists s', s' \from dom g) -> fprd_p1 (f ** g) =~= f.
  Proof.
    move => [s' [t' gs't']].
    by split => [[k [p [[/= eq _] eq']]] | ]; [rewrite -eq' | exists s'; exists (s0, t')].
  Qed.
  
  Lemma fprd_proj2 (f: S ->> T) (g: S' ->> T'):
    (exists s, s \from dom f) -> fprd_p2 (f ** g) =~= g.
  Proof.
    move => [s [somet fst]].
    move => s' t.
    by split => [[k [p [[/= _ eq] eq']]] | ]; [rewrite -eq' | exists s; exists (somet, t)].
  Qed.
  
  Lemma fprd_dom R Q R' Q' (f: R ->> Q) (g: R' ->> Q'):
    dom (f ** g) === (dom f) \x (dom g).
  Proof.
    split; last by move => [[s' fs's] [t' ft't]]; exists (s',t').
    by move => [] x [] /= fsx gty; split; [exists x.1| exists x.2].
  Qed.

  Lemma fprd_inv (f: S ->> T) (g: S' ->> T'): (f ** g)\^-1 =~= f\^-1 ** g\^-1.
  Proof. done. Qed.
  
  Lemma fprd_codom (f: S ->> T) (g: S' ->> T'): codom (f ** g) === (codom f) \x (codom g).
  Proof. by rewrite !codom_dom_inv fprd_inv -fprd_dom. Qed.
  
  Lemma fprd_sing (f: S ->> T) (g: S' ->> T'):
    f \is_singlevalued -> g \is_singlevalued -> (f ** g) \is_singlevalued.
  Proof.
    move => fsing gsing [s1 s2] [t1 t2] [t'1 t'2] [fst gst] [fst' gst'].
    by rewrite (fsing s1 t1 t'1) // (gsing s2 t2 t'2).
  Qed.

  Lemma fprd_tot (f: S ->> T) (g: S' ->> T'):
    f \is_total -> g \is_total -> (f ** g) \is_total.
  Proof. by rewrite !tot_spec fprd_dom => -> ->. Qed.

  Lemma tot_fprd (f: S ->> T) (g: S' ->> T') (s: S) (s': S'):
    (f ** g) \is_total -> f \is_total /\ g \is_total.
  Proof.
    move => tot; have [[t t' [fst gs't']] ]:= tot (s, s').
    move/tot_spec: tot; rewrite fprd_dom => eq.
    by rewrite !tot_spec; apply/ (sprd_All_inv _ _ eq); [exists t; apply fst | exists t'; apply gs't'].
  Qed.
  
  Lemma fprd_cotot (f: S ->> T) (g: S' ->> T'):
    f \is_cototal -> g \is_cototal -> (f ** g) \is_cototal.
  Proof. by rewrite !cotot_spec fprd_codom => -> ->. Qed.
  
  Lemma fprd_rcmp R R' (f: S ->> T) (g: S' ->> T') (f': R ->> S) (g': R' ->> S'):
    (f ** g) \o_R (f' ** g') =~= (f \o_R f') ** (g \o_R g').
  Proof.
    by split => [[[r s'] [[f'st g's't] []]] | [[r [f'rs fst]] [s' []]]]; [split; [exists r | exists s'] | exists (r, s')].
  Qed.

  Lemma fprd_comp R R' (f: S ->> T) (g: S' ->> T') (f': R ->> S) (g': R' ->> S'):
    (f ** g) \o (f' ** g') =~= (f \o f') ** (g \o g').
  Proof.
    move => r t.
    split => [[/fprd_rcmp [rcmpf rcmpg]] | [[rcmp subs] [rcmp' subs']]].
    - rewrite fprd_dom => subs; split; split => // s frs.
      + by have [s' [grs g'st]]:= rcmpg; have []//:= subs (s, s').
      by have [s' [grs g'st]]:= rcmpf; have []//:= subs (s', s).
    split; first exact/fprd_rcmp.
    by rewrite fprd_dom => s []; split; [apply subs | apply subs'].
  Qed.

  Lemma fprd_tight (f: S ->> T) (g: S' ->> T') (f': S ->> T) (g': S' ->> T'):
    f \tightens f' -> g \tightens g' -> (f ** g) \tightens (f' ** g').
  Proof.
    move => tight tight'; apply split_tight => [ | s dm t [fst gst]].
    - by rewrite !fprd_dom => s [dm dm']; split; apply/tight_dom; try apply/dm; try apply/dm'.
    by move/fprd_dom: dm => [dm dm']; split; apply/tight_val; try apply /fst; try apply /gst.
  Qed.
End products.
Notation "f '**' g" := (fprd_mf f g) (at level 50): mf_scope.
Notation "f '**_f' g" := (fprd f g) (at level 50): mf_scope.
Notation "f '**_p' g" := (pfprd f g) (at level 50): mf_scope.

Section sums.
  Context (S T S' T': Type).
  (* A modification of the following construction is used to define the sum of represented spaces. *)
  Definition mf_fsum S T S' T' (f : S ->> T) (g : S' ->> T') :=
    make_mf (fun c x => match c with
                        | inl a => match x with
                                   | inl y => f a y
                                   | inr z => False
                                   end
                        | inr b => match x with
                                   | inl y => False
                                   | inr z => g b z
                                   end
                        end).
  Local Notation "f +s+ g" := (mf_fsum f g) (at level 50).
  
  Definition fsum S T S' T' (f: S -> T) (g: S' -> T') :=
	fun ss' => match ss' with
		| inl s => inl (f s)
		| inr s' => inr (g s')
	end.
  Local Notation "f +s+_f g" := (fsum f g) (at level 50).

  Lemma	F2MF_fsum (f: S -> T) (g: S' -> T'):
    F2MF (f +s+_f g) =~= (F2MF f) +s+ (F2MF g).
  Proof.
    split; rewrite /F2MF; first by move <-; case s => /=.
    by case: s => /=; case: s0 => //= s t ->.
  Qed.

  Definition pfsum S T S' T' (f: S -> option T) (g: S' -> option T') :=
    fun ss' => match ss' with
               | inl s => match (f s) with
                          |None => None
                          | some fs => Some (inl fs)
                          end
               | inr s' => match (g s') with
                           | None => None
                           | some gs' => Some (inr gs')
                           end
               end.
  Local Notation "f +s+_p g" := (pfsum f g) (at level 50).
  
  Lemma PF2MF_fsum (f: S -> option T) (g: S' -> option T'):
    PF2MF (f +s+_p g) =~= (PF2MF f) +s+ (PF2MF g).
  Proof.
    move => s t; rewrite /pfsum /=.
    case: s => [s | s'].
    - case: (f s) => [fs | ]; last by split => //; case: t.
      by case: t => [t | t'] //; split => [[<-] | <-].
    case: (g s') => [gs' | ]; last by split => //; case: t.
    by case: t => [t | t'] //; split => [[<-] | <-].
  Qed.
  
  Lemma fsum_cotot (f: S ->> T) (g: S' ->> T'):
    f \is_cototal -> g \is_cototal -> (f +s+ g) \is_cototal.
  Proof.
   by move => sur sur' [t | t']; [have [s]:= sur t; exists (inl s) | have [s']:= sur' t'; exists (inr s')].
  Qed.

  Lemma fsum_sing (f: S ->> T) (g: S' ->> T'):
    f \is_singlevalued -> g \is_singlevalued -> (f +s+ g) \is_singlevalued.
  Proof.
    move => fsing gsing [s [t [r /=fst fsr | r'] | t' [r | r']]| s' [t [r | r'] | t' [r | r' /= gs't' gs'r']]] //.
    - by rewrite (fsing s t r).
    by rewrite (gsing s' t' r').
  Qed.
End sums.
Notation "f '+s+' g" := (mf_fsum f g) (at level 50): mf_scope.
Notation "f '+s+_f' g" := (fsum f g) (at level 50): mf_scope.
Notation "f '+s+_p' g" := (pfsum f g) (at level 50): mf_scope.

Section lists.
  Fixpoint mf_map_prp S T (f: S ->> T) L K :=  
    match L with
    | nil => match K with
             | nil => True
             | cons t K' => False
             end
    |cons s L' => match K with
                  | nil => False
                  | cons t K' => f s t /\ mf_map_prp f L' K'
                  end
    end.
  
  Definition mf_map S T (f: S ->> T) := make_mf (mf_map_prp f).
  
  Lemma F2MF_map S T (f: S ->> T): mf_map (F2MF f) =~= F2MF (map f).
  Proof.
    elim => [[] | s L ih [ | t K]] //=.
    split => [[-> prp] | [->]]; first by f_equal; exact/ih/prp.
    by split; last apply/ih.
  Qed.
  
  Fixpoint pmap S T (f: S -> option T) L := match L with
                                            | nil => Some nil
                                            | s :: L' => match pmap f L' with
                                                         | None => None
                                                         | Some K => match f s with
                                                                     | None => None
                                                                     | Some t => some (t :: K)
                                                                     end
                                                         end
                                            end.
  
  Lemma map_pmap S T (f: S -> T): Some \o_f (map f) =1 pmap (Some \o_f f).
  Proof.
    elim => // s L /= ih.
    case E: (pmap (Some \o_f f) L) => [K | ]; first by move: ih; rewrite E; case => ->.
    by move: E; rewrite -ih /=.
  Qed.

  Lemma PF2MF_map S T (f: S -> option T): mf_map (PF2MF f) =~= PF2MF (pmap f).
  Proof.
    elim => [[] | s L ih [/= | t K]]//; first by case E: (pmap f L) => [K | ]//; case E': (f s).
    split => [/=[] | /=].
    - by case: (f s) => // _ -> prp; have /= := (ih K).1 prp; case: (pmap f L) => // _ -> .
    case E: (pmap f L) => [K' | ]//.
    by case E': (f s) => [fs | ]// [->  <-]; split; last by apply/ih => /=; rewrite E.
  Qed.
  
  Lemma map_sur S T (f: S ->> T): f \is_cototal -> (mf_map f) \is_cototal.
  Proof.
    move => sur.
    elim => [ | t K [L eq]]; first by exists nil.
    by have [s val]:= sur t; exists (s :: L).
  Qed.
End lists.

Section functions.
  Context (S T S' T': Type).
    
  Definition cnst S T (c: T) := (fun (_: S) => c).
  
  Definition mf_cnst S T (c: T) := F2MF (@cnst S T c).
  Arguments mf_cnst {S} {T}.
  
  Lemma cnst_rcmp R (c: T) (f: R ->> S): (mf_cnst c) \o_R f =~= (mf_cnst c)|_(dom f).
  Proof. by move => r t; split => [[s [fst <-]] | [[s] frs <-]]; first split; try by exists s. Qed.
  
  Lemma cnst_comp R (c: T) (f: R ->> S): (mf_cnst c) \o f =~= (mf_cnst c)|_(dom f).
  Proof.
    move => r t.
    split; first by rewrite /=/cnst; move => [[s [frs /=->]] _]; split => //; exists s.
    move => [[s fsr <-]]; split; first by exists s.
    by move => a b; exists c.
  Qed.

  Lemma fprd_id: @mf_id S ** @mf_id S' =~= @mf_id (S * S').
  Proof. by move => [s s'] [t t'] /=;split; by move => [-> ->]. Qed.
  
  Definition mf_fst S T := (F2MF (@fst S T)).
  Arguments mf_fst {S} {T}.
  
  Lemma fst_unit_inj: (forall t t' : T, t = t') -> injective (@fst S T).
  Proof. by move => eq s t eq'; exact/injective_projections. Qed.
  
  Lemma fprd_fst R R' Q Q' (f: R ->> Q) (g: R' ->> Q') : mf_fst \o (f ** g) =~= (f \o mf_fst)|_(All \x dom g).
  Proof.
    move => s t; rewrite comp_F2MF.
    split => [[[[t' t''] [[/= fs1t' gs2t'']]] /=<- _] | [[_ [t' gs2t']] fst]].
    split => //; split => //; by exists t''.
    rewrite comp_rcmp; last exact /F2MF_tot.
    by exists (t, t').
  Qed.

  Definition mf_snd S T := (F2MF (@snd S T)).
  Arguments mf_snd {S} {T}.
  
  Lemma fprd_snd R R' Q Q' (f: R ->> Q) (g: R' ->> Q') : mf_snd \o (f ** g) =~= (g \o mf_snd)|_(dom f \x All).
  Proof.
    move => s t; rewrite comp_F2MF.
    split => [[[[t' t''] [[/= fs1t' gs2t'']]] /=<- _] | [[[t' gs2t'] _] fst]].
    - by split => //; split => //; exists t'.
    rewrite comp_rcmp; last exact /F2MF_tot.
    by exists (t', t).
  Qed.

  Definition diag S := fun (d: S) => (d,d).
  Arguments diag {S}.
  Definition mf_diag S := F2MF (@diag S).
  Arguments mf_diag {S}.

  Lemma snd_diag_id: mf_snd \o @mf_diag S =~= mf_id.
  Proof. by rewrite F2MF_comp_F2MF. Qed.
  
  Lemma fst_diag_id: mf_fst \o @mf_diag S =~= mf_id.
  Proof. by rewrite F2MF_comp_F2MF. Qed.
  
  Definition prd_mf R S T (f: R ->> S) (g: R ->> T):= make_mf (fun r st =>
                                                                 f r st.1 /\ g r st.2).
  
  Lemma prd_spec R (f: R ->> S) (g: R ->> T):
    prd_mf f g =~= (f ** g) \o mf_diag.
  Proof. by rewrite comp_F2MF => r st /=. Qed.
  
  Definition prd_p R S T (f: R -> option S) (g: R -> option T) r :=
    match f r with
    | None => None
    | Some fr => match g r with
                 | None => None
                 | Some gr => Some (fr, gr)
                 end
    end.
  
  Lemma PF2MF_comp_F2MF R R' Q (f: R -> R') (g: R' -> option Q):
    (PF2MF g) \o (F2MF f) =~= PF2MF (g \o_f f).
  Proof.
    rewrite F2MF_PF2MF PF2MF_comp_PF2MF -PF2MF_eq => r /=.
    by rewrite /pcomp/obind /=.
  Qed.
  
  Lemma prd_p_spec R (f: R -> option S) (g: R -> option T):
    PF2MF (prd_p f g) =~= prd_mf (PF2MF f) (PF2MF g).
  Proof.
    by rewrite prd_spec -PF2MF_fprd PF2MF_comp_F2MF -PF2MF_eq.
  Qed.
  
  Definition prd R S T (f: R -> S) (g: R -> T) r:= (f r, g r).

  Lemma prd_f_spec R (f: R -> S) (g: R -> T):
    F2MF (prd f g) =~= prd_mf (F2MF f) (F2MF g).
  Proof.
      by rewrite prd_spec -F2MF_fprd F2MF_comp_F2MF -F2MF_eq.
  Qed.
  
  Lemma fst_prd R (f: R ->> S) (g: R ->> T):
    mf_fst \o (prd_mf f g) =~= f|_(dom g).
  Proof.
    rewrite prd_spec -comp_assoc fprd_fst [_ \o mf_fst]comp_F2MF comp_F2MF => s t /=.
    by split => [[[]] | []].
  Qed.
  
  Lemma fst_prd_tot R (f: R ->> S) (g: R ->> T):
    g \is_total -> mf_fst \o (prd_mf f g) =~= f.
  Proof.  
    by move => /tot_spec tot; rewrite fst_prd tot -restr_all.
  Qed.
  
  Lemma snd_prd R (f: R ->> S) (g: R ->> T):
    mf_snd \o (prd_mf f g) =~= g|_(dom f).
  Proof.
    rewrite prd_spec -comp_assoc fprd_snd [_ \o mf_snd]comp_F2MF comp_F2MF => s t /=.
    by split => [[[]] | []].
  Qed.
  
  Lemma snd_prd_tot R (f: R ->> S) (g: R ->> T):
    f \is_total -> mf_snd \o (prd_mf f g) =~= g.
  Proof.
    by move => /tot_spec tot; rewrite snd_prd tot -restr_all.
  Qed.
  
  Lemma tight_fprd_diag (f: S ->> T): (mf_diag \o f) \tightens ((f ** f) \o mf_diag).
  Proof.
    apply split_tight => [ | s sfd [_ _] [[t] [fst [<- <-]] _]]; last by rewrite comp_F2MF.
    rewrite comp_F2MF => s [[t t'] [fst fst']].
    rewrite comp_rcmp; last exact /F2MF_tot.
    by exists (t, t); exists t; split => //.
  Qed.
  
  Lemma fprd_diag (f: S ->> T): f \is_singlevalued -> (f ** f) \o mf_diag =~= mf_diag \o f.
  Proof.
    rewrite comp_F2MF comp_rcmp; last exact /F2MF_tot.
    move => sing s [t1 t2].
    split => [[fst1 fst2] | ]; last by move => [t] [fst [<- <-]].
    by exists t1; split => //; rewrite (sing s t2 t1).
  Qed.
  
  Lemma fprd_diag_sing (f: S ->> T): ((f ** f) \o mf_diag) \tightens (mf_diag \o f) -> f \is_singlevalued.
  Proof.
    move => tight.
    have: ((f ** f) \o mf_diag) =~= (mf_diag \o f) by apply/tight_equiv/tight_fprd_diag.
    rewrite comp_F2MF comp_rcmp; last exact /F2MF_tot.
    by move => eq s t t'; intros; have /=[ | t'' [fst'' [<- <-]]]//:= (eq s (t, t')).1.
  Qed.

  Definition lcry_f S T R (f: S * T -> R) s t := f (s, t).
  
  Definition lcry S T R (f: S * T ->> R) s :=
    make_mf (fun t fst => f (s,t) fst).
  
  Lemma F2MF_lcry R (f: S * T -> R) s:
    F2MF (lcry_f f s) =~= lcry (F2MF f) s.
  Proof. done. Qed.
  
  Definition lcry_p S T R (f: S * T -> option R) s t := f (s, t).
  
  Lemma PF2MF_lcry R (f: S * T -> option R) s:
    PF2MF (lcry_p f s) =~= lcry (PF2MF f) s.
  Proof. done. Qed.

  Definition rcry_f S T R (f: S * T -> R) t s := f (s, t).
  
  Definition rcry S T R (f: S * T ->> R) t := make_mf (fun s fst => f (s, t) fst).

  Lemma F2MF_rcry R (f: S * T -> R) t:
    F2MF (rcry_f f t) =~= rcry (F2MF f) t.
  Proof. done. Qed.

  Definition rcry_p S T R (f: S * T -> option R) t s := f (s, t).
  
  Lemma PF2MF_rcry R (f: S * T -> option R) t:
    PF2MF (rcry_p f t) =~= rcry (PF2MF f) t.
  Proof. done. Qed.

  Definition uncurry R S T (E: R * S -> T) r:= (fun s => E (r,s)).
  Definition mf_uncurry R S T (E: R * S ->> T) r := make_mf (fun s t => E (r, s) t).
  
  Lemma F2MF_ncry R (E: R * S -> T) r:
    F2MF (uncurry E r) =~= mf_uncurry (F2MF E) r.
  Proof. done. Qed.
  
  Lemma mf_ncry_prp R (E: R * S ->> T) r:
    mf_uncurry E r =~= E \o ((mf_cnst r) ** mf_id) \o mf_diag.
  Proof. by rewrite -F2MF_fprd comp_assoc !comp_F2MF => s t/=. Qed.
End functions.
Arguments cnst {S} {T}.
Arguments mf_cnst {S} {T}.
Arguments diag {S}.
Arguments mf_diag {S}.
Arguments mf_fst {S} {T}.
Arguments mf_snd {S} {T}.
Arguments mf_empty {S} {T}.
Arguments empty {S}.