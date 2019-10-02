From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_ntrvw dict.
Import Morphisms FunctionalExtensionality ProofIrrelevance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section data_spaces.
  Context (data_type: Type) (raw: data_type -> Type).
  Coercion raw: data_type >-> Sortclass.
    
  Structure data_space :=
    {
      space :> Type;
      data: data_type;
      encoding: data ->> space;
      surjective: encoding \is_cototal;
      deterministic: encoding \is_singlevalued;
    }.

  Notation "d \codes x" := (x \from encoding _ d) (at level 30).

  Definition constructible (A: data_space) (x: A) := {d: data A | d \codes x}.

  Canonical ms_data (data: data_type):= Build_data_space (@id_sur data) (@id_sing data).
    
    Global Instance ms2dic (A: data_space): Dictionary (encoding A).
      by split; [apply/surjective | apply/deterministic].
    Defined.

  Section pairs.
    Structure pairs_data :=
      {
        pair_data: data_type -> data_type -> data_type;
        unpair: forall data data', (pair_data data data') -> (data * data');
        surjective_pairing: forall data data', (@unpair data data') \is_surjective;
      }.
    Context (pairs: pairs_data).
            
    Canonical product_data_space (A: data_space) (B: data_space): data_space.
    exists (A * B)%type
           (pair_data pairs (data A) (data B))
           ((encoding A) ** (encoding B) \o (F2MF (@unpair pairs (data A) (data B)))).
    - apply comp_cotot; first by apply F2MF_sing.
      + by apply fprd_cotot; by apply surjective.
      by apply surjective_pairing.
    apply comp_sing; last by apply F2MF_sing.
    by apply fprd_sing; apply deterministic.
    Defined.

    Local Notation "A \*_ds B" := (product_data_space A B) (at level 30).
  
    Lemma prod_code_spec (A B: data_space) d (x: A) (y: B):
      d \codes (x,y) <-> (unpair d).1 \codes x /\ (unpair d).2 \codes y.
    Proof.
      split => [[[p [<- [/= dnx dny]] ]] | [dnx dny]] //.
      split => [ | _ <- /=]; last by exists (x, y).
      by exists ((unpair d).1, (unpair d).2); split; first exact/injective_projections.
    Qed.
  
    Section functions.    
      Structure functions_data:=
        {
          function_data: data_type -> data_type -> data_type;
          run: forall data data', function_data data data' -> data ->> data';
          eval: forall data data',
              {E: function_data (pair_data pairs (function_data data data') data) data' |
               forall d, run E d === run (unpair d).1 (unpair d).2};
        }.

      Definition trivial_universal (some_data: data_type) (nil: some_data): functions_data.
        exists (fun d d' => some_data) (fun d d' d'' => mf_empty).
        move => d d'.
        exists nil => d'' //.
      Defined.
      
      Context (universal: functions_data).
      Definition associate (D D': data_type) A A' (conv: D ->> A) (conv': D' ->> A')
                 (d: function_data universal D D') f :=
        f \realized_by run d \wrt conv \and conv'.
      
      Definition solvable (A B: data_space) (f: A ->> B):=
        {d: function_data universal (data A) (data B) | associate (encoding A) (encoding B) d f}.
      
      Definition function_encoding (D D': data_type) A A' (conv: D ->> A) (conv': D' ->> A') :=
        make_mf (fun d (f: {f: A -> A' | exists d, associate conv conv' d (F2MF f)}) =>
                   associate conv conv' d (F2MF (sval f))).
      
      Lemma funenc_sur (D D': data_type) A A' (conv: D ->> A) (conv': D' ->> A'):
        (function_encoding conv conv') \is_cototal.
      Proof. by move => [f [/=d ass]]; exists d. Qed.
      
      Lemma funenc_sing (A B: data_space):
        (function_encoding (encoding A) (encoding B)) \is_singlevalued.
      Proof.
        move => d [/=f P] [/= g Q] ass ass'.
        have eq: f = g by apply/functional_extensionality/rlzr_F2MF_eq/ass'/ass.
        move: Q ass'; rewrite -eq => Q ass'.
        by f_equal; apply/proof_irrelevance.
      Qed.
    
      Canonical functions (A B: data_space): data_space.
      exists (make_subset (fun (f: A -> B) =>
                             exists d, associate (encoding A) (encoding B) d (F2MF f)))
             (function_data universal (data A) (data B))
             (function_encoding (encoding A) (encoding B)).
      - exact/funenc_sur.
        exact/funenc_sing.
      Defined.  

      Notation "A c-> B" := (functions A B) (at level 30).
      
      Definition evaluation A B (fx: A c-> B \*_ds A):= sval fx.1 fx.2.
      
      Lemma eval_slvbl A B: solvable (F2MF (@evaluation A B)).
      Proof.
        have [E E_spec]:= eval universal (data A) (data B).
        exists E => d [f x] [[[nf nx [/=eq [/=nfnf nxnx] subs]]]] [fx val].
        have [ | [nfx/= nfxnfx] dm/=]:= nfnf nx x nxnx; first by exists fx.
        split => [ | nfx' /E_spec nfxnfx']; first by exists nfx; apply/E_spec; rewrite eq.
        by apply/dm; rewrite eq in nfxnfx'.
      Qed.
      
      Definition ms_eval A B : (A c-> B) \*_ds A c-> B.
        exists (@evaluation A B).
        rewrite /=.
        have [d ass]:= eval_slvbl A B.
        by exists d.
      Defined.

      Lemma cnstr_slvbl (A B: data_space) (f: A c-> B):
        constructible f = solvable (F2MF (sval f)).
      Proof. done. Qed.
      
      Lemma eval_cnstr (A B: data_space): constructible (ms_eval A B).
      Proof. exact/eval_slvbl. Qed.

      Lemma slvbl_rlzr (A B: data_space) (F: data A ->> data B) (f: A ->> B):
        solvable F -> f \realized_by F \wrt (encoding A) \and (encoding B) -> solvable f.
      Proof.
        case => d ass rlzr.
        exists d => phi x phinx xfd.
        have phifd: phi \from dom F by apply/rlzr_dom/xfd/phinx/rlzr.
        split =>[ | Fphi val]; first by case: (ass phi phi).
        have [ | | phifd' prp]//:= ass phi phi.
        have [_ [/=<- val']]:= prp Fphi val.
        have [_ prp']:= rlzr phi x phinx xfd.
        exact/prp'.
      Qed.        

      Lemma id_slvbl (A: data_space):
        solvable (@mf_id (data A)) -> solvable (@mf_id A).
      Proof. by move => slvbl; apply/slvbl_rlzr/id_rlzr. Qed.
      
      Lemma fst_slvbl (A B: data_space):
        solvable (F2MF (@fst (data A) (data B))) -> solvable (F2MF (@fst A B)).
      Proof.
        case => d ass.
        exists d => e [x y] /prod_code_spec [enx eny] _.
        have [ | | efd prp]:= ass e (unpair e); first exact/prod_code_spec; first exact/F2MF_dom.
        split => // Fd val; exists x; split => //.
        by have [_ [/= <- <-]]:= prp Fd val.
      Qed.

      Lemma snd_slvbl (A B: data_space):
        solvable (F2MF (@snd (data A) (data B))) -> solvable (F2MF (@snd A B)).
      Proof.
        case => d ass.
        exists d => e [x y] /prod_code_spec [enx eny] _.
        have [ | | efd prp]:= ass e (unpair e); first exact/prod_code_spec; first exact/F2MF_dom.
        split => // Fd val; exists y; split => //.
        by have [_ [/= <- <-]]:= prp Fd val.
      Qed.
    End functions.
  End pairs.
End data_spaces.
Notation "A \*_ds B" := (product_data_space A B) (at level 30): ds_scope.
Delimit Scope ds_scope with ds.

Module modest_sets.
  Structure data_structure:=
  {
    data_types: Type;
    raw: data_types -> Type;
    pairs: pairs_data raw;
    functions: functions_data pairs;
  }.

  Definition modest_set (data: data_structure) := data_space (@raw data).
End modest_sets.