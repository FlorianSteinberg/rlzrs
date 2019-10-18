From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_ntrvw dict.
Import Morphisms FunctionalExtensionality ProofIrrelevance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
  
Section data_spaces.
  Context (data_type: Type) (raw: data_type -> Type).
  Coercion raw: data_type >-> Sortclass.
  
  Structure encoding_of X :=
    {
      data: data_type;
      delta:> Dictionary data X;
    }.

  Notation "d \code_for x \wrt delta" := ((delta: encoding_of _) d x) (at level 30).

  Structure data_space :=
    {
      space :> Type;
      encoding: encoding_of space;
    }.

  Notation "d \codes x" := (d \code_for x \wrt (encoding _)) (at level 30).

  Coercion encoding: data_space >-> encoding_of.

  Definition codes_of (A: data_space) (x: A) := {d | d \codes x}.

  Definition id_enc (data: data_type):= id_dictionary data.

  Canonical data_encoding (data: data_type):= Build_encoding_of (id_enc data).

  Canonical space_of_data (data: data_type) := Build_data_space (@data_encoding data).
  
  Section pairs.
    Structure pairs_data :=
      {
        pair_data: data_type -> data_type -> data_type;
        unpair: forall data data', (pair_data data data') -> (data * data');
        surjective_pairing: forall data data', (@unpair data data') \is_surjective;
      }.
    Context (pairs: pairs_data).

    Section product_encoding.
      Definition data_pairs_encoding (data data': data_type): encoding_of (data * data').
        exists (pair_data pairs data data').
        exists (F2MF (@unpair pairs data data')); first exact/surjective_pairing.
        exact/F2MF_sing.
      Defined.

      Context X X' (delta: encoding_of X) (delta': encoding_of X').

      Canonical product_encoding:=
        Build_encoding_of (combine_dictionaries
                             (data_pairs_encoding (data delta) (data delta'))
                             (product_dictionary delta delta')).
    End product_encoding.

    Lemma dpe_spec data data': data_pairs_encoding data data' =~= product_encoding _ _.
    Proof. by move => q [a1 a2]; split => [<- | [[s1 s2] [/= -> [-> ->]]]]//; exists (unpair q). Qed.
                                                                
    Section product_space.
      Context (X X': data_space).

      Canonical product_space :=
        Build_data_space (product_encoding (encoding X) (encoding X')).
    End product_space.      
    Local Notation "A \*_ds B" := (product_space A B) (at level 30).

    Lemma prod_code_spec (A B: data_space) d (x: A) (y: B):
      d \codes (x,y) <-> (unpair d).1 \codes x /\ (unpair d).2 \codes y.
    Proof.
      split => [[p [<-]] | [dnx dny]]//.
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

      Section function_encoding.       
        Context X X' (delta: encoding_of X) (delta': encoding_of X'). 

        Definition solution_wrt f (d: function_data universal _ _) :=
          f \realized_by run d \wrt delta \and delta'.

        Definition realizer_wrt d f:= solution_wrt (F2MF f) d.

        Definition associate (d: function_data universal (data delta) (data delta')) f :=
          (F2MF f) \realized_by run d \wrt delta \and delta'.
        
        Canonical function_encoding: encoding_of (codom (make_mf associate)). 
          exists (function_data universal (data delta) (data delta')).
          exists (make_mf (fun d f => associate d (sval f))) => [[f [d ass]] | ]; first by exists d.
          move => d [f P]  [g Q]/= ass ass'.
          suff eq: f = g.
          - move: Q ass'; rewrite -eq => Q ass'.
            by f_equal; apply/proof_irrelevance.
          by apply/functional_extensionality => x; rewrite (rlzr_F2MF_eq ass ass').
        Defined.
      End function_encoding.

      Section function_space.
        Context (X X': data_space).

        Canonical function_space:= Build_data_space (function_encoding (encoding X) (encoding X')).

        Definition solution := @solution_wrt _ _ (encoding X) (encoding X').

        Definition solutions f := make_subset (solution f).

        Definition solvable f:= exists d, solution f d.

        Definition realizer f := solution (F2MF f).
      End function_space.
      Notation "A c-> B" := (function_space A B) (at level 30).

      Definition evaluation A B (fx: A c-> B \*_ds A):= sval fx.1 fx.2.
      
      Lemma eval_slvbl A B: solutions (F2MF (@evaluation A B)).
      Proof.
        have [E E_spec]:= eval universal (data A) (data B).
        exists E => d [f x] [[cf cx [/=eq [/= cfcf cxcx]]]] [fx val].
        have [ | [nfx/= nfxnfx] dm/=]:= cfcf cx x cxcx; first by exists fx.
        split => [ | nfx' /E_spec nfxnfx']; first by exists nfx; apply/E_spec; rewrite eq.
        by apply/dm; rewrite eq in nfxnfx'.
      Qed.
      
      Definition ms_eval A B : (A c-> B) \*_ds A c-> B.
        exists (@evaluation A B).
        rewrite /=.
        have [d ass]:= eval_slvbl A B.
        by exists d.
      Defined.

      Lemma cnstr_slvbl (A B: data_space) (f: A c-> B): codes_of f = solutions (F2MF (sval f)).
      Proof. done. Qed.
      
      Lemma eval_cnstr (A B: data_space): codes_of (ms_eval A B).
      Proof. exact/eval_slvbl. Qed.

      Lemma slvbl_rlzr (A B: data_space) (F: data A ->> data B) (f: A ->> B):
        solvable F -> f \realized_by F \wrt (encoding A) \and (encoding B) -> solvable f.
      Proof.
        case => d ass rlzr.
        exists d => phi x phinx xfd.
        have phifd: phi \from dom F by apply/rlzr_dom/xfd/phinx/rlzr.
        split =>[ | Fphi val]; first by case: (ass phi phi).
        have [ | | phifd' prp]//:= ass phi phi.
        have [stf [/=val' -> ]]:= prp Fphi val.
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
        by have [_ [/= <- ->]]:= prp Fd val.
      Qed.

      Lemma snd_slvbl (A B: data_space):
        solvable (F2MF (@snd (data A) (data B))) -> solvable (F2MF (@snd A B)).
      Proof.
        case => d ass.
        exists d => e [x y] /prod_code_spec [enx eny] _.
        have [ | | efd prp]:= ass e (unpair e); first exact/prod_code_spec; first exact/F2MF_dom.
        split => // Fd val; exists y; split => //.
        by have [_ [/= <- ->]]:= prp Fd val.
      Qed.
    End functions.
  End pairs.
End data_spaces.
Notation "A \*_ds B" := (product_space A B) (at level 30): ds_scope.
Delimit Scope ds_scope with ds.
