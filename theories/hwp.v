From stdpp Require Import gmap.
From iris.bi Require Import interface derived_laws notation.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.
From l3 Require Import lang heapprop.

Local Definition heapProp_hwp_def (e : expr) (Q : val → heapProp) : heapProp :=
  {| heapProp_holds σ := 
      ∀ σf, σ ##ₘ σf → ∃ v σ', (Q v) σ' ∧
        rtc erased_step ([e], {| heap := σ ∪ σf |})
                        ([Val v], {| heap := σ' ∪ σf |}) |}.
Local Definition heapProp_hwp_aux : seal (@heapProp_hwp_def). Proof. by eexists. Qed.
Definition heapProp_hwp := unseal heapProp_hwp_aux.
Local Definition heapProp_hwp_unseal :
  @heapProp_hwp = @heapProp_hwp_def := seal_eq heapProp_hwp_aux.

(* I don't want to use the Wp or Twp instance from
   https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/bi/weakestpre.v
   since it has extra junk in there, but I want to use similar notation. *)

Notation "'WP' e {{ Φ }}" := (heapProp_hwp e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

Notation "'WP' e {{ v , Q }}" := (heapProp_hwp e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern,
   format "'[hv' 'WP'  e  '/' {{  '[' v ,  '/' Q  ']' }} ']'") : bi_scope.

(* Might want more notation like (Texan?) triples too... *)

(* This tells us that WP implies leak freedom when the postcondition
   is intuitionistic, and externalizes *)
Lemma l3_adequacy_emp e φ : 
  (emp ⊢ WP e {{ v, □ ⌜φ v⌝ }}) →
  ∃ v, φ v ∧ rtc erased_step ([e], {| heap := ∅ |})
                              ([Val v], {| heap := ∅ |}).
Proof.
  rewrite /bi_entails /bi_emp /=; intros [Hwp].
  assert ((WP e {{ v, □ ⌜φ v⌝ }})%I ∅). { apply Hwp; by unseal. }
  rewrite heapProp_hwp_unseal in H; destruct (H ∅) as [v' [σ' [Hholds Hstep]]].
  { apply map_disjoint_empty_l. }
  exists v'. 
  assert (σ' = ∅). { admit. } split. 
  - admit. 
  - subst; by repeat rewrite right_id_L in Hstep.
Admitted.
