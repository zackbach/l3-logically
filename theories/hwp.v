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

