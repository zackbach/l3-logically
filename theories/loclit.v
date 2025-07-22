(* FROM: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/locations.v *)

From stdpp Require Import countable numbers gmap.

(* HeapLang has the carrier as integers Z, but I'm not sure why.
   Maybe I will have to switch this back later. *)
Record loclit := LocLit { loc_car : nat }.

Module LocLit.

  Add Printing Constructor loclit.

  Lemma eq_spec l1 l2 : l1 = l2 ↔ loc_car l1 = loc_car l2.
  Proof. destruct l1, l2; naive_solver. Qed.

  Global Instance loclit_eq_decision : EqDecision loclit.
  Proof. solve_decision. Defined.

  Global Instance loclit_inhabited : Inhabited loclit := populate {|loc_car := 0 |}.

  (* Must be Countable to use as keys of a gmap *)
  Global Instance loc_countable : Countable loclit.
  Proof. by apply (inj_countable' loc_car LocLit); intros []. Defined.

  Global Program Instance loclit_infinite : Infinite loclit :=
    inj_infinite (λ p, {| loc_car := p |}) (λ l, Some (loc_car l)) _.
  Next Obligation. done. Qed.

  Definition fresh_locs (ls : gset loclit) : loclit :=
    {| loc_car := set_fold (λ k r, (1 + loc_car k) `max` r) 1 ls |}.

  (* In HeapLang, they have offsets and prove a stronger freshness condition *)

  Lemma fresh_locs_fresh ls : fresh_locs ls ∉ ls.
  Proof.
    cut (∀ l, l ∈ ls → loc_car l < loc_car (fresh_locs ls)).
    { intros help Hf%help. simpl in *. lia. }
    apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → loc_car l < r));
      set_solver by eauto with lia.
  Qed.

  Global Opaque fresh_locs.

End LocLit.
