From stdpp Require Export binders strings.
From l3 Require Export loclit.
From Autosubst Require Export Autosubst.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export language ectx_language ectxi_language.

Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

(* This is structured such that it is possible to instantiate Iris using this
   language (even though our wp might be specialized to just this language) *)
(* The structure of this file follows HeapLang closely:
   https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/lang.v *)

Module l3_lang.

(* Step 1: syntax of expressions and values *)

(* https://www.ccs.neu.edu/home/amal/papers/linloc-fi07.pdf *)
(* See Section 3.1 *)

Inductive loc :=
  (* Using Autosubset and DeBrujin indices for location variables η *)
  | LocVar (ρ : var)
  | LocConst (l : loclit)
.

(* TODO: better notation? *)
Inductive expr :=
  (* Lets us include values directly, even with some redundancy.
     Expression versions of values step to Val, just like in HeapLang *)
  | Val (v : val)
  (* HeapLang does not duplicate literals but does duplicate things
     like Lam, which need to be an expr in order to be substituted into.
     Pair also needs to be an expr, since the value form is different.
     The "expr" versions of `val`s will step to the corresponding value.
     *)
  (* | Unit : expr *)
  | LetUnit (e1 e2 : expr)
  | Pair (e1 e2 : expr)
  | LetPair (x1 x2 : binder) (e1 e2 : expr)
  (* Using stdpp binders for program variables x *)
  | Var (x : binder)
  | Lam (x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* | Bang (v : val) *)
  | LetBang (x : binder) (e1 e2 : expr)
  | Dup (e : expr)
  | Drp (e : expr)
  (* | Ptr (l : loclit) *)
  (* | Cap : expr *)
  | New (e : expr)
  | Free (e : expr)
  | Swap (e1 e2 e3 : expr)
  (* Λη.e *)
  | LocLam (e : {bind loc in expr})
  | LocApp (e : expr) (η : loc)
  | LocPack (η : loc) (e : expr)
  (* let ⌜ρ, x⌝ = e1 in e2 *)
  | LocUnpack (x : binder) (e1 : expr) (e2 : {bind loc in expr})
with val :=
  | UnitV : val
  | PairV (v1 v2 : val)
  (* unlike L3, x is not a value *)
  | LamV (x : binder) (e : expr)
  | BangV (v : val)
  | PtrV (l : loclit)
  | CapV : val
  | LocLamV (e : {bind loc in expr})
  | LocPackV (η : loc) (v : val)
.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

(* Step 2: value and expr conversion functions *)

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.


(* The following lemmas are for "Equality and other typeclass stuff" *)
(* The bodies of these lemmas are from HeapLang, mostly *)
(* Not sure why these are needed but I bet they will come up... *)

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

(* in case we need these: *)
(* Global Instance val_inhabited : Inhabited val := populate UnitV. *)
(* Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant). *)

(* May need EqDecision instances for expr and val *)

(* Step 3: define small-step base reductions *)
(* this will involve defining your machine configuration,
   as well as substitution *)

(* SimpLang suggests that we wrap this, so I am! *)
(* If more lemmas are needed, I should move it to a different file *)
Record store : Type := {
  heap: gmap loclit val;
}.

(** the language interface needs these things to be inhabited, I believe *)
Global Instance store_inhabited : Inhabited store :=
  populate {| heap := inhabitant; |}.

Definition state_upd_heap (f : gmap loclit val → gmap loclit val) (σ : store) : store :=
  {| heap := f σ.(heap) |}.
Global Arguments state_upd_heap _ !_ /.

(* We need to talk about substitution in our semantics.
   We follow HeapLang: substitution is _not_ capture-avoiding;
   we do not substitute into values;
   we work with appropriately closed things. *)

Fixpoint subst_val (x : string) (v : val) (e : expr) :=
  match e with
  (* values are always closed *)
  | Val _ => e
  | LetUnit e1 e2 => LetUnit (subst_val x v e1) (subst_val x v e2)
  | Pair e1 e2 => Pair (subst_val x v e1) (subst_val x v e2)
  | LetPair x1 x2 e1 e2 => 
    let e2' := if decide (BNamed x ≠ x1 ∧ BNamed x ≠ x2) 
               then subst_val x v e2 else e2 in
    LetPair x1 x2 (subst_val x v e1) e2'
  | Var y => if decide (BNamed x = y) then Val v else Var y
  | Lam y e => Lam y $ if decide (BNamed x ≠ y) then subst_val x v e else e
  | App e1 e2 => App (subst_val x v e1) (subst_val x v e2)
  | LetBang y e1 e2 =>
    let e2' := if decide (BNamed x ≠ y) then subst_val x v e2 else e2 in
    LetBang y (subst_val x v e1) e2'
  | Dup e => Dup $ subst_val x v e
  | Drp e => Drp $ subst_val x v e
  | New e => New $ subst_val x v e
  | Free e => Free $ subst_val x v e
  | Swap e1 e2 e3 => 
    Swap (subst_val x v e1) (subst_val x v e2) (subst_val x v e3)
  | LocLam e => LocLam $ subst_val x v e
  | LocApp e η => LocApp (subst_val x v e) η
  | LocPack η e => LocPack η $ subst_val x v e
  | LocUnpack y e1 e2 => 
    let e2' := if decide (BNamed x ≠ y) then subst_val x v e2 else e2 in
    LocUnpack y (subst_val x v e1) e2'
  end.

Definition subst_val' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst_val x v | BAnon => id end.


(* we also have to be able to substitute away location variables,
   which we use the Autosubst machinery for! *)
(* https://www.ps.uni-saarland.de/autosubst/doc/Ssr.SystemF_SN.html *)

(* First, substitute into loc *)
Instance Ids_loc : Ids loc. derive. Defined.
Instance Rename_loc : Rename loc. derive. Defined.
Instance Subst_loc : Subst loc. derive. Defined.

(* we need to be able to perform this same substitution into 
   both expressions and values *)

(* This will not substitute into the exprs inside of val, though. 
   This _should_ be okay, for the same reason why it is okay for
   variable substitution: values will be closed *)
(* BUT, if it turns out that this is broken, the solution will be
   to have two separate, non-mutually-recursive definitions,
   as in the Semantics lecture notes. *)
(* I have already gotten started with this setup, but I might
   have to revisit this and redo things with the other setup. *)
Instance HSubst_val : HSubst loc val. derive. Defined.
(* Since Hsubst_val was defined first, this should descend and
   substitute in the val case. Not sure if needed (or right)... *)
Instance HSubst_expr : HSubst loc expr. derive. Defined.

   
Inductive base_step : store * expr → store * expr → Prop :=
  | SLetUnit σ e :
    base_step (σ, LetUnit (Val UnitV) e) (σ, e)
  (* Extra instruction needed to step a pairs of values into a
     value which is a pair. See comments above for justification *)
  | SPair σ v1 v2 :
    base_step (σ, Pair (Val v1) (Val v2)) (σ, Val $ PairV v1 v2)
  | SLetPair σ x1 x2 v1 v2 e e' :
    e' = subst_val' x2 v2 (subst_val' x1 v1 e) →
    base_step (σ, LetPair x1 x2 (Val $ PairV v1 v2) e) (σ, e')
  | SLam σ x e :
    base_step (σ, Lam x e) (σ, Val $ LamV x e)
  | SApp σ x e v e' :
    e' = subst_val' x v e →
    base_step (σ, App (Val $ LamV x e) (Val v)) (σ, e')
  | SLetBang σ x v e e' :
    e' = subst_val' x v e →
    base_step (σ, LetBang x (Val v) e) (σ, e')
  | SDup σ v :
    base_step (σ, Dup $ Val $ BangV v) (σ, Val $ PairV (BangV v) (BangV v))
  | SDrp σ v :
    base_step (σ, Drp $ Val $ BangV v) (σ, Val UnitV)
  | SNew σ v (l : loclit) :
    σ.(heap) !! l = None →
    base_step 
      (σ, New $ Val v)
      (state_upd_heap <[l := v]> σ, 
       (* ⌜l, (cap, !ptr v)⌝, plus awkward val wrapping *)
       (* TODO: maybe the val wrapping is a little wrong here?? *)
       Val $ LocPackV (LocConst l) $ PairV CapV $ BangV $ PtrV l)
  | SFree σ l v :
    σ.(heap) !! l = Some v →
    base_step 
      (σ, Free $ Val $ LocPackV (LocConst l) $ PairV CapV $ BangV $ PtrV l)
      (state_upd_heap (delete l) σ, Val $ LocPackV (LocConst l) v)
  | SSwap σ l v1 v2 :
    σ.(heap) !! l = Some v1 →
    base_step (σ, Swap (Val CapV) (Val $ PtrV l) (Val v2))
              (state_upd_heap <[l := v2]> σ, Val $ PairV CapV v1)
  | SLocLam σ e :
    base_step (σ, LocLam e) (σ, Val $ LocLamV e)
  | SLocApp σ e l e' :
    e' = e.|[LocConst l/] →
    base_step (σ, LocApp (Val $ LocLamV e) $ LocConst l) (σ, e')
  | SLocPack σ η v :
    base_step (σ, LocPack η $ Val v) (σ, Val $ LocPackV η v)
  | SLUnpack σ x l v (e e' : expr) :
    e' = e.|[LocConst l/] →
    base_step (σ, LocUnpack x (Val $ LocPackV (LocConst l) v) e) (σ, e')
.


(* We also must lift head reduction to reduction-in-context *)

(* We define this in the more Iris-y way, which is to define just the individual
   items of the evaluation context, not the whole context grammar itself.
   This means we don't have an empty context, nor do we take contexts in variants.
   The more standard interface (EctxLanguage) is obtained by considering lists
   of evaluation contexts, where the empty list is the empty context.
   This appears to require establishing fewer lemmas. *)
(* In other words, write down the grammar without the E itself, or the empty context. *)
(* As an example, the expression ((e1, e2), e3) usually gets decomposed with
    E = (([], e2), e3), then plugged as E[e1]
   But here, it would be decomposed as two PairLCtx in a list.
   From this, we automatically get that plugging commutes with composing. *)
Inductive ectx_item :=
  | LetUnitCtx (e2 : expr)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | LetPairCtx (x1 x2 : binder) (e2 : expr)
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | LetBangCtx (x : binder) (e2 : expr)
  | DupCtx
  | DrpCtx
  | NewCtx
  | FreeCtx
  | SwapLCtx (e2 e3 : expr)
  | SwapMCtx (v1 : val) (e3 : expr)
  | SwapRCtx (v1 v2 : val)
  (* Following L3, these are location constants *)
  | LocAppCtx (l : loclit)
  | LocPackCtx (l : loclit)
  | LocUnpackCtx (x : binder) (e2 : {bind loc in expr})
.

Definition fill_item (Ei : ectx_item) (e : expr) : expr :=
  match Ei with
  | LetUnitCtx e2 => LetUnit e e2
  | PairLCtx e2 => Pair e e2
  (* of_val is just Val, but I am defining it this way for modularity *)
  | PairRCtx v1 => Pair (of_val v1) e
  | LetPairCtx x1 x2 e2 => LetPair x1 x2 e e2
  | AppLCtx e2 => App e e2
  | AppRCtx v1 => App (of_val v1) e
  | LetBangCtx x e2 => LetBang x e e2
  | DupCtx => Dup e
  | DrpCtx => Drp e
  | NewCtx => New e
  | FreeCtx => Free e
  | SwapLCtx e2 e3 => Swap e e2 e3
  | SwapMCtx v1 e3 => Swap (of_val v1) e e3
  | SwapRCtx v1 v2 => Swap (of_val v1) (of_val v2) e
  | LocAppCtx l => LocApp e $ LocConst l
  | LocPackCtx l => LocPack (LocConst l) e
  | LocUnpackCtx x e2 => LocUnpack x e e2
  end.

(* The following typeclass instances and lemmas are necessary to use EctxiLanguageMixin,
   just adapted to have fewer arguments since the definitions above have less Iris noise *)
(* The proofs are just as in the SimpLang instantiation / Semantics notes. *)
(* This probably isn't necessary for the project, but good practice to instantiate *)

(* Not quite a lemma about contexts, but still needed *)
Lemma val_base_stuck σ1 e1 σ2 e2 : base_step (σ1, e1) (σ2, e2) → to_val e1 = None.
Proof. inversion 1; naive_solver. Qed.

Lemma fill_item_val Ei e :
  is_Some (to_val (fill_item Ei e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ei; simplify_option_eq; eauto. Qed.

Global Instance fill_item_inj Ei : Inj (=) (=) (fill_item Ei).
Proof. destruct Ei; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_no_val_inj Ei1 Ei2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ei1 e1 = fill_item Ei2 e2 → Ei1 = Ei2.
Proof. destruct Ei1, Ei2; naive_solver eauto with f_equal. Qed.

Lemma base_ctx_step_val Ei σ1 e σ2 e2 :
  base_step (σ1, (fill_item Ei e)) (σ2, e2) → is_Some (to_val e).
Proof. destruct Ei; inversion_clear 1; simplify_option_eq; eauto. Qed.

(* I don't know how useful this is... *)
Module l3_iris_wrap.
  (* I tried to define the language above without extra Iris noise.
     However, this means instantiating is a little more annoying. *)
  
  (* As in SimpLang, observations are just an empty inductive *)
  Inductive observation :=.
  Lemma observations_empty (κs: list observation) : κs = [].
  Proof. by destruct κs as [ | [] ]. Qed.

  (* Iris expects this signature *)
  Definition base_step' (e1 : expr) (σ1 : store) (κ : list observation)
                        (e2 : expr) (σ2 : store) (efs : list expr) : Prop :=
    efs = [] ∧ base_step (σ1, e1) (σ2, e2).

  Lemma val_base_stuck' e1 σ1 κ e2 σ2 efs : base_step' e1 σ1 κ e2 σ2 efs → to_val e1 = None.
  Proof. unfold base_step'; intros [? ?]; eauto using val_base_stuck. Qed.

  Lemma base_ctx_step_val' Ei e σ1 κ e2 σ2 efs :
    base_step' (fill_item Ei e) σ1 κ e2 σ2 efs → is_Some (to_val e).
  Proof. unfold base_step'; intros [? ?]; eauto using base_ctx_step_val. Qed.

  Lemma l3_lang_mixin : EctxiLanguageMixin of_val to_val fill_item base_step'.
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_base_stuck',
      fill_item_val, fill_item_no_val_inj, base_ctx_step_val'.
  Qed.
End l3_iris_wrap.

Canonical Structure l3_ectxi_lang := EctxiLanguage l3_iris_wrap.l3_lang_mixin.
Canonical Structure l3_ectx_lang := EctxLanguageOfEctxi l3_ectxi_lang.
Canonical Structure l3_lang := LanguageOfEctx l3_ectx_lang.

(* this defines lots of things like step, cfg, etc,
   though they do have a bit of Iris-y stuff around it... *)
(* see also relations for nsteps, rtc, etc *)

End l3_lang.