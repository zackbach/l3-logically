From stdpp Require Export binders strings.
From l3 Require Export loclit.
From Autosubst Require Export Autosubst.
From iris.proofmode Require Import proofmode.

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
  | LocPackV (η : loc) (e : expr)
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
       Val $ LocPackV (LocConst l) $ Val $ PairV CapV $ BangV $ PtrV l)
  | SFree σ l v :
    σ.(heap) !! l = Some v →
    base_step 
      (σ, Free $ Val $ LocPackV (LocConst l) $ Val $ PairV CapV $ BangV $ PtrV l)
      (state_upd_heap (delete l) σ, Val $ LocPackV (LocConst l) $ Val v)
  | SSwap σ l v1 v2 :
    σ.(heap) !! l = Some v1 →
    base_step (σ, Swap (Val CapV) (Val $ PtrV l) (Val v2))
              (state_upd_heap <[l := v2]> σ, Val $ PairV CapV v1)
  | SLocLam σ e :
    base_step (σ, LocLam e) (σ, Val $ LocLamV e)
  | SLocApp σ e l e' :
    e' = e.|[LocConst l/] →
    base_step (σ, LocApp (Val $ LocLamV e) $ LocConst l) (σ, e')
  | SLocPack σ η e :
    base_step (σ, LocPack η e) (σ, Val $ LocPackV η e)
  | SLUnpack σ x l v (e e' : expr) :
    e' = e.|[LocConst l/] →
    base_step (σ, LocUnpack x (Val $ LocPackV (LocConst l) $ Val v) e) (σ, e')
.


End l3_lang.