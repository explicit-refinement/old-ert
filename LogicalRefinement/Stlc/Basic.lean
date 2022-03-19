import LogicalRefinement.Wk

inductive Ty
| bot
| unit
| nats
| arrow (A B: Ty)
| prod (A B: Ty)
| coprod (A B: Ty)

open Ty

def Ty.interp_based_in (A: Ty) (M: Type -> Type): (Type -> Type) -> Type := λU => U (match A with
| bot => Empty
| unit => Unit
| nats => Nat
| arrow A B => A.interp_based_in M id -> B.interp_based_in M M
| prod A B => Prod (A.interp_based_in M id) (B.interp_based_in M id)
| coprod A B => Sum (A.interp_based_in M id) (B.interp_based_in M id))

def Ty.interp_in (A: Ty) (M: Type -> Type) := A.interp_based_in M M
def Ty.interp_val_in (A: Ty) (M: Type -> Type) := A.interp_based_in M id
def Ty.interp_val_char {A: Ty} {M}: A.interp_in M = M (A.interp_val_in M) := by cases A <;> rfl

-- Note: if the λx gets moved into the match, we get a kernel error; maybe post on Zulip about this...
def Ty.eager {A: Ty} {M: Type -> Type} [Monad M]: A.interp_val_in M -> A.interp_in M := 
  λx => by cases A with
    | bot => cases x
    | _ => exact do return x

instance myOptionMonad: Monad Option where
  pure := some
  bind := λx f => match x with | none => none | some x => f x 

def Ty.interp (A: Ty): Type := A.interp_in Option
def Ty.interp_val (A: Ty): Type := A.interp_val_in Option

def Ty.abort (A: Ty): A.interp := by cases A <;> exact none
def Ty.app {A B} (l: (arrow A B).interp) (r: A.interp): B.interp := by
  cases A <;>
  exact match l, r with
  | some l, some r => l r
  | _, _ => B.abort
def Ty.pair {A B} (l: A.interp) (r: B.interp): (prod A B).interp := by
  cases A <;> cases B <;>
  exact match l, r with
  | some l, some r => some (l, r)
  | _, _ => none
def Ty.inl {A B} (e: A.interp): (coprod A B).interp := by 
  cases A <;> exact e.map Sum.inl
def Ty.inr {A B} (e: B.interp): (coprod A B).interp := by 
  cases B <;> exact e.map Sum.inr

inductive Stlc
-- Basic
| var (n: Nat)
| lam (A: Ty) (s: Stlc)
| app (F: Ty) (s t: Stlc)

-- Products and coproducts
| pair (l r: Stlc)
| let_pair (e: Stlc) (e': Stlc)

| inj (f: Fin 2) (e: Stlc)
| cases (d l r: Stlc)

-- Erasure
| nil

-- Failure
| abort

-- Natural numbers
| zero
| succ
| natrec (n: Stlc) (z: Stlc) (s: Stlc)

def Stlc.wk: Stlc -> Wk -> Stlc
| var n, ρ => var (ρ.var n)
| lam A s, ρ => lam A (s.wk ρ.lift)
| app F s t, ρ => app F (s.wk ρ) (t.wk ρ)
| pair l r, ρ => pair (l.wk ρ) (r.wk ρ)
| let_pair e e', ρ => let_pair (e.wk ρ) (e'.wk (ρ.liftn 2))
| inj i e, ρ => inj i (e.wk ρ)
| cases d l r, ρ => cases (d.wk ρ) (l.wk ρ.lift) (r.wk ρ.lift)
| natrec n z s, ρ => natrec (n.wk ρ) (z.wk ρ) (s.wk ρ.lift)
| c, ρ => c

def Stlc.wk1 (σ: Stlc): Stlc := σ.wk Wk.wk1

def Stlc.Context := List Ty

def Stlc.Context.interp: Context -> Type
| [] => Unit
| A::As => Prod A.interp_val (interp As)

inductive Stlc.HasVar: Context -> Ty -> Nat -> Prop
| zero {Γ A}: HasVar (A::Γ) A 0
| succ {Γ A B n}: HasVar Γ A n -> HasVar (B::Γ) A (Nat.succ n)

theorem Stlc.HasVar.zero_invert {Γ A B} (P: HasVar (A::Γ) B 0): A = B := by cases P; rfl
theorem Stlc.HasVar.succ_invert {Γ A B} (P: HasVar (A::Γ) B (n + 1)): HasVar Γ B n := by cases P; assumption

def Stlc.HasVar.interp {Γ A n} (H: HasVar Γ A n) (G: Γ.interp): A.interp_val :=
  match Γ with
  | [] => by {
    apply False.elim;
    cases H
  }
  | B::Γ => 
    let (IA, G) := G; 
    match n with
    | 0 => by rw [H.zero_invert] at IA; exact IA
    | Nat.succ n => H.succ_invert.interp G

inductive Stlc.HasType: Context -> Stlc -> Ty -> Prop
| var {Γ A n}: HasVar Γ A n -> HasType Γ (var n) A
| lam {Γ A B s}: HasType (A::Γ) s B -> HasType Γ (lam A s) (arrow A B)
| app {Γ A B s t}: HasType Γ s (arrow A B) -> HasType Γ t A -> HasType Γ (app (arrow A B) s t) B

| pair {Γ A B l r}: HasType Γ l A -> HasType Γ r B -> HasType Γ (pair l r) (prod A B)
| let_pair {Γ A B C e e'}: 
  HasType Γ e (prod A B) -> HasType (B::A::Γ) e' C -> HasType Γ (let_pair e e') C

| inj0 {Γ A B e}: HasType Γ e A -> HasType Γ (inj 0 e) (coprod A B)
| inj1 {Γ A B e}: HasType Γ e B -> HasType Γ (inj 1 e) (coprod A B)
| cases {Γ A B C d l r}: 
  HasType Γ d (coprod A B) -> HasType (A::Γ) l C -> HasType (A::Γ) r C -> 
  HasType Γ (cases d l r) C

| nil {Γ}: HasType Γ nil unit

| abort {Γ A}: HasType Γ abort A

| zero {Γ}: HasType Γ zero nats
| succ {Γ}: HasType Γ succ (arrow nats nats)
| natrec {Γ C n z s}:
  HasType Γ n nats ->
  HasType Γ z C ->
  HasType (A::Γ) s C ->
  HasType Γ (natrec n z s) C

inductive Stlc.WkCtx: Wk -> Context -> Context -> Prop
  | id: WkCtx Wk.id Γ Γ
  | step {ρ Γ Δ A}: WkCtx ρ Γ Δ -> WkCtx ρ.step (A::Γ) Δ 
  | lift {ρ Γ Δ A}: WkCtx ρ Γ Δ -> WkCtx ρ.lift (A::Γ) (A::Δ)

theorem Stlc.HasType.wk {Γ Δ ρ a A}: WkCtx ρ Γ Δ -> HasType Δ a A -> HasType Γ (a.wk ρ) A := by {
  sorry
}

def Stlc.Subst := Nat -> Stlc

def Stlc.Subst.lift (σ: Subst): Subst
| 0 => var 0
| n + 1 => (σ n).wk1

def Stlc.Subst.liftn (σ: Subst): Nat -> Subst
| 0 => σ
| n + 1 => (σ.lift).liftn n

def Stlc.subst: Stlc -> Subst -> Stlc
| var n, σ => σ n
| lam A s, σ => lam A (s.subst σ.lift)
| app (arrow A B) s t, σ => app (arrow A B) (s.subst σ) (t.subst σ)
| pair l r, σ => pair (l.subst σ) (r.subst σ)
| let_pair e e', σ => let_pair (e.subst σ) (e'.subst (σ.liftn 2))
| inj i e, σ => inj i (e.subst σ)
| cases d l r, σ => cases (d.subst σ) (l.subst σ.lift) (r.subst σ.lift)
| natrec n z s, σ => natrec (n.subst σ) (z.subst σ) (s.subst σ.lift)
| c, σ => c

def Stlc.SubstCtx (σ: Subst) (Γ Δ: Context): Prop :=  
  ∀{n A}, HasVar Δ A n -> HasType Γ (σ n) A

theorem Stlc.HasType.subst {Γ Δ σ a A}: 
  SubstCtx σ Γ Δ -> HasType Δ a A -> HasType Γ (a.subst σ) A := by {
  sorry
}

def Stlc.HasType.interp {Γ a A} (H: HasType Γ a A) (G: Γ.interp): A.interp :=
  match a with
  | Stlc.var n => 
    let v: HasVar Γ A n := by cases H; assumption;
    Ty.eager (v.interp G)
  | Stlc.lam X s => by cases A with
    | arrow A B =>
      have H: HasType (A::Γ) s B := by cases H; assumption;
      exact some (λx => H.interp (x, G))
    | _ => apply False.elim; cases H
  | Stlc.app P l r => 
    by 
    have Hl: HasType Γ l P := by cases H; assumption;
    cases P with
    | arrow X _ =>
      have Hr: HasType Γ r X := by cases H; assumption;
      let Il := Hl.interp G;
      let Ir := Hr.interp G;
      sorry
    | _ => apply False.elim; cases H
  | _ => sorry