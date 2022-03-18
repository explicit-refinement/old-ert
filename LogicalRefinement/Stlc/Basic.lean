import LogicalRefinement.Wk

inductive Ty
| unit
| nats
| arrow (A B: Ty)
| prod (A B: Ty)
| coprod (A B: Ty)

open Ty

def Ty.interp: (A: Ty) -> Type
| unit => Unit
| nats => Nat
| arrow A B => A.interp -> B.interp
| prod A B => Prod A.interp B.interp
| coprod A B => Sum A.interp B.interp

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
| A::As => Prod A.interp (interp As)

inductive Stlc.HasVar: Context -> Ty -> Nat -> Prop
| zero {Γ A}: HasVar (A::Γ) A 0
| succ {Γ A B n}: HasVar Γ A n -> HasVar (B::Γ) A (Nat.succ n)

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

def Stlc.interp {Γ a A}: HasType Γ a A -> Γ.interp -> A.interp :=
  match a with
  | _ => sorry