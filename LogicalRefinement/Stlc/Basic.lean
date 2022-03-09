inductive Ty
| unit
| nats
| fn (A B: Ty)
| prod (A B: Ty)
| coprod (A B: Ty)

open Ty

inductive Stlc
-- Basic
| var (n: Nat)
| lam (A: Ty) (s: Stlc)
| app (s t: Stlc)

-- Products and coproducts
| pair (l r: Stlc)
| proj (f: Fin 2) (e: Stlc)
| inj (f: Fin 2) (e: Stlc)
| cases (d l r: Stlc)

-- Erasure
| nil

-- Failure
| abort

-- Natural numbers
| zero
| succ
| natrec (A: Ty) (n: Stlc) (z: Stlc) (s: Stlc)

def Stlc.Context := List Ty

inductive Stlc.HasVar: Context -> Nat -> Ty -> Prop
| zero {Γ A}: HasVar (A::Γ) 0 A
| succ {Γ A B n}: HasVar Γ n A -> HasVar (B::Γ) (Nat.succ n) A

inductive Stlc.HasType: Context -> Stlc -> Ty -> Prop
| lam {Γ A B s}: HasType (A::Γ) s B -> HasType Γ (lam A s) (fn A B)
| app {Γ A B s t}: HasType Γ s (fn A B) -> HasType Γ t A -> HasType Γ (app s t) B