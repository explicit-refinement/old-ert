inductive Ty
| unit
| nats
| arrow (A B: Ty)
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

def Stlc.Context := List Ty

inductive Stlc.HasVar: Context -> Nat -> Ty -> Prop
| zero {Γ A}: HasVar (A::Γ) 0 A
| succ {Γ A B n}: HasVar Γ n A -> HasVar (B::Γ) (Nat.succ n) A

inductive Stlc.HasType: Context -> Stlc -> Ty -> Prop
| var {Γ A n}: HasVar Γ n A -> HasType Γ (var n) A
| lam {Γ A B s}: HasType (A::Γ) s B -> HasType Γ (lam A s) (arrow A B)
| app {Γ A B s t}: HasType Γ s (arrow A B) -> HasType Γ t A -> HasType Γ (app s t) B

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