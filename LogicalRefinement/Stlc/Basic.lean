inductive Ty
| unit
| nats
| fn (A B: Ty)
| prod (A B: Ty)
| coprod (A B: Ty)

open Ty

inductive Stlc
-- Basic
| lam (A: Ty) (s: Stlc)
| app (s t: Stlc)
| var (n: Nat)

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