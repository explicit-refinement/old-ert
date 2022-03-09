inductive Ty
| fn (A: Ty) (B: Ty)
| nats
| bool

inductive Stlc
-- Basic
| lam (A: Ty) (s: Stlc)
| app (s: Stlc) (t: Stlc)
| var (n: Nat)

-- Erasure
| nil

-- Failure
| abort

-- Natural numbers
| zero
| succ
| natrec (A: Ty) (n: Stlc) (z: Stlc) (s: Stlc)