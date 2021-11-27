inductive Untyped where
  -- Types
  | nat
  | pi (A: Untyped) (B: Untyped)
  | sigma (A: Untyped) (B: Untyped)
  | coprod (A: Untyped) (B: Untyped)
  | set (A: Untyped) (B: Untyped)
  | assume (φ: Untyped) (A: Untyped)
  | intersect (A: Untyped) (B: Untyped)
  | union (A: Untyped) (B: Untyped)

  -- Propositions
  | top
  | bot
  | and (φ: Untyped) (ψ: Untyped)
  | or (φ: Untyped) (ψ: Untyped)
  | implies (φ: Untyped) (ψ: Untyped)
  | forall_ (A: Untyped) (φ: Untyped)
  | exists_ (A: Untyped) (φ: Untyped)
  | eq (A: Untyped) (e: Untyped) (e': Untyped)

  -- Terms
  | var (n: Nat)
  | lam (A: Untyped) (e: Untyped)
  | app (l: Untyped) (r: Untyped)
  | pair (l: Untyped) (r: Untyped)
  | proj (b: Bool) (e: Untyped)
  | inj (b: Bool) (e: Untyped)
  | case (e: Untyped) (l: Untyped) (r: Untyped)
  | mkset (e: Untyped) (p: Untyped)
  | letset (e: Untyped)
  | lam_pr (φ: Untyped) (e: Untyped)
  | app_pr (e: Untyped) (p: Untyped)
  | lam_irrel (A: Untyped) (e: Untyped)
  | app_irrel (l: Untyped) (r: Untyped)
  | repr (l: Untyped) (r: Untyped)
  | let_repr (e: Untyped)

  -- Proofs
  | nil
  | abort (p: Untyped)
  | conj (l: Untyped) (r: Untyped)
  | proj_conj (b: Bool) (p: Untyped)
  | disj (b: Bool) (p: Untyped)
  | case_disj (p: Untyped) (l: Untyped) (r: Untyped)
  | lam_imp (φ: Untyped) (p: Untyped)
  | ponens (l: Untyped) (r: Untyped)
  | general (A: Untyped) (p: Untyped)
  | inst (p: Untyped) (e: Untyped)
  | witness (e: Untyped) (p: Untyped)
  | let_wit (p: Untyped)
  | refl (e: Untyped)
  --TODO: equality axioms...