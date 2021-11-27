mutual

inductive Ty where
  | nat
  | pi (A: Ty) (B: Ty)
  | sigma (A: Ty) (B: Ty)
  | coprod (A: Ty) (B: Ty)
  | set (A: Ty) (φ: Pr)
  | assume (φ: Pr) (A: Ty)
  | intersect (A: Ty) (B: Ty)
  | union (A: Ty) (B: Ty)

inductive Pr where
  | top
  | bot
  | and (φ: Pr) (ψ: Pr)
  | or (φ: Pr) (ψ: Pr)
  | implies (φ: Pr) (ψ: Pr)
  | forall_ (A: Ty) (φ: Pr)
  | exists_ (A: Ty) (φ: Pr)
  | eq (A: Ty) (e: Term) (e': Term)

inductive Term where
  | var (n: Nat)
  | lam (A: Ty) (e: Term)
  | app (l: Term) (r: Term)
  | pair (l: Term) (r: Term)
  | proj (b: Bool) (e: Term)
  | inj (b: Bool) (e: Term)
  | case (e: Term) (l: Term) (r: Term)
  | mkset (e: Term) (p: Proof)
  | letset (e: Term)
  | lam_pr (φ: Proof) (e: Term)
  | app_pr (e: Term) (p: Proof)
  | lam_irrel (A: Ty) (e: Term)
  | app_irrel (l: Term) (r: Term)
  | repr (l: Term) (r: Term)
  | let_repr (e: Term)

inductive Proof where
  | nil
  | abort (p: Proof)
  | conj (l: Proof) (r: Proof)
  | proj (b: Bool) (p: Proof)
  | disj (b: Bool) (p: Proof)
  | case (p: Proof) (l: Proof) (r: Proof)
  | lam (φ: Proof) (p: Proof)
  | app (l: Proof) (r: Proof)
  | general (A: Ty) (p: Proof)
  | inst (p: Proof) (e: Term)
  | witness (e: Term) (p: Proof)
  | let_wit (p: Proof)
  | refl (e: Term)
  --TODO: equality axioms...

end