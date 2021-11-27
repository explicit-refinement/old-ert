mutual

inductive Ty: Nat -> Type where
  | nat: Ty n
  | pi (A: Ty n) (B: Ty (n + 1)): Ty n
  | sigma (A: Ty n) (B: Ty (n + 1)): Ty n
  | coprod (A: Ty n) (B: Ty n): Ty n
  | set (A: Ty n) (φ: Pr (n + 1)): Ty n
  | assume (φ: Pr n) (A: Ty n): Ty n
  | intersect (A: Ty n) (B: Ty (n + 1)): Ty n
  | union (A: Ty n) (B: Ty (n + 1)): Ty n

inductive Pr: Nat -> Type where
  | top: Pr n
  | bot: Pr n
  | and (φ: Pr n) (ψ: Pr n): Pr n
  | or (φ: Pr n) (ψ: Pr n): Pr n
  | implies (φ: Pr n) (ψ: Pr n): Pr n
  | forall_ (A: Ty n) (φ: Pr (n + 1)): Pr n
  | exists_ (A: Ty n) (φ: Pr (n + 1)): Pr n
  | eq (A: Ty n) (e: Term n) (e': Term n): Pr n

inductive Term: Nat -> Type where
  | var (m: Fin n): Term n
  | lam (A: Ty n) (e: Term (n + 1)): Term n
  | app (l: Term n) (r: Term n): Term n
  | pair (l: Term n) (r: Term n): Term n
  | proj (b: Bool) (e: Term n): Term n
  | inj (b: Bool) (e: Term n): Term n
  | case (e: Term n) (l: Term n) (r: Term n): Term n
  | mkset (e: Term n) (p: Proof n): Term n
  | letset (e: Term (n + 2)): Term n
  | lam_pr (φ: Proof n) (e: Term (n + 1)): Term n
  | app_pr (e: Term n) (p: Proof (n + 1)): Term n
  | lam_irrel (A: Ty n) (e: Term (n + 1)): Term n
  | app_irrel (l: Term n) (r: Term n): Term n
  | repr (l: Term n) (r: Term n): Term n
  | let_repr (e: Term (n + 2)): Term n

inductive Proof: Nat -> Type where
  | var (m: Fin n): Proof n
  | nil: Proof n
  | abort (p: Proof n): Proof n
  | conj (l: Proof n) (r: Proof n): Proof n
  | proj (b: Bool) (p: Proof n): Proof n
  | disj (b: Bool) (p: Proof n): Proof n
  | case (p: Proof n) (l: Proof n) (r: Proof n): Proof n
  | lam (φ: Proof n) (p: Proof (n + 1)): Proof n
  | app (l: Proof n) (r: Proof n): Proof n
  | general (A: Ty n) (p: Proof (n + 1)): Proof n
  | inst (p: Proof n) (e: Term n): Proof n
  | witness (e: Term n) (p: Proof n): Proof n
  | let_wit (p: Proof (n + 2)): Proof n
  | refl (e: Term n): Proof n
  --TODO: equality axioms...

end

inductive Hypothesis (n: Nat) where
  | comp (A: Ty n)
  | refine (A: Ty n)
  | logic (φ: Pr n)

inductive Con: Nat -> Type where
  | ε: Con 0
  | cons (H: Hypothesis n) (c: Con n): Con (n + 1)