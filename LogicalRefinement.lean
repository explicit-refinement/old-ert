import Init.Data.Nat

mutual

  inductive Ty: Nat -> Type where
    | nat: Ty n
    | pi (A: Ty n) (B: Ty (1 + n)): Ty n
    | sigma (A: Ty n) (B: Ty (1 + n)): Ty n
    | coprod (A: Ty n) (B: Ty n): Ty n
    | set (A: Ty n) (φ: Pr (1 + n)): Ty n
    | assume (φ: Pr n) (A: Ty n): Ty n
    | intersect (A: Ty n) (B: Ty (1 + n)): Ty n
    | union (A: Ty n) (B: Ty (1 + n)): Ty n

  inductive Pr: Nat -> Type where
    | top: Pr n
    | bot: Pr n
    | and (φ: Pr n) (ψ: Pr n): Pr n
    | or (φ: Pr n) (ψ: Pr n): Pr n
    | implies (φ: Pr n) (ψ: Pr n): Pr n
    | forall_ (A: Ty n) (φ: Pr (1 + n)): Pr n
    | exists_ (A: Ty n) (φ: Pr (1 + n)): Pr n
    | eq (A: Ty n) (e: Term n) (e': Term n): Pr n

  inductive Term: Nat -> Type where
    | var (m: Fin n): Term n
    | lam (A: Ty n) (e: Term (1 + n)): Term n
    | app (l: Term n) (r: Term n): Term n
    | pair (l: Term n) (r: Term n): Term n
    | proj (b: Bool) (e: Term n): Term n
    | inj (b: Bool) (e: Term n): Term n
    | case (e: Term n) (l: Term n) (r: Term n): Term n
    | mkset (e: Term n) (p: Proof n): Term n
    | letset (e: Term (2 + n)): Term n
    | lam_pr (φ: Proof n) (e: Term (1 + n)): Term n
    | app_pr (e: Term n) (p: Proof (1 + n)): Term n
    | lam_irrel (A: Ty n) (e: Term (1 + n)): Term n
    | app_irrel (l: Term n) (r: Term n): Term n
    | repr (l: Term n) (r: Term n): Term n
    | let_repr (e: Term (2 + n)): Term n

  inductive Proof: Nat -> Type where
    | var (m: Fin n): Proof n
    | nil: Proof n
    | abort (p: Proof n): Proof n
    | conj (l: Proof n) (r: Proof n): Proof n
    | proj (b: Bool) (p: Proof n): Proof n
    | disj (b: Bool) (p: Proof n): Proof n
    | case (p: Proof n) (l: Proof n) (r: Proof n): Proof n
    | lam (φ: Proof n) (p: Proof (1 + n)): Proof n
    | app (l: Proof n) (r: Proof n): Proof n
    | general (A: Ty n) (p: Proof (1 + n)): Proof n
    | inst (p: Proof n) (e: Term n): Proof n
    | witness (e: Term n) (p: Proof n): Proof n
    | let_wit (p: Proof (2 + n)): Proof n
    | refl (e: Term n): Proof n
    --TODO: equality axioms...

end

inductive Wk: Nat -> Nat -> Type 0 where
  | id: Wk n n
  | step: Wk m n -> Wk (Nat.succ m) n
  | lift: Wk m n -> Wk (Nat.succ m) (Nat.succ n)

def wk_compose: Wk n m -> Wk m l -> Wk n l
  | Wk.id, ρ => ρ
  | Wk.step ρ, ρ' => Wk.step (wk_compose ρ ρ')
  | Wk.lift ρ, Wk.id => Wk.lift ρ
  | Wk.lift ρ, Wk.step ρ' => Wk.step (wk_compose ρ ρ')
  | Wk.lift ρ, Wk.lift ρ' => Wk.lift (wk_compose ρ ρ')

infixl:30 " ⋅ " => wk_compose

def Fin.succ: Fin n -> Fin (Nat.succ n)
  | Fin.mk m p => Fin.mk (Nat.succ m) (Nat.lt_succ_of_le p)

def Fin.zero: Fin (Nat.succ n) := Fin.mk 0 (Nat.zero_lt_of_lt (Nat.lt_succ_self _))

def wkVar: Wk n m -> Fin m -> Fin n
  | Wk.id, v => v
  | Wk.step ρ, v => Fin.succ (wkVar ρ v)
  | Wk.lift ρ, Fin.mk 0 p => Fin.zero
  | Wk.lift ρ, Fin.mk (Nat.succ n) p => Fin.succ (wkVar ρ (Fin.mk n (Nat.lt_of_succ_lt_succ p)))

mutual

  def wkTy: Wk n m -> Ty n -> Ty m := sorry

  def wkPr: Wk n m -> Pr n -> Pr m := sorry

  def wkTerm: Wk n m -> Term n -> Term m := sorry

  def wkProof: Wk n m -> Proof n -> Proof m := sorry

end

inductive Hypothesis (n: Nat) where
  | comp (A: Ty n)
  | refine (A: Ty n)
  | logic (φ: Pr n)

inductive Con: Nat -> Type where
  | ε: Con 0
  | cons (H: Hypothesis n) (c: Con n): Con (1 + n)