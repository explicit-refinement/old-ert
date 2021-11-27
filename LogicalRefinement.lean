import Init.Data.Nat

inductive Untyped: Nat -> Type 0 where
  -- Types
  | nat: Untyped n
  | pi (A: Untyped n) (B: Untyped (n + 1)): Untyped n
  | sigma (A: Untyped n) (B: Untyped (n + 1)): Untyped n
  | coprod (A: Untyped n) (B: Untyped n): Untyped n
  | set (A: Untyped n) (φ: Untyped (n + 1)): Untyped n
  | assume (φ: Untyped n) (A: Untyped n): Untyped n
  | intersect (A: Untyped n) (B: Untyped (n + 1)): Untyped n
  | union (A: Untyped n) (B: Untyped (n + 1)): Untyped n

  -- Proposition s
  | top: Untyped n
  | bot: Untyped n
  | and (φ: Untyped n) (ψ: Untyped n): Untyped n
  | or (φ: Untyped n) (ψ: Untyped n): Untyped n
  | implies (φ: Untyped n) (ψ: Untyped n): Untyped n
  | forall_ (A: Untyped n) (φ: Untyped (n + 1)): Untyped n
  | exists_ (A: Untyped n) (φ: Untyped (n + 1)): Untyped n
  | eq (A: Untyped n) (e: Untyped n) (e': Untyped n): Untyped n

  -- Terms
  | var (m: Fin n): Untyped n
  | lam (A: Untyped n) (e: Untyped (n + 1)): Untyped n
  | app (l: Untyped n) (r: Untyped n): Untyped n
  | pair (l: Untyped n) (r: Untyped n): Untyped n
  | proj (b: Bool) (e: Untyped n): Untyped n
  | inj (b: Bool) (e: Untyped n): Untyped n
  | case (e: Untyped n) (l: Untyped n) (r: Untyped n): Untyped n
  | mkset (e: Untyped n) (p: Untyped n): Untyped n
  | letset (e: Untyped (n + 2)): Untyped n
  | lam_pr (φ: Untyped n) (e: Untyped (n + 1)): Untyped n
  | app_pr (e: Untyped n) (p: Untyped n): Untyped n
  | lam_irrel (A: Untyped n) (e: Untyped (n + 1)): Untyped n
  | app_irrel (l: Untyped n) (r: Untyped n): Untyped n
  | repr (l: Untyped n) (r: Untyped n): Untyped n
  | let_repr (e: Untyped (n + 2)): Untyped n

  -- Proofs
  | prf (m: Fin n): Untyped n
  | nil: Untyped n
  | abort (p: Untyped n): Untyped n
  | conj (l: Untyped n) (r: Untyped n): Untyped n
  | comp (b: Bool) (p: Untyped n): Untyped n
  | disj (b: Bool) (p: Untyped n): Untyped n
  | case_pr (p: Untyped n) (l: Untyped n) (r: Untyped n): Untyped n
  | imp (φ: Untyped n) (p: Untyped (n + 1)): Untyped n
  | mp (l: Untyped n) (r: Untyped n): Untyped n
  | general (A: Untyped n) (p: Untyped (n + 1)): Untyped n
  | inst (p: Untyped n) (e: Untyped n): Untyped n
  | witness (e: Untyped n) (p: Untyped n): Untyped n
  | let_wit (p: Untyped (n + 2)): Untyped n
  | refl (e: Untyped n): Untyped n
  --TODO: equality axioms...

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

def wk (ρ: Wk n m): Untyped m -> Untyped n

  -- Types
  | Untyped.nat => Untyped.nat
  | Untyped.pi A B => Untyped.pi (wk ρ A) (wk (Wk.lift ρ) B)
  | Untyped.sigma A B => Untyped.sigma (wk ρ A) (wk (Wk.lift ρ) B)
  | Untyped.coprod A B => Untyped.coprod (wk ρ A) (wk ρ B)
  | Untyped.set A φ => Untyped.set (wk ρ A) (wk (Wk.lift ρ) φ)
  | Untyped.assume φ A => Untyped.assume (wk ρ φ) (wk ρ A)
  | Untyped.intersect A B => Untyped.intersect (wk ρ A) (wk (Wk.lift ρ) B)
  | Untyped.union A B => Untyped.union (wk ρ A) (wk (Wk.lift ρ) B)

  -- Propositions
  | Untyped.top => Untyped.top
  | Untyped.bot => Untyped.bot
  | Untyped.and φ ψ => Untyped.and (wk ρ φ) (wk ρ ψ)
  | Untyped.or φ ψ => Untyped.or (wk ρ φ) (wk ρ ψ)
  | Untyped.implies φ ψ => Untyped.implies (wk ρ φ) (wk ρ ψ)
  | Untyped.forall_ A φ => Untyped.forall_ (wk ρ A) (wk (Wk.lift ρ) φ)
  | Untyped.exists_ A φ => Untyped.exists_ (wk ρ A) (wk (Wk.lift ρ) φ)
  | Untyped.eq A l r => Untyped.eq (wk ρ A) (wk ρ l) (wk ρ r)
  
  -- Terms
  | Untyped.var m => Untyped.var (wkVar ρ m)
  | Untyped.lam A e => Untyped.lam (wk ρ A) (wk (Wk.lift ρ) e)
  | Untyped.app l r => Untyped.app (wk ρ l) (wk ρ r)
  | Untyped.pair l r => Untyped.pair (wk ρ l) (wk ρ r)
  | Untyped.proj b e => Untyped.proj b (wk ρ e)
  | Untyped.inj b e => Untyped.inj b (wk ρ e)
  | Untyped.case e l r => Untyped.case (wk ρ e) (wk ρ l) (wk ρ r)
  | Untyped.mkset e p => Untyped.mkset (wk ρ e) (wk ρ p)
  | Untyped.letset e => Untyped.letset (wk (Wk.lift (Wk.lift ρ)) e)
  | Untyped.lam_pr φ e => Untyped.lam_pr (wk ρ φ) (wk (Wk.lift ρ) e)
  | Untyped.app_pr φ e => Untyped.app_pr (wk ρ φ) (wk ρ e)
  | Untyped.lam_irrel l r => Untyped.lam_irrel (wk ρ l) (wk (Wk.lift ρ) r)
  | Untyped.app_irrel l r => Untyped.app_irrel (wk ρ l) (wk ρ r)
  | Untyped.repr l r => Untyped.repr (wk ρ l) (wk ρ r)
  | Untyped.let_repr e => Untyped.let_repr (wk (Wk.lift (Wk.lift ρ)) e)

  -- Proofs
  | Untyped.prf m => Untyped.prf (wkVar ρ m)
  | Untyped.nil => Untyped.nil
  | Untyped.abort p => Untyped.abort (wk ρ p)
  | Untyped.conj l r => Untyped.conj (wk ρ l) (wk ρ r)
  | Untyped.comp b p => Untyped.comp b (wk ρ p)
  | Untyped.disj b p => Untyped.disj b (wk ρ p)
  | Untyped.case_pr p l r => Untyped.case_pr (wk ρ p) (wk ρ l) (wk ρ r)
  | Untyped.imp φ p => Untyped.imp (wk ρ φ) (wk (Wk.lift ρ) p)
  | Untyped.mp l r => Untyped.mp (wk ρ l) (wk ρ r)
  | Untyped.general A p => Untyped.general (wk ρ A) (wk (Wk.lift ρ) p)
  | Untyped.inst p e => Untyped.inst (wk ρ p) (wk ρ e)
  | Untyped.witness e p => Untyped.witness (wk ρ e) (wk ρ p)
  | Untyped.let_wit p => Untyped.let_wit (wk (Wk.lift (Wk.lift ρ)) p)
  | Untyped.refl e => Untyped.refl (wk ρ e)

inductive Hypothesis (n: Nat) where
  | comp (A: Untyped n)
  | refine (A: Untyped n)
  | logic (φ: Untyped n)

inductive Con: Nat -> Type where
  | ε: Con 0
  | cons (H: Hypothesis n) (c: Con n): Con (n + 1)