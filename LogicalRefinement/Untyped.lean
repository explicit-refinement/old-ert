-- Based off https://github.com/mr-ohman/logrel-mltt/blob/master/Definition/Untyped.agda

import Init.Data.Nat
import LogicalRefinement.Wk

inductive Untyped: Nat -> Type 0 where

  -- Variables
  | var (m: Fin n): Untyped n

  -- Types
  | nat: Untyped n
  | pi (A: Untyped n) (B: Untyped (n + 1)): Untyped n
  | sigma (A: Untyped n) (B: Untyped (n + 1)): Untyped n
  | coprod (A: Untyped n) (B: Untyped n): Untyped n
  | set (A: Untyped n) (φ: Untyped (n + 1)): Untyped n
  | assume (φ: Untyped n) (A: Untyped n): Untyped n
  | intersect (A: Untyped n) (B: Untyped (n + 1)): Untyped n
  | union (A: Untyped n) (B: Untyped (n + 1)): Untyped n

  -- Propositions
  | top: Untyped n
  | bot: Untyped n
  | and (φ: Untyped n) (ψ: Untyped n): Untyped n
  | or (φ: Untyped n) (ψ: Untyped n): Untyped n
  | implies (φ: Untyped n) (ψ: Untyped n): Untyped n
  | forall_ (A: Untyped n) (φ: Untyped (n + 1)): Untyped n
  | exists_ (A: Untyped n) (φ: Untyped (n + 1)): Untyped n
  | eq (A: Untyped n) (e: Untyped n) (e': Untyped n): Untyped n

  -- Terms
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

@[simp] def Fin.succ: Fin n -> Fin (Nat.succ n)
  | Fin.mk m p => Fin.mk (Nat.succ m) (Nat.lt_succ_of_le p)

@[simp] def Fin.zero: Fin (Nat.succ n) := Fin.mk 0 (Nat.zero_lt_succ _)

def wk (ρ: Wk n m): Untyped m -> Untyped n

  -- Variables
  | Untyped.var m => Untyped.var (Wk.var ρ m)

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
  | Untyped.lam A e => Untyped.lam (wk ρ A) (wk (Wk.lift ρ) e)
  | Untyped.app l r => Untyped.app (wk ρ l) (wk ρ r)
  | Untyped.pair l r => Untyped.pair (wk ρ l) (wk ρ r)
  | Untyped.proj b e => Untyped.proj b (wk ρ e)
  | Untyped.inj b e => Untyped.inj b (wk ρ e)
  | Untyped.case e l r => Untyped.case (wk ρ e) (wk ρ l) (wk ρ r)
  | Untyped.mkset e p => Untyped.mkset (wk ρ e) (wk ρ p)
  | Untyped.letset e => Untyped.letset (wk (Wk.liftn 2 ρ) e)
  | Untyped.lam_pr φ e => Untyped.lam_pr (wk ρ φ) (wk (Wk.lift ρ) e)
  | Untyped.app_pr φ e => Untyped.app_pr (wk ρ φ) (wk ρ e)
  | Untyped.lam_irrel l r => Untyped.lam_irrel (wk ρ l) (wk (Wk.lift ρ) r)
  | Untyped.app_irrel l r => Untyped.app_irrel (wk ρ l) (wk ρ r)
  | Untyped.repr l r => Untyped.repr (wk ρ l) (wk ρ r)
  | Untyped.let_repr e => Untyped.let_repr (wk (Wk.liftn 2 ρ) e)

  -- Proofs
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
  | Untyped.let_wit p => Untyped.let_wit (wk (Wk.liftn 2 ρ) p)
  | Untyped.refl e => Untyped.refl (wk ρ e)

--TODO: shorten...
@[simp] theorem wk_comp (ρ: Wk n m) (σ: Wk m l): (u: Untyped l) -> wk ρ (wk σ u) = wk (Wk.comp ρ σ) u
  
  -- Variables
  | Untyped.var _ => by simp [wk]
  
  -- Types
  | Untyped.nat => rfl
  | Untyped.pi A B => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }
  | Untyped.sigma A B => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }
  | Untyped.coprod A B => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }
  | Untyped.set A B => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }
  | Untyped.assume φ A => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }
  | Untyped.intersect A B => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }
  | Untyped.union A B => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }

  -- Propositions
  | Untyped.top => rfl
  | Untyped.bot => rfl
  | Untyped.and φ ψ => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.or φ ψ => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.implies φ ψ => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.forall_ A φ => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.exists_ A φ => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.eq A l r => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  
  -- Terms
  | Untyped.lam A e => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.app l r => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.pair l r => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.proj b e => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.inj b e => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.case e l r => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.mkset e p => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.letset e => by { simp only [wk, Wk.liftn]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.lam_pr φ e => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.app_pr φ e => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.lam_irrel l r => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.app_irrel l r => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.repr l r => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.let_repr e => by { simp only [wk, Wk.liftn]; simp only [wk_comp, wk_lift_comp] }  

  -- Proofs
  | Untyped.nil => rfl
  | Untyped.abort p => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.conj l r => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.comp b p => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.disj b p => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.case_pr p l r => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.imp φ p => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.mp l r => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.general A p => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.inst p e => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.witness e p => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.let_wit p => by { simp only [wk, Wk.liftn]; simp only [wk_comp, wk_lift_comp] }  
  | Untyped.refl e => by { simp only [wk]; simp only [wk_comp, wk_lift_comp] }  

def Subst (m: Nat) (n: Nat): Type 0 := Fin n -> Untyped m

@[simp] def Subst.head (σ: Subst m (Nat.succ n)): Untyped m := σ Fin.zero

def Subst.tail (σ: Subst m (Nat.succ n)): Subst m n :=  λv => σ (Fin.succ v)

def Subst.id: Subst n n := Untyped.var

def Subst.wk1 (σ: Subst m n): Subst (m + 1) n := λ x => wk Wk.wk1 (σ x)

def Subst.lift (σ: Subst m n): Subst (m + 1) (n + 1)
  | Fin.mk 0 p => Untyped.var Fin.zero
  | Fin.mk (Nat.succ n) p => Subst.wk1 σ (Fin.mk n (Nat.lt_of_succ_lt_succ p))

@[simp] def Subst.liftn: (l: Nat) -> Subst m n -> Subst (m + l) (n + l)
  | 0, σ => σ
  | Nat.succ n, σ => Subst.lift (liftn n σ)

def toSubst (ρ: Wk m n): Subst m n := λv => Untyped.var (Wk.var ρ v)

instance {m n: Nat}: Coe (Wk m n) (Subst m n) where
  coe w := toSubst w

@[simp] def Subst.cons (σ: Subst m n) (t: Untyped m): Subst m (n + 1)
  | (Fin.mk 0 _) => t
  | (Fin.mk (Nat.succ n) p) => σ (Fin.mk n (Nat.lt_of_succ_lt_succ p))

@[simp] def Subst.sg: Untyped n -> Subst n (n + 1) := Subst.cons Subst.id

@[simp] def subst (σ: Subst m n): Untyped n -> Untyped m

  -- Variables
  | Untyped.var v => σ v

  -- Types
  | Untyped.nat => Untyped.nat
  | Untyped.pi A B => Untyped.pi (subst σ A) (subst (Subst.lift σ) B)
  | Untyped.sigma A B => Untyped.sigma (subst σ A) (subst (Subst.lift σ) B)
  | Untyped.coprod A B => Untyped.coprod (subst σ A) (subst σ B)
  | Untyped.set A φ => Untyped.set (subst σ A) (subst (Subst.lift σ) φ)
  | Untyped.assume φ A => Untyped.assume (subst σ φ) (subst σ A)
  | Untyped.intersect A B => Untyped.intersect (subst σ A) (subst (Subst.lift σ) B)
  | Untyped.union A B => Untyped.union (subst σ A) (subst (Subst.lift σ) B)

  -- Propositions
  | Untyped.top => Untyped.top
  | Untyped.bot => Untyped.bot
  | Untyped.and φ ψ => Untyped.and (subst σ φ) (subst σ ψ)
  | Untyped.or φ ψ => Untyped.or (subst σ φ) (subst σ ψ)
  | Untyped.implies φ ψ => Untyped.implies (subst σ φ) (subst σ ψ)
  | Untyped.forall_ A φ => Untyped.forall_ (subst σ A) (subst (Subst.lift σ) φ)
  | Untyped.exists_ A φ => Untyped.exists_ (subst σ A) (subst (Subst.lift σ) φ)
  | Untyped.eq A l r => Untyped.eq (subst σ A) (subst σ l) (subst σ r)
  
  -- Terms
  | Untyped.lam A e => Untyped.lam (subst σ A) (subst (Subst.lift σ) e)
  | Untyped.app l r => Untyped.app (subst σ l) (subst σ r)
  | Untyped.pair l r => Untyped.pair (subst σ l) (subst σ r)
  | Untyped.proj b e => Untyped.proj b (subst σ e)
  | Untyped.inj b e => Untyped.inj b (subst σ e)
  | Untyped.case e l r => Untyped.case (subst σ e) (subst σ l) (subst σ r)
  | Untyped.mkset e p => Untyped.mkset (subst σ e) (subst σ p)
  | Untyped.letset e => Untyped.letset (subst (Subst.liftn 2 σ) e)
  | Untyped.lam_pr φ e => Untyped.lam_pr (subst σ φ) (subst (Subst.lift σ) e)
  | Untyped.app_pr φ e => Untyped.app_pr (subst σ φ) (subst σ e)
  | Untyped.lam_irrel l r => Untyped.lam_irrel (subst σ l) (subst (Subst.lift σ) r)
  | Untyped.app_irrel l r => Untyped.app_irrel (subst σ l) (subst σ r)
  | Untyped.repr l r => Untyped.repr (subst σ l) (subst σ r)
  | Untyped.let_repr e => Untyped.let_repr (subst (Subst.liftn 2 σ) e)

  -- Proofs
  | Untyped.nil => Untyped.nil
  | Untyped.abort p => Untyped.abort (subst σ p)
  | Untyped.conj l r => Untyped.conj (subst σ l) (subst σ r)
  | Untyped.comp b p => Untyped.comp b (subst σ p)
  | Untyped.disj b p => Untyped.disj b (subst σ p)
  | Untyped.case_pr p l r => Untyped.case_pr (subst σ p) (subst σ l) (subst σ r)
  | Untyped.imp φ p => Untyped.imp (subst σ φ) (subst (Subst.lift σ) p)
  | Untyped.mp l r => Untyped.mp (subst σ l) (subst σ r)
  | Untyped.general A p => Untyped.general (subst σ A) (subst (Subst.lift σ) p)
  | Untyped.inst p e => Untyped.inst (subst σ p) (subst σ e)
  | Untyped.witness e p => Untyped.witness (subst σ e) (subst σ p)
  | Untyped.let_wit p => Untyped.let_wit (subst (Subst.liftn 2 σ) p)
  | Untyped.refl e => Untyped.refl (subst σ e)

def Subst.comp (σ: Subst l m) (τ: Subst m n): Subst l n :=
  λv => subst σ (τ v)

theorem subst_wk_inner_lift (ρ: Wk n m): (v: Fin (m + 1)) -> 
  Subst.lift (toSubst ρ) v = toSubst (Wk.lift ρ) v := sorry
  
@[simp] theorem subst_wk_lift (ρ: Wk n m):
  Subst.lift (toSubst ρ) = toSubst (Wk.lift ρ) := by {
    funext v;
    simp only [subst_wk_inner_lift]
  }

@[simp] theorem subst_wk_inner (ρ: Wk n m): (u: Untyped m) -> subst ρ u = wk ρ u
  -- Variables
  | Untyped.var _ => by simp [subst, wk, toSubst]
  
  -- Types
  | Untyped.nat => rfl
  | Untyped.pi A B => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }  
  | Untyped.sigma A B => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }  
  | Untyped.coprod A B => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }  
  | Untyped.set A B => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }  
  | Untyped.assume φ A => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }  
  | Untyped.intersect A B => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }  
  | Untyped.union A B => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }  

  -- Propositions
  | Untyped.top => rfl
  | Untyped.bot => rfl
  | Untyped.and φ ψ => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.or φ ψ => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.implies φ ψ => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.forall_ A φ => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.exists_ A φ => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.eq A l r => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  
  -- Terms
  | Untyped.lam A e => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.app l r => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.pair l r => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.proj b e => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.inj b e => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.case e l r => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.mkset e p => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }  
  | Untyped.letset e => by { simp only [subst, Subst.liftn]; simp only [Wk.liftn, subst_wk_lift, wk, subst_wk_inner] }  
  | Untyped.lam_pr φ e => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.app_pr φ e => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.lam_irrel l r => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.app_irrel l r => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.repr l r => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.let_repr e => by { simp only [subst, Subst.liftn]; simp only [Wk.liftn, subst_wk_lift, wk, subst_wk_inner] }  

  -- Proofs
  | Untyped.nil => rfl
  | Untyped.abort p => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.conj l r => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.comp b p => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.disj b p => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.case_pr p l r => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.imp φ p => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.mp l r => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.general A p => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.inst p e => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.witness e p => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    
  | Untyped.let_wit p => by { simp only [subst, Subst.liftn]; simp only [Wk.liftn, subst_wk_lift, wk, subst_wk_inner] }  
  | Untyped.refl e => by { simp only [subst]; simp only [subst_wk_lift, wk, subst_wk_inner] }    

@[simp] theorem subst_lift_comp (σ: Subst n m) (τ: Subst m l):
  Subst.comp (Subst.lift σ) (Subst.lift τ) = Subst.lift (Subst.comp σ τ) := by {
    funext (Fin.mk v p);
    cases v with
    | zero => simp [Subst.lift, Subst.comp]
    | succ v => 
      simp [Subst.lift, Subst.comp]
      sorry
  }

--TODO: shorten...
@[simp] theorem subst_comp (σ: Subst n m) (τ: Subst m l): (u: Untyped l) -> 
  subst σ (subst τ u) = subst (Subst.comp σ τ) u
  -- Variables
  | Untyped.var _ => by simp [Subst.comp, subst]
  
  -- Types
  | Untyped.nat => rfl
  | Untyped.pi A B => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }
  | Untyped.sigma A B => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }
  | Untyped.coprod A B => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }
  | Untyped.set A B => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }
  | Untyped.assume φ A => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }
  | Untyped.intersect A B => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }
  | Untyped.union A B => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }

  -- Propositions
  | Untyped.top => rfl
  | Untyped.bot => rfl
  | Untyped.and φ ψ => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.or φ ψ => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.implies φ ψ => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.forall_ A φ => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.exists_ A φ => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.eq A l r => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  
  -- Terms
  | Untyped.lam A e => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.app l r => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.pair l r => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.proj b e => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.inj b e => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.case e l r => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.mkset e p => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.letset e => by { simp only [subst, Subst.liftn]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.lam_pr φ e => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.app_pr φ e => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.lam_irrel l r => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.app_irrel l r => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.repr l r => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.let_repr e => by { simp only [subst, Subst.liftn]; simp only [subst_comp, subst_lift_comp] }  

  -- Proofs
  | Untyped.nil => rfl
  | Untyped.abort p => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.conj l r => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.comp b p => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.disj b p => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.case_pr p l r => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.imp φ p => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.mp l r => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.general A p => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.inst p e => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.witness e p => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.let_wit p => by { simp only [subst, Subst.liftn]; simp only [subst_comp, subst_lift_comp] }  
  | Untyped.refl e => by { simp only [subst]; simp only [subst_comp, subst_lift_comp] }  