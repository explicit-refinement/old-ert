import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Wk
import LogicalRefinement.Typed.Subst
import LogicalRefinement.Typed.Downgrade
open Term
open Annot
open AnnotSort

theorem HasType.no_poly {Γ v s}: ¬(HasType Γ (Term.var v) (sort s)) := by {
  intro H; cases H
}

theorem HasType.no_poly_ty {Γ v}: ¬(Γ ⊢ (Term.var v): type) := no_poly

inductive Annot.regular: Annot -> Context -> Prop
  | sort {Γ s}: regular (sort s) Γ
  | expr {Γ s A}: (Γ ⊢ A: sort s) -> regular (expr s A) Γ

def Annot.regular_expr: regular (expr s A) Γ -> (Γ ⊢ A: sort s)
  | Annot.regular.expr Hr => Hr

theorem HasType.regular (p: Γ ⊢ a: A): A.regular Γ := by {
  induction p;

  -- Types and propositions are trivially regular
  all_goals try exact Annot.regular.sort

  case app A B l r HP Hl Hr Is IP IA =>
    constructor
    apply subst_sort
    cases HP <;> assumption
    intro n A k;
    exact Hr.to_subst

  case app_pr A B l r HP Hl Hr Is IP IA =>
    constructor
    apply subst_sort
    cases HP <;> assumption
    intro n A k;
    exact Hr.to_subst

  case lam_irrel _ _ _ IB => 
    constructor
    constructor
    assumption
    cases IB
    apply HasType.sub
    assumption
    constructor
    exact Context.is_sub.refl
    repeat constructor
    
  case app_irrel A B l r HP Hl Hr Is IP IA =>
    constructor
    apply HasType.downgrade
    apply subst_sort
    cases HP <;> assumption
    intro n A k Hv;
    apply Hr.to_subst
    apply Hv.sub
    constructor
    apply Context.is_sub.upgrade
    repeat constructor

  case dconj HD _ _ _ IA IB => 
    constructor
    constructor
    cases IA
    assumption
    cases HD
    assumption

  case mp HM Hl Hr _ _ _ =>
    cases HM with
    | dimplies Hφ Hψ =>
      constructor
      apply HasType.downgrade
      apply HasType.subst0_sort
      exact Hψ.upgrade
      assumption

  case inst Hf Hl Hr If Il Ir => 
    constructor
    apply HasType.downgrade
    apply HasType.subst0_sort
    cases Hf with
    | forall_ HA Hφ => exact Hφ.upgrade
    assumption

  case refl Ha IA =>  
    cases IA;
    constructor
    apply HasType.downgrade
    constructor
    assumption
    apply HasType.upgrade
    assumption
    apply HasType.upgrade
    assumption

  case sym HA IA => 
    cases IA;
    constructor
    apply HasType.sym_ty
    assumption

  case trans HA IA => 
    cases IA;
    constructor
    apply HasType.trans_ty
    assumption

  case cong HP _ _ _ _ Ip => 
    constructor
    constructor
    apply HasType.downgrade
    apply HasType.subst0_sort
    exact HP.upgrade
    cases Ip with
    | expr Ip => cases Ip; assumption
    apply HasType.downgrade
    apply HasType.wk_sort
    apply HasType.subst0_sort
    exact HP.upgrade
    cases Ip with
    | expr Ip => cases Ip; assumption
    repeat constructor

  case beta Hs HA Ht Is IA It => 
    cases Is with
    | expr HB =>
      constructor
      apply HasType.downgrade
      constructor
      exact HB.upgrade.subst0_sort Ht
      constructor
      constructor
      exact HA.upgrade.upgrade
      exact HB.upgrade.upgrade
      constructor
      exact Hs.upgrade.upgrade
      exact HA.upgrade.upgrade
      exact Ht.upgrade
      exact Hs.upgrade.upgrade.subst0 Ht.upgrade

  case eta Γ A B f Hf HA If IA => 
    cases If with
    | expr Hf =>
      cases Hf with
      | pi HA' HB =>
        simp only [eta_ex]
        constructor
        apply HasType.downgrade
        constructor
        constructor
        exact HA'
        exact HB
        constructor
        conv =>
          arg 3
          rw [<-B.subst00_wknth]
        apply HasType.app
        constructor
        exact HA'.upgrade.wk1_sort
        apply HB.wk_sort
        constructor
        constructor
        rw [Context.upgrade_idem]
        constructor
        exact Hf.upgrade.wk1
        constructor
        exact HA'.upgrade.wk1_sort
        constructor
        constructor
        exact HA'.upgrade
        exact Hf.upgrade

  case irir Γ A B f x y Hf Hx Hy If Ix Iy => 
    cases Ix with
    | expr HA =>
      cases If with
      | expr HF =>
        cases HF with
        | intersect HA HB =>
          constructor
          apply HasType.downgrade
          constructor
          rw [<-B.subst0_wk1]
          exact HB.subst0_sort Hx
          conv =>
            arg 3
            rw [<-@Term.subst0_wk1 B x]
          constructor
          exact HA.upgrade.intersect HB.upgrade
          exact Hf.upgrade
          exact Hx.upgrade.upgrade
          conv =>
            arg 3
            rw [<-@Term.subst0_wk1 B y]
          constructor
          exact HA.upgrade.intersect HB.upgrade
          exact Hf.upgrade
          exact Hy.upgrade.upgrade

  case prir => sorry

  case succ => repeat constructor

  case natrec HC Hn Hz Hs IC In Iz Is => 
    constructor
    apply HasType.subst0_sort
    apply HC.sub
    constructor
    apply Context.is_sub.refl
    constructor
    constructor
    assumption

  all_goals (
    constructor; 
    first 
    | assumption 
    | (
      apply subst0_sort
      assumption
      assumption
    )
    | (constructor <;> (
        first 
        | assumption 
        | ( apply Annot.regular_expr; assumption )
      ))
  )
}

theorem HasType.term_regular (p: HasType Γ a (term A)): HasType Γ A type 
  := by {
    let H := regular p;
    cases H with
    | expr H => exact H
  }

theorem HasType.proof_regular (p: HasType Γ a (proof A)): HasType Γ A prop 
  := by {
    let H := regular p;
    cases H with
    | expr H => exact H
  }