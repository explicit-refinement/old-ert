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

--TODO: report invalid environment extension

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

  case app A B _ r HP _ Hr _ _ _ =>
    constructor
    apply subst_sort'
    cases HP <;> assumption
    intro n A k;
    apply Hr.to_subst'

  case app_pr A B _ r HP _ Hr _ _ _ =>
    constructor
    apply subst_sort'
    cases HP <;> assumption
    intro n A k;
    apply Hr.to_subst'

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
    
  case app_irrel A B _ r HP _ Hr _ _ _ =>
    constructor
    apply HasType.downgrade
    apply subst_sort'
    cases HP <;> assumption
    intro n A k Hv;
    cases k with
    | val s => 
      apply Hr.to_subst'
      rw [HasVar.v_eq]
      exact Hv.v.upgrade
    | gst => 
      apply SubstVar'.wk_sort
      apply Hr.to_subst'
      apply Hv.ghost_up
      constructor

  case dconj HD _ _ _ IA _ => 
    constructor
    constructor
    cases IA
    assumption
    cases HD
    assumption

  case mp HM _ Hr _ _ _ =>
    cases HM with
    | dimplies Hφ Hψ =>
      constructor
      apply HasType.downgrade
      apply HasType.subst0_sort
      exact Hψ.upgrade
      upgrade_ctx assumption

  case inst Hf _ Hr _ _ _ => 
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

  case cong _ _ _ _ _ Ip _ => 
    constructor
    apply HasType.downgrade
    apply HasType.subst0_sort
    upgrade_ctx assumption
    cases Ip with
    | expr Ip => cases Ip; assumption

  -- case trans _ _ _ _ _ Ip _ => 
  --   constructor
  --   apply HasType.downgrade
  --   apply HasType.subst0_sort
  --   upgrade_ctx assumption
  --   cases Ip with
  --   | expr Ip => cases Ip; assumption

  case beta Hs HA Ht Is _ _ => 
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

  case beta_ir Hs HA Ht Is _ _ => 
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
      exact HA.upgrade.upgrade
      upgrade_ctx assumption
      exact Ht.upgrade.upgrade
      exact Hs.upgrade.upgrade.subst0 Ht.upgrade

  case beta_pr Hs Hφ Hp Is _ _  => 
    cases Is with
    | expr HA =>
      constructor
      apply HasType.downgrade
      constructor
      exact HA.upgrade.subst0_sort Hp
      constructor
      constructor
      exact Hφ.upgrade.upgrade
      exact HA.upgrade.upgrade
      constructor
      exact Hφ.upgrade.upgrade
      exact Hs.upgrade.upgrade
      exact Hp.upgrade
      exact Hs.upgrade.upgrade.subst0 Hp.upgrade

  case funext Γ A B f g _ _ Hf Hg _ _ If _ _ => 
    constructor
    apply HasType.downgrade
    constructor
    cases If; assumption
    exact Hf.upgrade
    exact Hg.upgrade

  case irir Γ A B f x y Hf Hx Hy If Ix _ => 
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

  case prir => 
    constructor
    constructor
    apply subst0_sort
    assumption
    assumption
    apply wk1_sort
    apply subst0_sort
    assumption
    assumption

  case beta_left => 
    constructor
    constructor
    apply downgrade
    apply subst0_sort
    upgrade_ctx assumption
    constructor
    assumption
    upgrade_ctx assumption
    constructor
    constructor
    assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    apply subst0_gen
    assumption
    assumption
    rw [Term.alpha0_inj_subst]
    rfl

  case beta_right => 
    constructor
    constructor
    apply downgrade
    apply subst0_sort
    upgrade_ctx assumption
    constructor
    assumption
    upgrade_ctx assumption
    constructor
    constructor
    assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    apply subst0_gen
    assumption
    assumption
    rw [Term.alpha0_inj_subst]
    rfl

  case beta_pair => 
    constructor
    constructor
    apply HasType.downgrade
    apply subst0_sort
    upgrade_ctx assumption
    constructor
    constructor
    upgrade_ctx assumption
    upgrade_ctx assumption
    assumption
    assumption
    constructor
    constructor
    constructor
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    apply subst01_gen;
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    simp only [Annot.subst01, Annot.subst, term]
    apply congr rfl
    exact Term.alpha0_subst01_bin.symm

  case beta_set => 
    constructor
    constructor
    apply HasType.downgrade
    apply subst0_sort
    upgrade_ctx assumption
    constructor
    constructor
    upgrade_ctx assumption
    upgrade_ctx assumption
    assumption
    upgrade_ctx assumption
    constructor
    constructor
    constructor
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    apply subst01_gen;
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    simp only [Annot.subst01, Annot.subst, term]
    apply congr rfl
    exact Term.alpha0_subst01_bin.symm

  case beta_repr => 
    constructor
    constructor
    apply HasType.downgrade
    apply subst0_sort
    upgrade_ctx assumption
    constructor
    constructor
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    constructor
    constructor
    constructor
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    apply subst01_gen;
    upgrade_ctx assumption
    upgrade_ctx assumption
    assumption
    simp only [Annot.subst01, Annot.subst, term]
    apply congr rfl
    exact Term.alpha0_subst01_bin.symm

  case natrec HC Hn _ _ _ _ _ _ => 
    constructor
    apply HasType.subst0_sort
    apply HC.sub
    constructor
    apply Context.is_sub.refl
    constructor
    constructor
    assumption

  case beta_zero => 
    constructor
    constructor
    apply downgrade
    apply subst0_sort
    upgrade_ctx assumption
    constructor
    constructor
    upgrade_ctx assumption
    constructor
    assumption
    upgrade_ctx assumption
    assumption

  case beta_succ => 
    constructor
    constructor
    apply downgrade
    apply subst0_sort
    upgrade_ctx assumption
    focus repeat constructor
    assumption
    constructor
    upgrade_ctx assumption
    focus repeat constructor
    assumption
    assumption
    assumption
    apply subst01_gen_gst;
    assumption
    constructor
    upgrade_ctx assumption
    assumption
    assumption
    assumption
    assumption
    apply congr rfl
    simp only [
      Term.subst01, Term.wknth, Term.alpha0, Term.subst0,
      <-Subst.subst_wk_compat,
      Term.subst_composes
    ]
    apply congr rfl;
    funext n;
    cases n <;> rfl

  case succ => repeat constructor

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

theorem HasType.expr_regular (p: HasType Γ a (expr s A)): HasType Γ A (sort s) 
  := by {
    let H := regular p;
    cases H with
    | expr H => exact H
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