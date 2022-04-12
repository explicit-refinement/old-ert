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

  all_goals (
    constructor; 
    first 
    | assumption 
    | (constructor <;> (
        first 
        | assumption 
        | ( apply Annot.regular_expr; assumption )
        | skip
      ))
    | skip
  )

  case app A B l r HP Hl Hr Is IP IA =>
    apply subst_sort
    cases HP <;> assumption
    intro n A k;
    exact Hr.to_subst

  case app_pr A B l r HP Hl Hr Is IP IA =>
    apply subst_sort
    cases HP <;> assumption
    intro n A k;
    exact Hr.to_subst
    
    
  case app_irrel A B l r HP Hl Hr Is IP IA =>
    apply HasType.downgrade
    apply subst_sort
    cases HP <;> assumption
    intro n A k Hv;
    apply Hr.to_subst
    apply Hv.sub
    constructor
    apply Context.is_sub.upgrade
    repeat constructor

  repeat sorry
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