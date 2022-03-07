import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Wk
import LogicalRefinement.Typed.Subst
open Untyped
open Annot
open AnnotSort

inductive Annot.regular: Annot -> Context -> Prop
  | sort {Γ s}: regular (sort s) Γ
  | expr {Γ s A}: (Γ ⊢ A: sort s) -> regular (expr s A) Γ

def Annot.regular_expr: regular (expr s A) Γ -> (Γ ⊢ A: sort s)
  | Annot.regular.expr Hr => Hr

-- theorem HasType.regular (p: Γ ⊢ a: A): A.regular Γ := by {
--   induction p;

--   -- Types and propositions are trivially regular
--   all_goals try exact Annot.regular.sort

--   case lam =>
--     constructor; constructor <;>
--     first | assumption | { apply Annot.regular_expr; assumption }

--   case app =>
--     constructor;
--     apply subst_sort
--     sorry
--     sorry
--     sorry

--   --TODO: general tactic for app requires substitution lemma for subst0

--   repeat sorry
-- }

-- theorem HasType.term_regular (p: HasType Γ a (term A)): HasType Γ A type 
--   := by {
--     let H := regular p;
--     cases H with
--     | expr H => exact H
--   }

-- theorem HasType.proof_regular (p: HasType Γ a (proof A)): HasType Γ A prop 
--   := by {
--     let H := regular p;
--     cases H with
--     | expr H => exact H
--   }