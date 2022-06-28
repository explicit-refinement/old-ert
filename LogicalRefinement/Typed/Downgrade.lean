import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Wk
import LogicalRefinement.Typed.Subst
open Term
open Annot
open AnnotSort

set_option maxHeartbeats 10000000

theorem HasType.downgrade_helper {Δ Γ: Context} {a A s}
  : (Δ ⊢ a: A) -> (Γ.is_sub Δ) -> (A = sort s) -> Γ ⊢ a: sort s
  := by {
    intro H;
    induction H generalizing s Γ;
    case eq _ Hl Hr IA _ _ => 
      intro HΓΔ Hs;
      rw [<-Hs]
      rw [<-HΓΔ.upgrade_eq] at Hl
      rw [<-HΓΔ.upgrade_eq] at Hr
      exact HasType.eq (IA HΓΔ rfl) Hl Hr
    
    all_goals (
      intro HΓΔ Hs; 
      first | contradiction | (
        rw [<-Hs]
        rename_i' HA HB IA IB;
        constructor <;> (
          first 
          | exact IA HΓΔ rfl
          | (
            apply IB
            repeat constructor
            try assumption
            repeat constructor
            try rfl
          )
        )
      )
    )
  }

theorem HasType.downgrade {Γ: Context} {A s} (H: Γ.upgrade ⊢ A: sort s): Γ ⊢ A: sort s
  := H.downgrade_helper Context.is_sub.upgrade rfl