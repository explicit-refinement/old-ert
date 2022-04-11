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
    induction H generalizing s Γ with
    | pi HA HB IA IB => 
      intro HΓΔ Hs;
      rw [<-Hs]
      constructor
      apply IA
      assumption
      rfl
      apply IB
      constructor
      assumption
      constructor
      constructor
      rfl
    | sigma HA HB IA IB => 
      intro HΓΔ Hs;
      rw [<-Hs]
      constructor
      apply IA
      assumption
      rfl
      apply IB
      constructor
      assumption
      constructor
      constructor
      rfl
    | coprod HA HB IA IB => 
      intro HΓΔ Hs;
      rw [<-Hs]
      constructor
      apply IA
      assumption
      rfl
      apply IB
      assumption
      rfl
    | set HA HB IA IB => 
      intro HΓΔ Hs;
      rw [<-Hs]
      constructor
      apply IA
      assumption
      rfl
      apply IB
      constructor
      assumption
      constructor
      constructor
      rfl
    | assume HA HB IA IB =>
      intro HΓΔ Hs;
      rw [<-Hs]
      constructor
      apply IA
      assumption
      rfl
      apply IB
      constructor
      assumption
      constructor
      constructor
      rfl
    | intersect HA HB IA IB => 
      intro HΓΔ Hs;
      rw [<-Hs]
      constructor
      apply IA
      assumption
      rfl
      apply IB
      constructor
      assumption
      constructor
      constructor
      rfl
    | union HA HB IA IB => 
      intro HΓΔ Hs;
      rw [<-Hs]
      constructor
      apply IA
      assumption
      rfl
      apply IB
      constructor
      assumption
      constructor
      constructor
      rfl
    | dand HA HB IA IB => 
      intro HΓΔ Hs;
      rw [<-Hs]
      constructor
      apply IA
      assumption
      rfl
      apply IB
      constructor
      assumption
      constructor
      constructor
      rfl
    | or HA HB IA IB => 
      intro HΓΔ Hs;
      rw [<-Hs]
      constructor
      apply IA
      assumption
      rfl
      apply IB
      assumption
      rfl
    | dimplies HA HB IA IB => 
      intro HΓΔ Hs;
      rw [<-Hs]
      constructor
      apply IA
      assumption
      rfl
      apply IB
      constructor
      assumption
      constructor
      constructor
      rfl
    | forall_ HA HB IA IB => 
      intro HΓΔ Hs;
      rw [<-Hs]
      constructor
      apply IA
      assumption
      rfl
      apply IB
      constructor
      assumption
      constructor
      constructor
      rfl
    | exists_ HA HB IA IB => 
      intro HΓΔ Hs;
      rw [<-Hs]
      constructor
      apply IA
      assumption
      rfl
      apply IB
      constructor
      assumption
      constructor
      constructor
      rfl
    | eq => sorry
    | _ => intro HΓΔ Hs; first | contradiction | (repeat rw [<-Hs]; constructor)
  }

theorem HasType.downgrade {Γ: Context} {A s} (H: Γ.upgrade ⊢ A: sort s): Γ ⊢ A: sort s
  := H.downgrade_helper Context.is_sub.upgrade rfl