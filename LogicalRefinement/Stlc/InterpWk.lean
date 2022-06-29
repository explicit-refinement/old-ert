import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.InterpSubst
import LogicalRefinement.Stlc.Subst
open Annot
open AnnotSort

theorem Term.wk_stlc_commute {Γ Δ ρ a} 
  (H: Δ ⊢ a: term A) 
  (R: WkCtx ρ Γ Δ)
  : (a.wk ρ).stlc
  = a.stlc.wk ρ
  := by {
    rw [<-Subst.subst_wk_compat]
    --TODO: this rw [<-Stlc.Subst.subst_wk_compat]
    --apply Term.term_subst_stlc_commute H R.to_subst
    sorry
  }