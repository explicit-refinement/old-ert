import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.InterpWkUtils
import LogicalRefinement.Stlc.InterpSubst
import LogicalRefinement.Stlc.InterpInv
import LogicalRefinement.Stlc.Subst
open Annot
open AnnotSort

def Wk.stlc (ρ: Wk) (Γ: Sparsity) (Δ: Sparsity): Stlc.Subst := ρ.to_subst.stlc Γ Δ

--TODO: relate Wk.stlc to context operations...

--TODO: WkCtx -> SubstCtx

theorem Term.wk_stlc_commute {Γ Δ ρ a} 
  (H: Δ ⊢ a: term A) 
  (S: WkCtx ρ Γ Δ)
  : (a.wk ρ).stlc Γ.sparsity
  = (a.stlc Δ.sparsity).subst (ρ.stlc Γ.sparsity Δ.sparsity)
  := sorry