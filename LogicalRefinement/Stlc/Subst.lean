import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp

def Stlc.SubstCtx.interp {σ: Subst} {Γ Δ: Context} (S: SubstCtx σ Γ Δ)
  : ∀{n A}, Stlc.HasVar Δ n A -> Γ.interp -> A.interp
  := sorry
  
-- def Stlc.HasType.subst_interp {σ Γ Δ a A} 
--   (H: HasType Δ a A) 
--   (S: SubstCtx σ Γ Δ):
--   (H.subst S).interp = ...
