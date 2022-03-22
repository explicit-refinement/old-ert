import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp

def Stlc.InterpSubst (Γ Δ: Context): Type := 
  ∀{n A}, Stlc.HasVar Δ n A -> Γ.interp -> A.interp

def Stlc.SubstCtx.interp {σ: Subst} {Γ Δ: Context} (S: SubstCtx σ Γ Δ)
  : InterpSubst Γ Δ
  := sorry
  
-- def Stlc.HasType.subst_interp {σ Γ Δ a A} 
--   (H: HasType Δ a A) 
--   (S: SubstCtx σ Γ Δ):
--   (H.subst S).interp = ...
