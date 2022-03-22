import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp

def Stlc.Subst.interp (σ: Subst) (Γ Δ: Context): Type :=  
  ∀{n A}, Stlc.HasVar Δ n A -> Γ.interp -> A.interp

def Stlc.SubstCtx.interp {σ: Subst} {Γ Δ: Context} (S: SubstCtx σ Γ Δ)
  : σ.interp Γ Δ
  := sorry