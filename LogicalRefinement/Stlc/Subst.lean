import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp

def Stlc.Subst.interp (σ: Subst) (Δ: Context): Type :=  
  ∀{n A}, Stlc.HasVar Δ n A -> A.interp