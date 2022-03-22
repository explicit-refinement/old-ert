import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp

def Stlc.InterpSubst (Γ Δ: Context): Type := 
  ∀{n A}, Stlc.HasVar Δ n A -> Γ.interp -> A.interp

def Stlc.SubstCtx.interp {σ: Subst} {Γ Δ: Context} (S: SubstCtx σ Γ Δ)
  : InterpSubst Γ Δ
  := sorry
  
def Stlc.subst_deriv {Γ Δ: Context} {A}:
  Δ.deriv A -> InterpSubst Γ Δ -> Γ.deriv A
  := sorry
