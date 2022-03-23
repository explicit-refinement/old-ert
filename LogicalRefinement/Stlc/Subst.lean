import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp

def Stlc.InterpSubst (Γ Δ: Context): Type := 
  ∀{n A}, Stlc.HasVar Δ n A -> Γ.deriv A

def Stlc.SubstCtx.interp {σ: Subst} {Γ Δ: Context} (S: SubstCtx σ Γ Δ)
  : InterpSubst Γ Δ
  := λHv => (S Hv).interp
  
def Stlc.InterpSubst.transport_ctx {Γ Δ: Context} (S: InterpSubst Γ Δ)
  : Γ.interp -> Δ.interp
  := sorry

def Stlc.InterpSubst.subst {Γ Δ: Context} (S: InterpSubst Γ Δ):
  ∀{A}, Δ.deriv A -> Γ.deriv A
  := λD G => D (S.transport_ctx G)