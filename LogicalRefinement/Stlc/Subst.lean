import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp

def Stlc.InterpSubst (Γ Δ: Context): Type := Γ.interp -> Δ.interp

def Stlc.InterpSubst.subst {Γ Δ: Context} (S: InterpSubst Γ Δ):
  ∀{A}, Δ.deriv A -> Γ.deriv A
  := λD G => D (S G)

def Stlc.SubstCtx.interp {σ: Subst} {Γ Δ: Context} (S: SubstCtx σ Γ Δ)
  : InterpSubst Γ Δ
  := sorry
