import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.Subst

def Subst.stlc (σ: Subst): Stlc.Subst := sorry

theorem SubstCtx.stlc {σ Γ Δ} (S: SubstCtx σ Γ Δ)
  : Stlc.SubstCtx σ.stlc Γ.stlc Δ.stlc
  := sorry

theorem Term.subst_stlc_commute {σ: Subst} {a: Term}
  : (a.subst σ).stlc = a.stlc.subst σ.stlc
  := sorry