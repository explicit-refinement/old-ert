import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.Subst

def Subst.stlc (σ: Subst): Stlc.Subst := 
  λv => (σ v).stlc

theorem SubstCtx.stlc {σ Γ Δ} (S: SubstCtx σ Γ Δ)
  : Stlc.SubstCtx σ.stlc Γ.stlc Δ.stlc
  := by {
    intro n A Hv;
    simp only [Subst.stlc]
    sorry
  }

-- But why...
set_option maxHeartbeats 1000000

theorem Term.subst_stlc_commute {σ a} (H: HasType Γ a A)
  : (a.subst σ).stlc = a.stlc.subst σ.stlc
  := by {
    revert σ;
    induction H with
    | lam => sorry
    | app => sorry
    | pair => sorry
    | let_pair => sorry
    | inj_l => sorry
    | inj_r => sorry
    | case => sorry
    | elem => sorry
    | let_set => sorry
    | lam_pr => sorry
    | app_pr => sorry
    | lam_irrel => sorry
    | app_irrel => sorry
    | repr => sorry
    | let_repr => sorry
    | natrec => sorry
    | _ => 
      intro σ;
      rfl
  }