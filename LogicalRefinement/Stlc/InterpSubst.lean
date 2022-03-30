import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.Subst

def Subst.stlc (σ: Subst): Stlc.Subst := 
  λv => (σ v).stlc

def Subst.stlc_lift {σ: Subst}
  : σ.lift.stlc = σ.stlc.lift
  := sorry

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
    | let_pair He HA HB HC He' Ie IA IB IC Ie' =>
      intros;
      simp only [
        stlc, Stlc.subst, HasType.stlc_ty_subst (by assumption), 
        Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
        *
      ]
    | elem Hl Hr Il Ir => sorry
    | let_set => sorry
    | lam_pr Hs HA Is IA => sorry
    | app_pr HP Hl Hr IP Il Ir => sorry
    | lam_irrel Hs HA Is IA => sorry
    | app_irrel HP Hl Hr IP Il Ir  => sorry
    | repr Hl Hr Il Ir => sorry
    | let_repr => sorry
    | natrec => sorry
    | _ => 
      intros;
      simp only [
        stlc, Stlc.subst, 
        Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
        *
      ]
      repeat rw [HasType.stlc_ty_subst]
      repeat first | assumption | rfl | constructor <;> assumption
  }