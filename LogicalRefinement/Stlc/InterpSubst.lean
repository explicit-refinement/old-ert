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
    | let_set => 
      intros;
      simp only [
        stlc, Stlc.subst, 
        Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
        *
      ]
      repeat rw [HasType.stlc_ty_subst]
      repeat first | assumption | rfl | constructor <;> assumption
    | lam_pr Hs HA Is IA => 
      intros;
      simp only [
        stlc, Stlc.subst, 
        Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
        *
      ]
      repeat rw [HasType.stlc_ty_subst]
      repeat first | assumption | rfl | constructor <;> assumption
    | lam_irrel Hs HA Is IA => 
      intros;
      simp only [
        stlc, Stlc.subst, 
        Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
        *
      ]
      repeat rw [HasType.stlc_ty_subst]
      repeat first | assumption | rfl | constructor <;> assumption
    | let_repr => 
      intros;
      simp only [
        stlc, Stlc.subst, 
        Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
        *
      ]
      repeat rw [HasType.stlc_ty_subst]
      repeat first | assumption | rfl | constructor <;> assumption
    | natrec => 
      intros;
      simp only [
        stlc, Stlc.subst, 
        Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
        *
      ]
      repeat rw [HasType.stlc_ty_subst]
      repeat first | assumption | rfl | constructor <;> assumption
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