import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.Subst

def Subst.stlc (σ: Subst) (Γ: Sparsity): Stlc.Subst := 
  λv => (σ (Γ.ix_inv v)).stlc Γ

theorem Subst.stlc_lift_true {σ: Subst} {Γ: Sparsity}
  : σ.lift.stlc (true::Γ) = (σ.stlc Γ).lift
  := by {
    funext v;
    cases v with
    | zero => rfl
    | succ v => 
      simp only [stlc, Stlc.Subst.lift, Sparsity.ix_inv, lift_succ, Subst.wk1]
      sorry
  }

theorem Subst.stlc_lift_false {σ: Subst} {Γ: Sparsity}
  : σ.lift.stlc (false::Γ) = σ.stlc Γ
  := sorry

theorem SubstCtx.stlc {σ Γ Δ} (S: SubstCtx σ Γ Δ)
  : Stlc.SubstCtx (σ.stlc Γ.sparsity) Γ.stlc Δ.stlc
  := by {
    intro n A Hv;
    simp only [Subst.stlc]
    sorry
  }

-- -- But why...
-- set_option maxHeartbeats 1000000

-- theorem Term.subst_stlc_commute {σ a} (H: HasType Γ a A)
--   : (a.subst σ).stlc = a.stlc.subst σ.stlc
--   := by {
--     revert σ;
--     induction H with
--     | let_set => 
--       intros;
--       simp only [
--         stlc, Stlc.subst, 
--         Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
--         *
--       ]
--       repeat rw [HasType.stlc_ty_subst]
--       repeat first | assumption | rfl | constructor <;> assumption
--       repeat sorry
--     | lam_pr Hs HA Is IA => 
--       intros;
--       simp only [
--         stlc, Stlc.subst, 
--         Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
--         *
--       ]
--       repeat rw [HasType.stlc_ty_subst]
--       repeat first | assumption | rfl | constructor <;> assumption
--       repeat sorry
--     | lam_irrel Hs HA Is IA => 
--       intros;
--       simp only [
--         stlc, Stlc.subst, 
--         Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
--         *
--       ]
--       repeat rw [HasType.stlc_ty_subst]
--       repeat first | assumption | rfl | constructor <;> assumption
--       repeat sorry
--     | let_repr => 
--       intros;
--       simp only [
--         stlc, Stlc.subst, 
--         Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
--         *
--       ]
--       repeat rw [HasType.stlc_ty_subst]
--       repeat first | assumption | rfl | constructor <;> assumption
--       repeat sorry
--     | natrec => 
--       intros;
--       simp only [
--         stlc, Stlc.subst, 
--         Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
--         *
--       ]
--       repeat rw [HasType.stlc_ty_subst]
--       repeat first | assumption | rfl | constructor <;> assumption
--       repeat sorry
--     | _ => 
--       intros;
--       simp only [
--         stlc, Stlc.subst, 
--         Subst.stlc_lift, Subst.liftn, Stlc.Subst.liftn,
--         *
--       ]
--       repeat rw [HasType.stlc_ty_subst]
--       repeat first | assumption | rfl | constructor <;> assumption
--   }