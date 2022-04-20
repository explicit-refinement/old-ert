import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.InterpWk
import LogicalRefinement.Stlc.Subst

def Subst.stlc (σ: Subst) (Γ: Sparsity) (Δ: Sparsity): Stlc.Subst := 
  λv => (σ (Δ.ix_inv v)).stlc Γ

theorem Subst.stlc_lift_true {σ: Subst} {Γ Δ: Sparsity}
  : σ.lift.stlc (true::Γ) (true::Δ) = (σ.stlc Γ Δ).lift
  := by {
    funext v;
    cases v with
    | zero => rfl
    | succ v => exact Term.stlc_wk1_true
  }

theorem Subst.stlc_lift_false {σ: Subst} {Γ: Sparsity}
  : σ.lift.stlc (false::Γ) (false::Δ) = σ.stlc Γ Δ
  := by {
    funext v;
    cases v with
    | zero => exact Term.stlc_wk1_false
    | succ v => exact Term.stlc_wk1_false
  }

theorem SubstCtx.stlc {σ Γ Δ} (S: SubstCtx σ Γ Δ) (HΔ: IsCtx Δ)
  : Stlc.SubstCtx (σ.stlc Γ.sparsity Δ.sparsity) Γ.stlc Δ.stlc
  := by {
    intro n A Hv;
    simp only [Subst.stlc]
    have ⟨A', Hv', HA', HΔA'⟩: ∃A', 
      (HasVar Δ (Δ.sparsity.ix_inv n) (HypKind.val AnnotSort.type) A') 
      ∧ ((Annot.expr AnnotSort.type (A'.subst σ)).stlc_ty = A) 
      ∧ (Δ ⊢ A': AnnotSort.type)
      := by {
        induction Δ generalizing n A with
        | nil => cases Hv
        | cons H Δ I =>
          cases H with
          | mk H k => 
            cases k with
            | val s =>
              cases s with
              | type => 
                rw [Context.sparsity_true]
                {
                  cases Hv with
                  | zero => 
                    exists H.wk1;
                    apply And.intro
                    . exact HasVar.zero (by constructor)
                    . apply And.intro
                      . simp only [Annot.stlc_ty]
                        rw [HasType.stlc_ty_subst]
                        rw [Term.stlc_ty_wk1]
                        apply HasType.wk1_sort
                        exact Hyp.unit
                        cases HΔ; 
                        assumption
                      . sorry
                  | succ Hv => sorry
                }
                rfl
              | prop => sorry
            | gst => sorry
      };
    rw [<-HA']
    apply HasType.stlc;
    exact S.subst_var HΔA' Hv'
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
