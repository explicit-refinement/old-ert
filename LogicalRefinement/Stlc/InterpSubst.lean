import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.InterpWk
import LogicalRefinement.Stlc.InterpInv
import LogicalRefinement.Stlc.Subst
open Annot
open AnnotSort

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
    have ⟨A', Hv', HA', HΔA'⟩ := Hv.interp_inv HΔ;
    rw [<-HA']
    rw [<-Annot.stlc_ty_subst HΔA']
    apply HasType.stlc;
    exact S.subst_var HΔA' Hv'
  }

-- TODO: this can probably be simplified to a sparsity-respecting 
-- condition on terms. Would clean things up a little, but for now
-- probably not worth the effort.
set_option maxHeartbeats 1000000

theorem Term.subst_stlc_commute {Γ Δ σ a} 
  (H: Δ ⊢ a: term A) 
  (S: SubstCtx σ Γ Δ)
  : (a.subst σ).stlc Γ.sparsity 
  = (a.stlc Δ.sparsity).subst (σ.stlc Γ.sparsity Δ.sparsity)
  := by {
    induction a generalizing σ Γ Δ A;
    case var v => 
      stop
      rw [Term.stlc_var]
      simp only [subst, Subst.stlc, Stlc.subst]
      --TODO: Sparsity.stlc is var since var is term
      --TODO: ix_inv ix is original, again since var is term
      sorry
    case const k => cases k <;> rfl
    case unary k t I => 
      stop
      cases k with
      | inj => 
        have ⟨B, HB⟩: ∃B, Δ ⊢ t: term B 
          := by cases H <;> exact ⟨_, by assumption⟩;
        simp only [stlc, Stlc.subst, I HB S]
      | _ => rfl
    case let_bin k e e' => sorry
    case bin k l r => sorry
    case abs k X t => sorry
    case tri k X l r => sorry
    case cases k K d l r => sorry
    case natrec k K e z s IK Ie Iz Is => 
      have Is': ∀ A Γ Δ G D σ, 
        (Δ ⊢ s: term A) -> 
        SubstCtx σ Γ Δ ->
        G = Γ.sparsity ->
        D = Δ.sparsity ->
        stlc (subst s σ) G =
        Stlc.subst (stlc s D) (Subst.stlc σ G D) := by {
          intro A Γ Δ G D σ HΔ S HG HD;
          rw [HG];
          rw [HD];
          apply Is <;> assumption
        };
      cases H;
      case natrec He Hz HK Hs => 
        conv =>
          congr
          . reduce
            congr
            . rw [HK.stlc_ty_subst]
            . rw [Ie He S]
            . rw [Iz Hz S]
            . {
                reduce
                  rw [Is']
              }
          . skip
        stop
        simp only [stlc, Stlc.subst]
        save
        rw [if_pos True.intro]
  }

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
