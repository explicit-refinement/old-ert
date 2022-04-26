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
    dsimp only [Subst.stlc]
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
    have loosen: ∀{l}, (
      ∀ {A Γ Δ σ},
      (Δ ⊢ l: term A) ->
      SubstCtx σ Γ Δ ->
      (l.subst σ).stlc Γ.sparsity =
      (l.stlc Δ.sparsity).subst (σ.stlc Γ.sparsity Δ.sparsity)
    ) -> ∀ {A Γ Δ σ},
      (Δ ⊢ l: term A) ->
      SubstCtx σ Γ Δ ->
      ∀SΓ SΔ,
      SΓ = Γ.sparsity ->
      SΔ = Δ.sparsity ->
      (l.subst σ).stlc SΓ =
      (l.stlc SΔ).subst (σ.stlc SΓ SΔ) := by {
        intros l Il A Γ Δ σ HΔ S SΓ SΔ HSΓ HSΔ;
        rw [HSΓ, HSΔ];
        exact Il HΔ S
      }
    induction a generalizing σ Γ Δ A;
    case var v => 
      rw [Term.stlc_var]
      dsimp only [subst, Subst.stlc]
      --TODO: Sparsity.stlc is var since var is term
      --TODO: ix_inv ix is original, again since var is term
      sorry
    case const k => cases k <;> rfl
    case unary k t I => 
      --TODO: change to cases h?
      cases k with
      | inj => 
        have ⟨B, HB⟩: ∃B, Δ ⊢ t: term B 
          := by cases H <;> exact ⟨_, by assumption⟩;
        dsimp only [stlc, Stlc.subst]
        rw [I HB S]
      | _ => rfl
    case let_bin k C e e' IC Ie Ie' => 
      cases H with
      | let_pair =>
        dsimp only [stlc, Stlc.subst]
        conv =>
          lhs
          congr
          . skip
          . skip
          . skip
        sorry
      | let_set =>
        dsimp only [stlc, Stlc.subst]
        conv =>
          lhs
          congr
          . skip
          . skip
          . skip
        sorry
      | let_repr =>
        dsimp only [stlc, Stlc.subst]
        conv =>
          lhs
          congr
          . skip
          . skip
          . skip
        sorry
    case bin k l r Il Ir => 
      cases H with
      | pair HP Hl Hr => 
        dsimp only [stlc, Stlc.subst]
        conv =>
          lhs
          congr
          . rw [Il Hl S]
          . rw [Ir Hr S]
      | elem HP Hl Hr => 
        dsimp only [stlc, Stlc.subst]
        rw [Il Hl S]
      | repr HP Hl Hr => 
        dsimp only [stlc, Stlc.subst]
        rw [Ir Hr S]
    case abs k X t => 
      cases H with
      | lam => 
        dsimp only [stlc, Stlc.subst]
        conv =>
          lhs
          congr
          . skip
          . skip
        sorry
      | lam_pr => 
        dsimp only [stlc, Stlc.subst]
        sorry
      | lam_irrel => 
        dsimp only [stlc, Stlc.subst]
        sorry
    case tri k X l r IX Il Ir => 
      cases H with
      | app HAB Hl Hr => 
        dsimp only [stlc, Stlc.subst]
        conv =>
          lhs
          congr
          . rw [HAB.stlc_ty_subst]
          . rw [Il Hl S]
          . rw [Ir Hr S]
      | app_pr HAB Hl Hr => 
        dsimp only [stlc, Stlc.subst]
        rw [Il Hl S]
      | app_irrel HAB Hl Hr => 
        dsimp only [stlc, Stlc.subst]
        rw [Il Hl S]
    case cases k C d l r IC Id Il Ir => 
      cases H with
      | case Hd HA HB HC Hl Hr => 
        rename_i A B C;
        have SA 
          : SubstCtx σ.lift ((Hyp.val A type)::Γ) ((Hyp.val A type)::Δ)
          := sorry;
        have SB 
          : SubstCtx σ.lift ((Hyp.val B type)::Γ) ((Hyp.val B type)::Δ)
          := sorry;
        dsimp only [stlc, Stlc.subst]
        conv =>
          lhs
          congr
          . rw [(HasType.coprod HA HB).stlc_ty_subst]
          . rw [Id Hd S]
          . rw [loosen Il Hl SA (true::Γ.sparsity) (true::Δ.sparsity)]
            rhs
            rw [Subst.stlc_lift_true]
          . rw [loosen Ir Hr SB (true::Γ.sparsity) (true::Δ.sparsity)]
            rhs
            rw [Subst.stlc_lift_true]
    case natrec k K e z s IK Ie Iz Is => 
      cases H with
      | natrec HK He Hz Hs => 
        let Γ' := (Hyp.gst nats)::Γ;
        let Δ' := (Hyp.gst nats)::Δ;
        have S': SubstCtx σ.lift Γ' Δ'
          := S.lift_primitive (by constructor) (by constructor)
        let Γ'' := (Hyp.val (K.subst σ.lift) type)::Γ';
        let Δ'' := (Hyp.val K type)::Δ';
        -- BUG?: why is it that if the `by exact` is removed for argument 2, 
        -- there's an error? (2022-04-26, 16:34)
        have S'': SubstCtx σ.lift.lift Γ'' Δ''
          := S'.lift_primitive (by constructor) (by exact HK.subst S');
        have Is'' := 
          loosen Is Hs S'' 
          (true::false::Γ.sparsity) (true::false::Δ.sparsity);
        dsimp only [subst, stlc, Stlc.subst, Subst.liftn]
        simp only [if_pos True.intro]
        conv =>
          lhs
          congr
          . rw [HK.stlc_ty_subst]
          . rw [Ie He S]
          . rw [Iz Hz S]
          . rw [Is'']
            rhs
            rw [Subst.stlc_lift_true]
            rw [Subst.stlc_lift_false]
  }