import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.Subst
import LogicalRefinement.Utils
open Annot
open AnnotSort

def Subst.stlc (σ: Subst): Stlc.Subst := 
  λv => (σ v).stlc

theorem Subst.stlc_lift {σ: Subst} {Γ Δ: Sparsity}
  : σ.lift.stlc = σ.stlc.lift
  := sorry

theorem SubstCtx.stlc {σ Γ Δ} (S: SubstCtx σ Γ Δ) (HΔ: IsCtx Δ)
  : Stlc.SubstCtx σ.stlc Γ.stlc Δ.stlc
  := sorry

theorem Term.term_subst_stlc_commute {Γ Δ σ a} 
  (H: Δ ⊢ a: term A) 
  (S: SubstCtx σ Γ Δ)
  : (a.subst σ).stlc
  = (a.stlc).subst σ.stlc
  := sorry

abbrev SubstCtx.interp {σ Γ Δ} (S: SubstCtx σ Γ Δ) (IΔ: IsCtx Δ)
  : Stlc.InterpSubst Γ.stlc Δ.stlc
  := Stlc.SubstCtx.interp (S.stlc IΔ)

theorem SubstCtx.interp_lift
  {σ: Subst} {Γ Δ: Context} {A s}
  (S: SubstCtx σ Γ Δ)
  (S': 
    SubstCtx σ.lift 
      ({ ty := A.subst σ, kind := HypKind.val s }::Γ) 
      ({ ty := A, kind := HypKind.val s }::Δ))
  (IΔ: IsCtx Δ)
  (HA: Δ ⊢ A: sort s)
  : S'.interp (IsCtx.cons_val IΔ HA) 
  = cast (by simp only [Context.stlc]; rw [HA.stlc_ty_subst])
    (@Stlc.InterpSubst.lift A.stlc_ty Γ.stlc Δ.stlc (S.interp IΔ))
  := by {
    funext n A' Hv G;
    cases G with
    | mk x G =>
      unfold Stlc.InterpSubst;
      rw [
        cast_app_pull_in_dep _ _ _ _ _ 
        (by simp only [Context.stlc]; rw [HA.stlc_ty_subst]) 
        (by simp only [Context.stlc]; rw [HA.stlc_ty_subst]) 
        (by simp only [Context.stlc]; rw [HA.stlc_ty_subst])
      ]
      rw [
          cast_app_pull_in_dep _ _ _ _ _ 
          (by simp only [Context.stlc]; rw [HA.stlc_ty_subst]) 
          (by simp only [Context.stlc]; rw [HA.stlc_ty_subst]) 
          (by simp only [Context.stlc]; rw [HA.stlc_ty_subst])]
      rw [cast_app_pull_in _ _ _]
      cases n with
      | zero =>
        simp only [Stlc.InterpSubst.lift]
        cases Hv;
        rw [cast_lam _ _ _ _ _ _
          (by simp only [Context.stlc]; rw [HA.stlc_ty_subst])]
        rw [
          cast_pair' 
          (by rw [HA.stlc_ty_subst]) 
          rfl _]
        rfl
        intros;
        exact 
          congr 
            (congr rfl (congr (congr rfl HA.stlc_ty_subst.symm) rfl)) 
            rfl;
      | succ n => 
        simp only [Stlc.InterpSubst.lift]
        rw [
          cast_lam _ _ _ _ _ _ 
          (by simp only [Context.stlc]; rw [HA.stlc_ty_subst])]
        cases Hv;
        rw [
          cast_pair' 
          (by rw [HA.stlc_ty_subst])  
          rfl _]
        simp only [
          cast, interp, 
          Stlc.SubstCtx.interp, Stlc.HasType.interp
        ]
        conv =>
          rhs
          rw [<-Stlc.HasType.interp_wk1 _ x]
        apply congr _ rfl;
        apply interp_congr;
        simp [Subst.stlc_lift, Subst.stlc]
        --TODO: fix this...
        sorry
  }

abbrev SubstCtx.interp_up {σ Γ Δ} (S: SubstCtx σ Γ Δ) (IΔ: IsCtx Δ)
  : Stlc.InterpSubst Γ.upgrade.stlc Δ.upgrade.stlc
  := SubstCtx.interp S.upgrade IΔ.upgrade

--TODO: think about this...
theorem SubstCtx.interp_up_char {σ Γ Δ} (S: SubstCtx σ Γ Δ) (IΔ: IsCtx Δ)
  : S.interp_up IΔ = S.upgrade.interp IΔ.upgrade
  := by rfl

abbrev SubstCtx.transport_interp {σ Γ Δ}
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.stlc.interp)
  : Δ.stlc.interp
  := Stlc.InterpSubst.transport_ctx (S.interp IΔ) G

theorem SubstCtx.transport_interp_lift
  {σ: Subst} {Γ Δ: Context} {A s}
  (S: SubstCtx σ Γ Δ)
  (S': 
    SubstCtx σ.lift 
      ({ ty := A.subst σ, kind := HypKind.val s }::Γ) 
      ({ ty := A, kind := HypKind.val s }::Δ))
  (IΔ: IsCtx Δ)
  (HA: Δ ⊢ A: sort s)
  (G: Γ.stlc.interp)
  (x y)
  (p: x = HA.stlc_ty_subst ▸ y)
  : transport_interp S' (IsCtx.cons_val IΔ HA) (y, G)
  = (x, transport_interp S IΔ G)
  := by {
    unfold transport_interp
    simp only [Context.stlc, Stlc.InterpSubst.transport_ctx]
    apply congr;
    {
      apply congr rfl;
      unfold interp;
      unfold Stlc.SubstCtx.interp;
      simp only [
        Stlc.HasType.interp_var, 
        Stlc.HasVar.interp, 
        Sparsity.ix, p, 
        Eq.mp, rec_to_cast'
      ]
    }
    {
      rw [interp_lift S S' IΔ HA]
      --TODO: report broken binding here...
      rw [Stlc.InterpSubst.pop_cast']
      rw [Stlc.InterpSubst.pop_lift_step]
      rw [Stlc.InterpSubst.transport_cast]
      rw [cast_pair']
      rw [Stlc.InterpSubst.transport_step]
      rfl
      rw [HA.stlc_ty_subst]
      rfl
      rw [HA.stlc_ty_subst]
      rw [HA.stlc_ty_subst]
      rfl
      rfl
    }
  }

abbrev SubstCtx.transport_interp_up {σ Γ Δ}
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.upgrade.stlc.interp)
  : Δ.upgrade.stlc.interp
  := transport_interp S.upgrade IΔ.upgrade G

theorem SubstCtx.transport_interp_up_lift
  {σ: Subst} {Γ Δ: Context} {A s}
  (S: SubstCtx σ Γ Δ)
  (S': 
    SubstCtx σ.lift 
      ({ ty := A.subst σ, kind := HypKind.val s }::Γ) 
      ({ ty := A, kind := HypKind.val s }::Δ))
  (IΔ: IsCtx Δ)
  (HA: Δ ⊢ A: sort s)
  (G: Γ.upgrade.stlc.interp)
  (x y)
  (p: x = HA.stlc_ty_subst ▸ y)
  : transport_interp_up S' (IsCtx.cons_val IΔ HA) (y, G)
  = (x, transport_interp_up S IΔ G)
  := by {
    unfold transport_interp_up
    apply transport_interp_lift;
    exact p;
    exact HA.upgrade
  }

theorem HasType.subst_stlc_interp_commute {Γ Δ σ a} 
  (H: Δ ⊢ a: term A) 
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.stlc.interp)
  : (H.subst S).stlc.interp G
  = (Annot.stlc_ty_subst H.expr_regular) ▸ H.stlc.interp.subst (S.interp IΔ) G
  := by {
    rw [<-Stlc.HasType.subst_interp_dist]
    rw [rec_to_cast']
    rw [Stlc.HasType.interp_transport_cast']
    rw [Term.term_subst_stlc_commute]
    assumption
    assumption
    rw [Annot.stlc_ty_subst H.expr_regular]
  }
  
theorem HasType.subst_stlc_interp_up_commute {Γ Δ σ a} 
  (H: Δ.upgrade ⊢ a: term A) 
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.upgrade.stlc.interp)
  : (H.subst S.upgrade).stlc.interp G
  = (Annot.stlc_ty_subst H.expr_regular) ▸ H.stlc.interp.subst (S.interp_up IΔ) G
  := by {
    rw [<-Stlc.HasType.subst_interp_dist]
    rw [rec_to_cast']
    rw [Stlc.HasType.interp_transport_cast']
    rw [Term.term_subst_stlc_commute]
    assumption
    apply SubstCtx.upgrade S;
    rw [Annot.stlc_ty_subst H.expr_regular]
  }

theorem HasType.subst_stlc_interp_commute' {Γ Δ σ a} 
  (H: Δ ⊢ a: term A) 
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.stlc.interp)
  : (Annot.stlc_ty_subst H.expr_regular) ▸ (H.subst S).stlc.interp G
  = H.stlc.interp.subst (S.interp IΔ) G
  := by {
    rw [<-Stlc.HasType.subst_interp_dist]
    rw [rec_to_cast']
    rw [Stlc.HasType.interp_transport_cast']
    rw [Term.term_subst_stlc_commute]
    assumption
    assumption
    rw [Annot.stlc_ty_subst H.expr_regular]
  }
  
theorem HasType.subst_stlc_interp_up_commute' {Γ Δ σ a} 
  (H: Δ.upgrade ⊢ a: term A) 
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.upgrade.stlc.interp)
  : (Annot.stlc_ty_subst H.expr_regular) ▸ (H.subst S.upgrade).stlc.interp G
  = H.stlc.interp.subst (S.interp_up IΔ) G
  := by {
    rw [<-Stlc.HasType.subst_interp_dist]
    rw [rec_to_cast']
    rw [Stlc.HasType.interp_transport_cast']
    rw [Term.term_subst_stlc_commute]
    assumption
    apply SubstCtx.upgrade S;
    rw [Annot.stlc_ty_subst H.expr_regular]
  }