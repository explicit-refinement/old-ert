import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.InterpWk
import LogicalRefinement.Stlc.Subst
import LogicalRefinement.Utils
open Annot
open AnnotSort

def Subst.stlc (σ: Subst): Stlc.Subst := 
  λv => (σ v).stlc

theorem Subst.stlc_lift {σ: Subst}
  : σ.lift.stlc = σ.stlc.lift
  := by {
    funext v;
    cases v with
    | zero => rfl
    | succ v => exact (σ v).wk1_stlc_commute
  }

theorem Stlc.HasVar.interp_inv {Γ: _root_.Context} (H: Stlc.HasVar Γ.stlc n A)
  : ∃A' k, _root_.HasVar Γ n k A' ∧ (Hyp.stlc (Hyp.mk A' k)) = A
  := by {
    generalize HΓ': Γ.stlc = Γ';
    rw [HΓ'] at H;
    induction H generalizing Γ with
    | zero =>
      cases Γ with
      | nil => cases HΓ'
      | cons Hy Γ => 
        cases Hy with
        | mk A' k =>
          exists A'.wk1, k;
          constructor
          constructor
          rw [Context.stlc_hyp] at HΓ'
          cases HΓ'
          cases k <;> simp only [Hyp.stlc, Term.stlc_ty_wk1]
    | succ Hv I =>
      cases Γ with
      | nil => cases HΓ'
      | cons Hy Γ => 
        rw [Context.stlc_hyp] at HΓ'
        cases HΓ';
        have ⟨A', k, Hv', HA⟩ := I rfl;
        exists A'.wk1, k;
        constructor
        constructor
        assumption
        rw [<-HA]
        cases k <;> simp only [Hyp.stlc, Term.stlc_ty_wk1]
  }

theorem SubstCtx.stlc {σ Γ Δ} (S: SubstCtx σ Γ Δ) (HΔ: IsCtx Δ)
  : Stlc.SubstCtx σ.stlc Γ.stlc Δ.stlc
  := by {
    intro n A Hv;
    have ⟨A', k, Hv', HA'⟩ := Hv.interp_inv;
    cases S _ _ _ Hv' with
    | expr E =>
      have E' := E.stlc;
      simp only [Subst.stlc, <-HA', stlc_ty] at *;
      rw [(HΔ.var_valid Hv').stlc_ty_subst] at E'
      exact E'
    | var Hn HA Hg => 
      simp only [Subst.stlc, Hn]
      constructor;
      have Hg' := Hg.stlc_hyp;
      cases k <;>
      simp only [Hyp.stlc, (HΔ.var_valid Hv').stlc_ty_subst] at Hg' <;>
      rw [<-HA'] <;>
      exact Hg'
  }

theorem HasType.subst_stlc_commute {σ Γ a A}
  (H: Γ ⊢ a: A)
  : (a.subst σ).stlc
  = a.stlc.subst σ.stlc
  := by {
    induction H generalizing σ with
    | var => rfl
    | _ => 
      (try rename AnnotSort => k <;> cases k) <;>
      dsimp only [
        Term.stlc, Stlc.subst, Stlc.Subst.liftn, Subst.liftn] <;>
      (try rw [HasType.stlc_ty_subst] 
        <;> first 
          | assumption 
          | (apply HasType.expr_regular <;> assumption) | skip) <;>
      simp only [*, Subst.stlc_lift]
  }

theorem HasType.term_subst_stlc_commute {σ a} 
  (H: Δ ⊢ a: term A)
  : (a.subst σ).stlc
  = (a.stlc).subst σ.stlc
  := H.subst_stlc_commute

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
        simp [Subst.stlc_lift, Subst.stlc, Subst.wk1]
        rw [Term.wk_stlc_commute]
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
    rw [HasType.term_subst_stlc_commute]
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
    rw [HasType.term_subst_stlc_commute]
    assumption
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
    rw [HasType.term_subst_stlc_commute]
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
    rw [HasType.term_subst_stlc_commute]
    assumption
    rw [Annot.stlc_ty_subst H.expr_regular]
  }

theorem HasType.subst0_stlc_interp_commute {Γ: Context} {a b A B s} 
  (Ha: ((Hyp.mk B (HypKind.val s))::Γ) ⊢ a: term A) 
  (Hb: Γ ⊢ b: expr s B)
  (IΓ: IsCtx Γ)
  (G: Γ.stlc.interp)
  : (Ha.subst (Hb.to_subst IΓ)).stlc.interp G
  = (Annot.stlc_ty_subst Ha.expr_regular) ▸ Ha.stlc.interp.subst ((Hb.to_subst IΓ).interp (IΓ.cons_val Hb.expr_regular)) G
  := by {
    rw [<-Stlc.HasType.subst_interp_dist]
    rw [rec_to_cast']
    rw [Stlc.HasType.interp_transport_cast']
    rw [HasType.term_subst_stlc_commute]
    assumption
    rw [Annot.stlc_ty_subst Ha.expr_regular]
  }

theorem HasType.subst0_gst_stlc_interp_commute {Γ: Context} {a b A B} 
  (Ha: ((Hyp.mk B HypKind.gst)::Γ) ⊢ a: term A) 
  (Hb: Γ ⊢ b: term B)
  (IΓ: IsCtx Γ)
  (G: Γ.stlc.interp)
  : ((Ha.sub (Context.is_sub.refl.cons (Hyp.is_sub.refl_ty HypKind.is_sub.gst))).subst (Hb.to_subst IΓ)).stlc.interp G
  = (Annot.stlc_ty_subst Ha.expr_regular) ▸ 
    (Ha.sub (Context.is_sub.refl.cons (Hyp.is_sub.refl_ty HypKind.is_sub.gst))).stlc.interp.subst ((Hb.to_subst IΓ).interp (IΓ.cons_val Hb.expr_regular)) G
  := by {
    rw [<-Stlc.HasType.subst_interp_dist]
    rw [rec_to_cast']
    rw [Stlc.HasType.interp_transport_cast']
    rw [HasType.term_subst_stlc_commute]
    assumption
    rw [Annot.stlc_ty_subst Ha.expr_regular]
  }

theorem HasType.subst01_stlc_interp_commute {Γ: Context} {e l r A B C sl sr} 
  (He: HasType 
    ((Hyp.mk B (HypKind.val sl))
    ::(Hyp.mk A (HypKind.val sr))::Γ) e (term C))
  (Hl: HasType Γ l (expr sl (B.subst0 r)))
  (Hr: HasType Γ r (expr sr A))
  (HB: HasType ({ ty := A, kind := HypKind.val sr }::Γ) B (sort sl))
  (IΓ: IsCtx Γ)
  (G: Γ.stlc.interp)
  : (He.subst (Hl.to_subst01 Hr IΓ)).stlc.interp G
  = (Annot.stlc_ty_subst He.expr_regular) 
    ▸ He.stlc.interp.subst 
      ((Hl.to_subst01 Hr IΓ).interp ((IΓ.cons_val Hr.expr_regular).cons_val HB)) G
  := by {
    rw [<-Stlc.HasType.subst_interp_dist]
    rw [rec_to_cast']
    rw [Stlc.HasType.interp_transport_cast']
    rw [HasType.term_subst_stlc_commute]
    assumption
    rw [Annot.stlc_ty_subst He.expr_regular]
  }

theorem HasType.subst01_stlc_interp_commute' {Γ: Context} {e l r A B C sl sr} 
  (He: HasType 
    ((Hyp.mk B (HypKind.val sl))
    ::(Hyp.mk A (HypKind.val sr))::Γ) e (term C))
  (He': Γ.stlc ⊧ e': C')
  (Hee': e' = (e.subst01 l r).stlc)
  (HCC': C' = C.stlc_ty)
  (Hl: HasType Γ l (expr sl (B.subst0 r)))
  (Hr: HasType Γ r (expr sr A))
  (HB: HasType ({ ty := A, kind := HypKind.val sr }::Γ) B (sort sl))
  (IΓ: IsCtx Γ)
  (G: Γ.stlc.interp)
  : He'.interp G
  = HCC' 
    ▸ He.stlc.interp.subst 
      ((Hl.to_subst01 Hr IΓ).interp ((IΓ.cons_val Hr.expr_regular).cons_val HB)) G
  := by {
    cases Hee';
    cases HCC';
    rw [<-Stlc.HasType.subst_interp_dist]
    simp only []
    apply interp_cast_spine;
    rw [<-HasType.term_subst_stlc_commute]
    rfl
    assumption
    rfl
    rfl
  }
  
theorem HasType.subst01_gst_stlc_interp_commute {Γ: Context} {e l r A B C sl} 
  (He: HasType 
    ((Hyp.mk B (HypKind.val sl))
    ::(Hyp.mk A HypKind.gst)::Γ) e (term C))
  (Hl: HasType Γ l (expr sl (B.subst0 r)))
  (Hr: HasType Γ r (term A))
  (HB: HasType ({ ty := A, kind := HypKind.val type }::Γ) B (sort sl))
  (IΓ: IsCtx Γ)
  (G: Γ.stlc.interp)
  : ((He.sub (by repeat first | exact Context.is_sub.refl | constructor)).subst (Hl.to_subst01 Hr IΓ)).stlc.interp G
  = (Annot.stlc_ty_subst He.expr_regular) 
    ▸ (He.sub (by repeat first | exact Context.is_sub.refl | constructor)).stlc.interp.subst 
      ((Hl.to_subst01 Hr IΓ).interp ((IΓ.cons_val Hr.expr_regular).cons_val HB)) G
  := by {
    rw [<-Stlc.HasType.subst_interp_dist]
    rw [rec_to_cast']
    rw [Stlc.HasType.interp_transport_cast']
    rw [HasType.term_subst_stlc_commute]
    assumption
    rw [Annot.stlc_ty_subst He.expr_regular]
  }

theorem HasType.subst01_gst_stlc_interp_commute' {Γ: Context} {e l r A B C sl e' C'} 
  (He: HasType 
    ((Hyp.mk B (HypKind.val sl))
    ::(Hyp.mk A HypKind.gst)::Γ) e (term C))
  (He': Γ.stlc ⊧ e': C')
  (Hee': e' = (e.subst01 l r).stlc)
  (HCC': C' = C.stlc_ty)
  (Hl: HasType Γ l (expr sl (B.subst0 r)))
  (Hr: HasType Γ r (term A))
  (HB: HasType ({ ty := A, kind := HypKind.val type }::Γ) B (sort sl))
  (IΓ: IsCtx Γ)
  (G: Γ.stlc.interp)
  : He'.interp G
  = HCC' 
    ▸ (He.sub (by repeat first | exact Context.is_sub.refl | constructor)).stlc.interp.subst 
      ((Hl.to_subst01 Hr IΓ).interp ((IΓ.cons_val Hr.expr_regular).cons_val HB)) G
  := by {
    cases Hee';
    cases HCC';
    rw [<-Stlc.HasType.subst_interp_dist]
    simp only []
    apply interp_cast_spine;
    rw [<-HasType.term_subst_stlc_commute]
    rfl
    assumption
    rfl
    rfl
  }
