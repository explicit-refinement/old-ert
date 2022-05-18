import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.InterpWkUtils
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
      cases H with
      | var HA Hv => 
        --TODO: factor out as lemma
        rw [Term.stlc_var]
        dsimp only [subst, Subst.stlc, Sparsity.stlc]
        simp only [Hv.sigma, if_pos True.intro]
        dsimp only [Stlc.subst]
        rw [Sparsity.ix_inv_valid]
        rw [Hv.sigma]
        rfl
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
      | let_pair He HA HB HC He' =>
        rename_i A B C;
        let Γ' := (Hyp.val (A.subst σ) type)::Γ;
        let Δ' := (Hyp.val A type)::Δ;
        have S': SubstCtx σ.lift Γ' Δ'
          := S.lift_delta (by exact HA)
        let Γ'' := (Hyp.val (B.subst σ.lift) type)::Γ';
        let Δ'' := (Hyp.val B type)::Δ';
        have S'': SubstCtx σ.lift.lift Γ'' Δ''
          := S'.lift_delta (by exact HB);
        have Ie'' := 
          loosen Ie' He' S'' 
          (true::true::Γ.sparsity) (true::true::Δ.sparsity);
        dsimp only [stlc, Stlc.subst, Subst.liftn]
        conv =>
          lhs
          congr
          . rw [(HasType.sigma HA HB).stlc_ty_subst]
          . rw [Ie He S]
          . rw [Ie'']
            rw [Subst.stlc_lift_true]
            rw [Subst.stlc_lift_true]
      | let_set He HA HB HC He' =>        
        rename_i A B C;
        let Γ' := (Hyp.val (A.subst σ) type)::Γ;
        let Δ' := (Hyp.val A type)::Δ;
        have S': SubstCtx σ.lift Γ' Δ'
          := S.lift_delta (by exact HA)
        let Γ'' := (Hyp.val (B.subst σ.lift) prop)::Γ';
        let Δ'' := (Hyp.val B prop)::Δ';
        have S'': SubstCtx σ.lift.lift Γ'' Δ''
          := S'.lift_delta (by exact HB);
        have Ie'' := 
          loosen Ie' He' S'' 
          (false::true::Γ.sparsity) (false::true::Δ.sparsity);
        dsimp only [stlc, Stlc.subst, Subst.liftn]
        conv =>
          lhs
          congr
          . rw [(HasType.set HA HB).stlc_ty_subst]
          . rw [Ie He S]
          . rw [Ie'']
            rw [Subst.stlc_lift_false]
            rw [Subst.stlc_lift_true]
      | let_repr He HA HB HC He' =>        
        rename_i A B C;
        let Γ' := (Hyp.gst (A.subst σ))::Γ;
        let Δ' := (Hyp.gst A)::Δ;
        have S': SubstCtx σ.lift Γ' Δ'
          := S.lift_delta (by exact HA)
        let Γ'' := (Hyp.val (B.subst σ.lift) type)::Γ';
        let Δ'' := (Hyp.val B type)::Δ';
        have S'': SubstCtx σ.lift.lift Γ'' Δ''
          := S'.lift_delta (by exact HB);
        have Ie'' := 
          loosen Ie' He' S'' 
          (true::false::Γ.sparsity) (true::false::Δ.sparsity);
        have HB': ((Hyp.val A type)::Δ) ⊢ B: type
          := by {
            apply HB.sub;
            constructor
            exact Context.is_sub.refl;
            constructor
            constructor
          }
        dsimp only [stlc, Stlc.subst, Subst.liftn]
        conv =>
          lhs
          congr
          . rw [(HasType.union HA HB').stlc_ty_subst]
          . rw [Ie He S]
          . rw [Ie'']
            rw [Subst.stlc_lift_true]
            rw [Subst.stlc_lift_false]
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
    -- TODO: potential bug: when A shadows A', there's an error
    -- (2022-04-26, 23:15)
    case abs k A' t IA It => 
      have SA: ∀k, (Δ ⊢ A': k.annot) -> 
        SubstCtx σ.lift ((Hyp.mk (A'.subst σ) k)::Γ) ((Hyp.mk A' k)::Δ)
        := λk HA => S.lift_delta HA
      cases H with
      | lam Ht HA => 
        dsimp only [stlc, Stlc.subst]
        conv =>
          lhs
          congr
          . rw [HA.stlc_ty_subst]
          . rw [
              loosen It Ht (SA _ (by exact HA)) 
              (true::Γ.sparsity) (true::Δ.sparsity)
              rfl rfl
            ]
            rhs
            rw [Subst.stlc_lift_true]
      | _ => 
        rename _ ⊢ t: _ => Ht;
        rename _ ⊢ A': _ => HA;
        dsimp only [stlc, Stlc.subst]
        rw [
          loosen It Ht (SA _ (by exact HA)) 
          (false::Γ.sparsity) (false::Δ.sparsity)
          rfl rfl
        ]
        rw [Subst.stlc_lift_false]
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
          : SubstCtx σ.lift ((Hyp.val (A.subst σ) type)::Γ) ((Hyp.val A type)::Δ)
          := S.lift_delta (by exact HA)
        have SB 
          : SubstCtx σ.lift ((Hyp.val (B.subst σ) type)::Γ) ((Hyp.val B type)::Δ)
          := S.lift_delta (by exact HB);
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
          := S.lift_delta (by constructor)
        let Γ'' := (Hyp.val (K.subst σ.lift) type)::Γ';
        let Δ'' := (Hyp.val K type)::Δ';
        -- BUG?: why is it that if the `by exact` is removed for argument 2, 
        -- there's an error? (2022-04-25, 16:34)
        --
        -- Note on (2022-04-26, 23:46): same thing with `lift_delta`;
        -- think it has to do with unification...
        --
        -- Note on (2022-05-13, 15:21): still have the same error...
        have S'': SubstCtx σ.lift.lift Γ'' Δ''
          := S'.lift_delta (by exact HK);
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

abbrev SubstCtx.interp {σ Γ Δ} (S: SubstCtx σ Γ Δ) (IΔ: IsCtx Δ)
  : Stlc.InterpSubst Γ.stlc Δ.stlc
  := Stlc.SubstCtx.interp (S.stlc IΔ)

abbrev SubstCtx.interp_up {σ Γ Δ} (S: SubstCtx σ Γ Δ) (IΔ: IsCtx Δ)
  : Stlc.InterpSubst Γ.upgrade.stlc Δ.upgrade.stlc
  := Stlc.SubstCtx.interp (SubstCtx.stlc S.upgrade IΔ.upgrade)

abbrev SubstCtx.transport_interp {σ Γ Δ}
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.stlc.interp)
  : Δ.stlc.interp
  := Stlc.InterpSubst.transport_ctx (S.interp IΔ) G

abbrev SubstCtx.transport_interp_up {σ Γ Δ}
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.upgrade.stlc.interp)
  : Δ.upgrade.stlc.interp
  := Stlc.InterpSubst.transport_ctx (S.interp_up IΔ) G

theorem Term.subst_stlc_interp_commute {Γ Δ σ a} 
  (H: Δ ⊢ a: term A) 
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.stlc.interp)
  : (Annot.stlc_ty_subst H.term_regular) ▸ (H.subst S).stlc.interp G
  = H.stlc.interp.subst (S.interp IΔ) G
  := by {
    rw [<-Stlc.HasType.subst_interp_dist]
    sorry
  }