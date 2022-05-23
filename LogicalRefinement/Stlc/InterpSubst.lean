import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.InterpWkUtils
import LogicalRefinement.Stlc.InterpInv
import LogicalRefinement.Stlc.Subst
import LogicalRefinement.Utils
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

theorem Term.term_subst_stlc_commute {Γ Δ σ a} 
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

theorem SubstCtx.interp_lift_ty 
  {σ: Subst} {Γ Δ: Context} {A}
  (S: SubstCtx σ Γ Δ)
  (S': 
    SubstCtx σ.lift 
      ({ ty := A.subst σ, kind := HypKind.val type }::Γ) 
      ({ ty := A, kind := HypKind.val type }::Δ))
  (IΔ: IsCtx Δ)
  (HA: Δ ⊢ A: type)
  : S'.interp (IsCtx.cons_val IΔ HA) 
  = cast (by simp only [Context.stlc]; rw [HA.stlc_ty_subst])
    (@Stlc.InterpSubst.lift A.stlc_ty Γ.stlc Δ.stlc (S.interp IΔ))
  := by {
    funext n A' Hv;
    cases n with
    | zero => 
      simp only [
        interp, Stlc.SubstCtx.interp, Subst.stlc, Sparsity.ix_inv,
        Subst.lift
        ]
      dsimp only [Term.stlc]
      sorry
    | succ n => sorry
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

theorem SubstCtx.transport_interp_lift_ty 
  {σ: Subst} {Γ Δ: Context} {A}
  (S: SubstCtx σ Γ Δ)
  (S': 
    SubstCtx σ.lift 
      ({ ty := A.subst σ, kind := HypKind.val type }::Γ) 
      ({ ty := A, kind := HypKind.val type }::Δ))
  (IΔ: IsCtx Δ)
  (HA: Δ ⊢ A: type)
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
      rw [interp_lift_ty S S' IΔ HA]
      rw [Stlc.InterpSubst.pop_cast]
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
  
theorem SubstCtx.transport_interp_lift_prop
  {σ: Subst} {Γ Δ: Context} {A}
  (S: SubstCtx σ Γ Δ)
  (S': 
    SubstCtx σ.lift 
      ({ ty := A.subst σ, kind := HypKind.val prop }::Γ) 
      ({ ty := A, kind := HypKind.val prop }::Δ))
  (IΔ: IsCtx Δ)
  (HA: Δ ⊢ A: prop)
  (G: Γ.stlc.interp)
  : transport_interp S' (IsCtx.cons_val IΔ HA) G
  = transport_interp S IΔ G
  := by {
    unfold transport_interp
    unfold Stlc.InterpSubst.transport_ctx
    simp only [Context.stlc]
    apply congr _ rfl;
    {
      funext h;
      generalize HI: interp S _ = I;
      generalize HI': interp S' _ = I';
      have HII': I = I' := by {
        rw [<-HI];
        rw [<-HI'];
        unfold interp;
        funext n A Hv G;
        unfold Stlc.SubstCtx.interp;
        apply congr _ rfl;
        apply interp_congr;
        simp [Subst.stlc_lift_false]
      };
      rw [HII']
    }
  }

abbrev SubstCtx.transport_interp_up {σ Γ Δ}
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.upgrade.stlc.interp)
  : Δ.upgrade.stlc.interp
  := transport_interp S.upgrade IΔ.upgrade G

theorem SubstCtx.transport_interp_up_lift_ty 
  {σ: Subst} {Γ Δ: Context} {A}
  (S: SubstCtx σ Γ Δ)
  (S': 
    SubstCtx σ.lift 
      ({ ty := A.subst σ, kind := HypKind.val type }::Γ) 
      ({ ty := A, kind := HypKind.val type }::Δ))
  (IΔ: IsCtx Δ)
  (HA: Δ ⊢ A: type)
  (G: Γ.upgrade.stlc.interp)
  (x y)
  (p: x = HA.stlc_ty_subst ▸ y)
  : transport_interp_up S' (IsCtx.cons_val IΔ HA) (y, G)
  = (x, transport_interp_up S IΔ G)
  := by {
    unfold transport_interp_up
    apply transport_interp_lift_ty;
    exact p;
    exact HA.upgrade
  }
  
theorem SubstCtx.transport_interp_up_lift_prop
  {σ: Subst} {Γ Δ: Context} {A}
  (S: SubstCtx σ Γ Δ)
  (S': 
    SubstCtx σ.lift 
      ({ ty := A.subst σ, kind := HypKind.val prop }::Γ) 
      ({ ty := A, kind := HypKind.val prop }::Δ))
  (IΔ: IsCtx Δ)
  (HA: Δ ⊢ A: prop)
  (G: Γ.upgrade.stlc.interp)
  : transport_interp_up S' (IsCtx.cons_val IΔ HA) G
  = transport_interp_up S IΔ G
  := by {
    unfold transport_interp_up
    apply transport_interp_lift_prop;
    exact HA.upgrade
  }

theorem HasType.subst_stlc_interp_commute {Γ Δ σ a} 
  (H: Δ ⊢ a: expr s A) 
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.stlc.interp)
  : (H.subst S).stlc.interp G
  = (Annot.stlc_ty_subst H.expr_regular) ▸ H.stlc.interp.subst (S.interp IΔ) G
  := by {
    cases s with
    | type =>
      rw [<-Stlc.HasType.subst_interp_dist]
      rw [rec_to_cast']
      rw [Stlc.HasType.interp_transport_cast']
      rw [Term.term_subst_stlc_commute]
      assumption
      assumption
      rw [Annot.stlc_ty_subst H.expr_regular]
    | prop => 
      generalize Stlc.HasType.interp _ _ = x;
      generalize Stlc.Context.deriv.subst _ _ _ = y;
      cases x with
      | none => 
        cases y with
        | none => simp
        | some x => cases x
      | some x => cases x
  }
  
theorem HasType.subst_stlc_interp_up_commute {Γ Δ σ a} 
  (H: Δ.upgrade ⊢ a: expr s A) 
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.upgrade.stlc.interp)
  : (H.subst S.upgrade).stlc.interp G
  = (Annot.stlc_ty_subst H.expr_regular) ▸ H.stlc.interp.subst (S.interp_up IΔ) G
  := by {
    cases s with
    | type =>
      rw [<-Stlc.HasType.subst_interp_dist]
      rw [rec_to_cast']
      rw [Stlc.HasType.interp_transport_cast']
      rw [Term.term_subst_stlc_commute]
      assumption
      apply SubstCtx.upgrade S;
      rw [Annot.stlc_ty_subst H.expr_regular]
    | prop =>
      generalize Stlc.HasType.interp _ _ = x;
      generalize Stlc.Context.deriv.subst _ _ _ = y;
      cases x with
      | none => 
        cases y with
        | none => simp
        | some x => cases x
      | some x => cases x
  }

theorem HasType.subst_stlc_interp_commute' {Γ Δ σ a} 
  (H: Δ ⊢ a: expr s A) 
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.stlc.interp)
  : (Annot.stlc_ty_subst H.expr_regular) ▸ (H.subst S).stlc.interp G
  = H.stlc.interp.subst (S.interp IΔ) G
  := by {
    cases s with
    | type =>
      rw [<-Stlc.HasType.subst_interp_dist]
      rw [rec_to_cast']
      rw [Stlc.HasType.interp_transport_cast']
      rw [Term.term_subst_stlc_commute]
      assumption
      assumption
      rw [Annot.stlc_ty_subst H.expr_regular]
    | prop =>
      generalize Stlc.HasType.interp _ _ = x;
      generalize Stlc.Context.deriv.subst _ _ _ = y;
      cases x with
      | none => 
        cases y with
        | none => simp
        | some x => cases x
      | some x => cases x
  }
  
theorem HasType.subst_stlc_interp_up_commute' {Γ Δ σ a} 
  (H: Δ.upgrade ⊢ a: expr s A) 
  (S: SubstCtx σ Γ Δ)
  (IΔ: IsCtx Δ)
  (G: Γ.upgrade.stlc.interp)
  : (Annot.stlc_ty_subst H.expr_regular) ▸ (H.subst S.upgrade).stlc.interp G
  = H.stlc.interp.subst (S.interp_up IΔ) G
  := by {
    cases s with
    | type =>
      rw [<-Stlc.HasType.subst_interp_dist]
      rw [rec_to_cast']
      rw [Stlc.HasType.interp_transport_cast']
      rw [Term.term_subst_stlc_commute]
      assumption
      apply SubstCtx.upgrade S;
      rw [Annot.stlc_ty_subst H.expr_regular]
    | prop =>
      generalize Stlc.HasType.interp _ _ = x;
      generalize Stlc.Context.deriv.subst _ _ _ = y;
      cases x with
      | none => 
        cases y with
        | none => simp
        | some x => cases x
      | some x => cases x
  }