import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc
import LogicalRefinement.Denot.Basic
import LogicalRefinement.Denot.Wk
import LogicalRefinement.Denot.Subst

open AnnotSort
open Annot

theorem HasVar.denote_annot
  (Hv: HasVar Γ n (HypKind.val s) A)
  (HΓ: IsCtx Γ)
  (G: Γ.upgrade.stlc.interp)
  (HG: G ⊧ ✓Γ)
  : (expr s A).denote' Γ G ((HΓ.var Hv).stlc.interp G.downgrade)
  := by {
    induction Γ generalizing s n A with
    | nil => cases Hv
    | cons H Γ I =>   
      cases H with
      | mk A k =>
        cases k with
        | val s => 
          cases s with
          | type => 
            let (x, G) := G;
            have ⟨Hx, HG⟩ := HG;
            cases Hv with
            | zero Hk => 
              cases Hk;
              simp only [denote, Context.stlc]
              apply Term.denote_wk1_ty _ _ Γ x G _ _ _ Hx
              rw [Stlc.Context.interp.downgrade_ty]
              rw [Stlc.HasType.interp_var]
              dsimp only [Stlc.HasVar.interp, Sparsity.ix]
              simp only [Eq.mp, Eq.mpr]
              conv =>
                rhs
                rw [monorecursor]
                skip
                rw [<-A.stlc_ty_wk1]
            | succ Hv => 
              cases HΓ with
              | cons_val HΓ =>
                have I' := I Hv HΓ G HG;
                cases s with
                | type =>
                  simp only [denote, Context.stlc]
                  apply Term.denote_wk1_ty _ _ Γ x G _ _ _ I'
                  rw [monorecursor]
                  rename Nat => n;
                  rw [Stlc.HasType.interp_transport_mono]
                  rw [Stlc.Context.interp.downgrade_ty]
                  rw [Stlc.HasType.var_interp_wk1]
                  rfl
                  rw [Term.stlc_var]
                  dsimp only [Sparsity.stlc]
                  split
                  . rfl
                  . have s := Hv.sigma_ty;
                    contradiction
                  rw [Term.stlc_ty_wk1]
                  constructor
                  exact Hv.stlc
                  rw [Term.stlc_var]
                  dsimp only [Sparsity.stlc]
                  split
                  . rfl
                  . have s := Hv.sigma_ty;
                    contradiction
                  rw [Term.stlc_ty_wk1]
                  rfl
                  rw [Term.stlc_ty_wk1]
                  rfl
                | prop => 
                  simp only [denote]
                  exact 
                    Term.denote_wk1_ty _ _ Γ x G 
                      none none (by rw [interp_eq_none]) I';
          | prop => 
            have ⟨Hx, HG⟩ := HG;
            cases Hv with
            | zero Hk => 
              cases Hk;
              simp only [denote, Context.stlc]
              apply Term.denote_wk1_prop _ _ Γ G _ _ _ Hx
              rw [interp_eq_none]
            | succ Hv => 
              cases HΓ with
              | cons_val HΓ =>
                have I' := I Hv HΓ G HG;
                cases s with
                | type =>                   
                  simp only [denote, Context.stlc]
                  apply Term.denote_wk1_prop _ _ Γ G _ _ _ I'
                  rw [monorecursor]
                  rename Nat => n;
                  rw [Stlc.HasType.interp_transport_mono]
                  rfl
                  rw [Term.stlc_var]
                  dsimp only [Sparsity.stlc]
                  split
                  . dsimp only [Term.stlc, Sparsity.stlc]
                    split
                    . rfl
                    . have s := Hv.sigma_ty;
                      contradiction
                  . have s := Hv.sigma_ty;
                    contradiction
                  rw [Term.stlc_ty_wk1]
                  constructor
                  rw [Term.stlc_ty_wk1]
                  rfl
                | prop => 
                  simp only [denote]
                  exact 
                    Term.denote_wk1_prop _ _ Γ G 
                      none none (by rw [interp_eq_none]) I';
        | gst => 
          cases Hv with
          | zero Hk => cases Hk
          | succ Hv => 
            cases HΓ with
            | cons_gst HΓ => 
              let (x, G) := G;
              have ⟨_, HG⟩ := HG;
              have I' := I Hv HΓ G HG;
              cases s with
              | type => 
                simp only [denote, Context.stlc]
                apply Term.denote_wk1_gst _ _ Γ x G _ _ _ I'
                rw [monorecursor]
                rw [Stlc.HasType.interp_transport_mono]
                rw [Stlc.Context.interp.downgrade_gst]
                rfl
                rw [Term.stlc_ty_wk1]
                rfl
                rw [Term.stlc_ty_wk1]
                rfl
              | prop => 
                simp only [denote]
                exact 
                  Term.denote_wk1_gst _ _ Γ x G 
                    none none (by rw [interp_eq_none]) I';
  }

theorem HasType.sym_axiom {Γ: Context} {A}:
  ∀{G: Γ.upgrade.stlc.interp}, (Term.sym_ty A).denote_prop' G
  := by {
    intro G;
    dsimp only [
      Term.denote_prop', 
      Term.denote_prop,
      Term.denote_ty,
      Term.sym_ty, Term.sym_ty_tmp, Term.subst0, Term.subst,
      Subst.lift, Subst.wk1, Term.wk1, Term.to_subst,
      Wk.var, Term.wk
    ]
    intro x _ y _ ⟨px, py, Hxy⟩;
    rw [
      Stlc.HasType.var_interp_0 _ _ _ rfl 
      (by simp only [Term.stlc_ty_wk])
    ] at Hxy
    rw [
      Stlc.HasType.var_interp_wk1 
      (by simp only [Term.stlc_ty_wk]; repeat constructor) 
      _ _ _ rfl rfl
    ] at Hxy
    rw [
      Stlc.HasType.var_interp_0 _ _ _ rfl 
      (by simp only [Term.stlc_ty_wk])
    ] at Hxy
    exists 
      (by simp only [Term.stlc_ty_wk]; repeat constructor), 
      (by simp only [Term.stlc_ty_wk]; repeat constructor);
    rw [
      Stlc.HasType.var_interp_0 _ _ _ rfl 
      (by simp only [Term.stlc_ty_wk])
    ]
    rw [
      Stlc.HasType.var_interp_wk1 
      (by simp only [Term.stlc_ty_wk]; repeat constructor) 
      _ _ _ rfl rfl
    ]
    rw [
      Stlc.HasType.var_interp_0 _ _ _ rfl 
      (by simp only [Term.stlc_ty_wk])
    ]
    exact cast_gen Hxy.symm
  }

theorem HasType.trans_axiom {Γ: Context} {A}:
  ∀{G: Γ.upgrade.stlc.interp}, (Term.trans_ty A).denote_prop' G
  := by {
    intro G;
    dsimp only [
      Term.denote_prop', 
      Term.denote_prop,
      Term.denote_ty,
      Term.sym_ty, Term.sym_ty_tmp, Term.subst0, Term.subst,
      Subst.lift, Subst.wk1, Term.wk1, Term.to_subst,
      Wk.var, Term.wk
    ]
    intro x _ y _ z _ ⟨px, py, Hxy⟩ ⟨py, pz, Hyz⟩;
    --TODO: automate...
    rw [
      Stlc.HasType.var_interp_wk1 
      (by simp only [Term.stlc_ty_wk]; repeat constructor) 
      _ _ _ rfl rfl
    ] at Hxy
    rw [
      Stlc.HasType.var_interp_wk1 
      (by simp only [Term.stlc_ty_wk]; repeat constructor) 
      _ _ _ rfl rfl
    ] at Hxy
    rw [
      Stlc.HasType.var_interp_0 _ _ _ rfl 
      (by simp only [Term.stlc_ty_wk])
    ] at Hxy
    rw [
      Stlc.HasType.var_interp_wk1 
      (by simp only [Term.stlc_ty_wk]; repeat constructor) 
      _ _ _ rfl rfl
    ] at Hxy
    rw [
      Stlc.HasType.var_interp_0 _ _ _ rfl 
      (by simp only [Term.stlc_ty_wk])
    ] at Hxy
    rw [
      Stlc.HasType.var_interp_0 _ _ _ rfl 
      (by simp only [Term.stlc_ty_wk])
    ] at Hyz
    rw [
      Stlc.HasType.var_interp_wk1 
      (by simp only [Term.stlc_ty_wk]; repeat constructor) 
      _ _ _ rfl rfl
    ] at Hyz
    rw [
      Stlc.HasType.var_interp_0 _ _ _ rfl 
      (by simp only [Term.stlc_ty_wk])
    ] at Hyz
    exists 
      (by simp only [Term.stlc_ty_wk]; repeat constructor), 
      (by simp only [Term.stlc_ty_wk]; repeat constructor);
    rw [
      Stlc.HasType.var_interp_wk1 (by simp only [Term.stlc_ty_wk]; repeat constructor) 
      _ _ _ rfl rfl
    ]
    rw [
      Stlc.HasType.var_interp_wk1 (by simp only [Term.stlc_ty_wk]; repeat constructor) 
      _ _ _ rfl rfl
    ]
    rw [
      Stlc.HasType.var_interp_0 _ _ _ rfl 
      (by simp only [Term.stlc_ty_wk])
    ]
    rw [
      Stlc.HasType.var_interp_0 _ _ _ rfl 
      (by simp only [Term.stlc_ty_wk])
    ]
    rw [cast_gen Hxy, cast_gen Hyz]
    simp only [Term.stlc_ty_wk]
  }

theorem HasType.denote
  (H: Γ ⊢ a: A)
  (HΓ: IsCtx Γ)
  (G: Γ.upgrade.stlc.interp)
  (HG: Γ.denote G)
  : A.denote' Γ G (H.stlc.interp G.downgrade)
  := by {
    --TODO: replace with a recursive match?
    induction H with
    | var HA Hv IA => exact Hv.denote_annot HΓ G HG
    | lam Hs HA Is IA =>
      stop
      intro x Hx
      cases x with
      | some x => 
        --TODO: make this a simp attribute mmkay...
        dsimp only [
          Annot.stlc_ty, term, Term.stlc_ty, Term.stlc, 
          Stlc.HasType.interp, 
          Ty.interp.app, Ty.interp.bind_val
        ]
        rw [<-Stlc.Context.interp.downgrade_ty]
        apply Is
        constructor
        exact HΓ
        exact HA
        exact ⟨Hx, HG⟩
      | none => exact False.elim (HA.denote_ty_non_null Hx)
    | @app Γ A B l r HAB Hl Hr IA Il Ir =>
      stop
      dsimp only [Annot.denote]
      dsimp only [
        Annot.stlc_ty, term, Term.stlc_ty, Term.stlc, 
        Stlc.HasType.interp, 
        Ty.interp.app
      ]
      generalize Hlg:
        Stlc.HasType.interp
        (_ : _⊧Term.stlc l _:_)
        (Stlc.Context.interp.downgrade G) = li;
      have Il' := Hlg ▸ (Il HΓ G HG);
      generalize Hrg:
        Stlc.HasType.interp
        (_ : _⊧Term.stlc r _:_)
        (Stlc.Context.interp.downgrade G) = ri;
      have Ir' := Hrg ▸ (Ir HΓ G HG);
      have HA: Γ ⊢ A: type := by cases HAB; assumption;
      have HB: ((Hyp.val A type)::Γ) ⊢ B: type := 
        by cases HAB; assumption;
      cases li with
      | some li => 
        cases ri with
        | some ri => 
          have Ilr := Il' (some ri) Ir';
          simp only []
          dsimp only [Annot.denote, Term.denote_ty, denote', Term.denote_ty'] at Il'
          dsimp only [Annot.denote, Term.denote_ty, denote']
          apply HasType.denote_ty_subst0' Hr HΓ rfl HG HB HB.stlc_ty_subst.symm _ Hrg.symm Ilr
          rw [monorecursor]
          rfl
        | none => exact False.elim (HA.denote_ty_non_null Ir')
      | none => exact False.elim (HAB.denote_ty_non_null Il')
    | @pair Γ A B l r HAB Hl Hr IAB Il Ir =>
      stop
      dsimp only [denote', Term.denote_ty', Term.denote_ty, 
        Stlc.HasType.interp, Term.stlc, stlc_ty, term, Term.stlc_ty, 
        Ty.interp.pair]
      generalize Hli: Stlc.HasType.interp _ _ = li;
      have Il' := Hli ▸ Il HΓ G HG;
      generalize Hri: Stlc.HasType.interp _ _ = ri;
      have HB: (_::Γ) ⊢ B: type := by cases HAB; assumption;
      have Ir' := Ir HΓ G HG;
      cases li with
      | some li => 
        cases ri with
        | some ri => 
          simp only [Ty.eager, pure]
          apply And.intro;
          {
            exact Il'
          }
          {
            simp only [<-Hli, <-Hri]
            simp only [denote'] at Ir';
            rw [denote_ty_subst0]
            exact Ir';
            assumption
            assumption
            rfl
            assumption
            assumption
            rw [HB.stlc_ty_subst0]
            rw [rec_to_cast']
            rw [Stlc.HasType.interp_transport_cast']
            rfl
            rw [HB.stlc_ty_subst0]
            rfl
          }
        | none => 
          apply Hr.term_regular.denote_ty_non_null
          dsimp only [denote'] at Ir'
          apply Term.denote_ty_transport rfl rfl rfl _ Ir'
          simp only []
          rw [<-Stlc.HasType.interp_transport_inner _ _ rfl HB.stlc_ty_subst.symm]
          exact (interp_eq_none' Hri).symm
      | none => exact Hl.term_regular.denote_ty_non_null Il'
    | @let_pair Γ A B C e e' k He HA HB HC He' Ie IA IB IC Ie' =>
      stop
      cases k with
      | type => sorry
      | prop => sorry
    | inj_l He HB Ie IB => 
      stop
      dsimp only [
        denote', Term.denote_ty', Term.denote_ty, Term.stlc, 
        stlc_ty, Term.stlc_ty, Stlc.HasType.interp,
        Ty.interp.inl
      ]
      generalize Hei: Stlc.HasType.interp _ _ = ei;
      have Ie' := Hei ▸ Ie HΓ G HG;
      cases ei with
      | some ei => 
        dsimp only [Option.map, Option.bind, Function.comp]
        exact Ie'
      | none => exact He.term_regular.denote_ty_non_null Ie'
    | inj_r He HA Ie IA => 
      dsimp only [
        denote', Term.denote_ty', Term.denote_ty, Term.stlc, 
        stlc_ty, Term.stlc_ty, Stlc.HasType.interp,
        Ty.interp.inl
      ]
      generalize Hei: Stlc.HasType.interp _ _ = ei;
      have Ie' := Hei ▸ Ie HΓ G HG;
      cases ei with
      | some ei => 
        dsimp only [Option.map, Option.bind, Function.comp]
        exact Ie'
      | none => exact He.term_regular.denote_ty_non_null Ie'
    | @case Γ A B C e l r k He HA HB HC Hl Hr Ie IA IB IC Il Ir =>
      stop
      have HAB: Γ ⊢ Term.coprod A B: type := HasType.coprod HA HB;
      cases k with
      | type => 
        dsimp only [denote']
        dsimp only [Term.stlc, Term.stlc_ty, stlc_ty, Stlc.HasType.interp]
        have Ie' := Ie HΓ G HG;
        dsimp only [Term.stlc, Term.stlc_ty, stlc_ty, Stlc.HasType.interp] at Ie';
        generalize Hei: Stlc.HasType.interp (_ : _⊧Term.stlc e _:_) _ = ei;
        --TODO: wait for Zulip to answer regarding the requirement to have
        -- Stlc.HasType.interp_irrel here.
        rw [Stlc.HasType.interp_irrel] at Ie'
        rw [Hei] at Ie'
        cases ei with
        | some ei => 
          cases ei with
          | inl a => 
            simp only [Ty.interp.case]
            have Il' := Il 
              (HΓ.cons_val HA)
              (Ty.eager a, G)
              ⟨Ie', HG⟩
              ;
            simp only [denote'] at Il';
            sorry --TODO: appropriate typecasting for Il'
          | inr b => 
            simp only [Ty.interp.case]
            have Ir' := Ir
              (HΓ.cons_val HB)
              (Ty.eager b, G)
              ⟨Ie', HG⟩
              ;
            dsimp only [denote'] at Ir';
            sorry --TODO: appropriate typecasting for Ir'
        | none => exact False.elim (HAB.denote_ty_non_null Ie')
      | prop => 
        dsimp only [denote']
        have Ie' := Ie HΓ G HG;
        dsimp only [
          Term.stlc, Term.stlc_ty, stlc_ty, Stlc.HasType.interp] 
          at Ie';
        generalize Hei: Stlc.HasType.interp (_ : _⊧Term.stlc e _:_) _ = ei;
        rw [Stlc.HasType.interp_irrel] at Ie'
        rw [Hei] at Ie'
        cases ei with
        | some ei => 
          cases ei with
          | inl a => 
            simp only [Ty.interp.case]
            have Il' := Il 
              (HΓ.cons_val HA)
              (Ty.eager a, G)
              ⟨Ie', HG⟩
              ;
            dsimp only [denote'] at Il';
            sorry --TODO: appropriate typecasting for Il'
          | inr b => 
            simp only [Ty.interp.case]
            have Ir' := Ir
              (HΓ.cons_val HB)
              (Ty.eager b, G)
              ⟨Ie', HG⟩
              ;
            dsimp only [denote'] at Ir';
            sorry --TODO: appropriate typecasting for Ir'
        | none => exact False.elim (HAB.denote_ty_non_null Ie')
        exact He.stlc
    | elem =>
      stop 
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      apply And.intro;
      {
        sorry
      }
      {
        sorry
      }
    | let_set => 
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
    | lam_pr => 
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      apply And.intro
      {
        sorry
      }
      {
        sorry
      }
    | app_pr HφA Hl Hr IφA Il Ir => 
      stop
      dsimp only [denote', Term.denote_ty, Term.denote_ty']
      sorry
    | lam_irrel => 
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      apply And.intro
      {
        sorry
      }
      {
        sorry
      }
    | app_irrel =>
      stop  
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      sorry
    | @repr Γ A B l r HAB Hl Hr IAB Il Ir =>
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      apply And.intro
      . sorry -- not_none + Ir?
      . exists Hl.stlc.interp G
        sorry
    | let_repr =>
      stop  
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
    | abort Hp HA Ip IA => exact False.elim (Ip HΓ G HG)
    | dconj HAB Hl Hr IAB Il Ir => 
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ] at *
      apply And.intro
      exact Il HΓ G HG
      have Ir' := Ir HΓ G HG;
      --TODO: subst0 for prop
      sorry
    | let_conj =>  
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
    | disj_l He HB Ie IB => exact Or.inl (Ie HΓ G HG)
    | disj_r He HB Ie IB => exact Or.inr (Ie HΓ G HG)
    | case_pr He HA HB HC Hl Hr Ie IA IB IC Il Ir => 
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ] at *
      have Ie' := Ie HΓ G HG;
      cases Ie' with
      | inl Ie' => 
        have Il' := Il (IsCtx.cons_val HΓ HA) G ⟨Ie', HG⟩;
        sorry
      | inr Ie' =>  
        have Ir' := Ir (IsCtx.cons_val HΓ HB) G ⟨Ie', HG⟩;
        sorry
    | imp Hϕ Hs Iϕ Is => exact λDϕ => Is (IsCtx.cons_val HΓ Hϕ) G ⟨Dϕ, HG⟩;
    --TODO: why is mp's result upgraded?
    | mp Hϕψ Hl Hr _ Il Ir => 
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ] at *
      rw [<-Hr.denote_prop_subst0 HΓ rfl HG 
        (by cases Hϕψ; assumption)
        (by rw [HasType.stlc_ty_subst0] <;> cases Hϕψ; assumption)
        (by 
          rw [rec_to_cast, cast_none];
          rw [HasType.stlc_ty_subst0]
          cases Hϕψ; assumption
        )
      ]
      exact Il HΓ G HG (Ir HΓ G HG)
    | general HA Hs IA Is => 
      exact λx Dx => Is (IsCtx.cons_val HΓ HA) (x, G) ⟨Dx, HG⟩;
    | inst => sorry
    | @wit Γ A φ l r HAφ Hl Hr IAφ Il Ir =>
      stop
      exists Hl.stlc.interp G
      --TODO: upgrade theorems for IsCtx and context denotation
      have Il' := Il HΓ.upgrade (Context.upgrade_idem.symm ▸ G) HG.upgrade;
      apply And.intro
      . dsimp only [denote', Term.denote_ty'] at Il'
        sorry
      . sorry
    | let_wit => sorry
    | refl Ha => exact ⟨Ha.stlc, Ha.stlc, rfl⟩
    | cong => 
      stop
      dsimp only [denote', Annot.denote]
      sorry
    | beta => 
      stop
      dsimp only [denote', Annot.denote]
      sorry
    | beta_ir => 
      stop
      dsimp only [denote', Annot.denote]
      sorry
    | beta_pr => 
      stop
      dsimp only [denote', Annot.denote]
      sorry
    | funext => sorry
    | irir Hf Hx Hy => 
      stop
      exact ⟨
        by {
          have Hf' := Hf.stlc;
          dsimp only 
            [stlc_ty, Term.const_arrow, Term.wk1, Term.stlc_ty] at Hf'
          rw [Term.stlc_ty_wk] at Hf'
          exact Hf'
        }, 
        by {
          have Hf' := Hf.stlc;
          dsimp only 
            [stlc_ty, Term.const_arrow, Term.wk1, Term.stlc_ty] at Hf'
          rw [Term.stlc_ty_wk] at Hf'
          exact Hf'
        }, 
        rfl
      ⟩
    | prir HP HA Hx Hy _  _ Ix Iy =>
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      rw [<-Hx.denote_prop_subst0 HΓ rfl HG HP _ 
        (by 
          rw [rec_to_cast, cast_none];
          exact congr (congr rfl HP.stlc_ty_subst.symm) rfl;
          exact HP.stlc_ty_subst.symm
        )
      ]
      intro Dx;
      --TODO: have an actual weakening theorem
      apply Term.denote_wk1_prop _ sorry _ G none none sorry _;
      unfold Term.denote_ty';
      rw [<-Hy.denote_prop_subst0 HΓ rfl HG HP _ 
        (by 
          rw [rec_to_cast, cast_none];
          exact congr (congr rfl HP.stlc_ty_subst.symm) rfl;
          exact HP.stlc_ty_subst.symm
        )
      ]
      exact Dx
    | beta_left =>  
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      exists sorry, sorry;
      simp only [Ty.interp.case];
      split
      {
        sorry
      }
      {
        sorry
      }
      {
        unfold Ty.abort;
        --TODO: subst0 none lemma
        sorry
      }
    | beta_right =>
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      exists sorry, sorry;
      sorry
    | beta_pair =>   
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
    | beta_set =>   
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
    | beta_repr =>   
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
    | succ => 
      stop
      intro x H;
      cases x with
      | none => cases H
      | some x => exact True.intro
    | @natrec Γ C e z s k HC He Hz Hs IC Ie Iz Is =>
      stop
      generalize Hei:
        Stlc.HasType.interp
          He.stlc
          (Stlc.Context.interp.downgrade G) = ei;
      cases ei with
      | none => 
        have Ie' := Ie HΓ G HG;
        dsimp only [Term.denote_ty', Term.denote_ty] at Ie';
        rw [Hei] at Ie';
        exact Ie'.elim
      | some n =>
        cases k with
        | type =>
          dsimp only [
            denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
            Term.denote_ty', Term.denote_ty
          ]
          simp only []
          generalize Hei':
            Stlc.HasType.interp
              (_: _ ⊧ e.stlc _: _)
              (Stlc.Context.interp.downgrade G) = ei';
          induction n generalizing e with
          | zero => 
            cases ei' with
            | some n' =>
              cases n' with
              | zero => 
                simp only [
                  Ty.interp.natrec_int, Ty.interp.natrec_inner, 
                  Ty.interp.bind_val
                ]
                --TODO: subst0 invariance
                sorry
              | succ n' => sorry
            | none => sorry
          | succ n I =>
            cases ei' with
            | some n' =>
              cases n' with
              | zero => sorry
              | succ n' => 
                simp only [
                  Ty.interp.natrec_int, Ty.interp.natrec_inner, 
                  Ty.interp.bind_val
                ]
                generalize HIi': Ty.interp.natrec_inner n' _ _ = Ii;
                cases Ii with
                | none => 
                  apply False.elim;
                  sorry
                | some Ii => 
                  simp only []
                  --TODO: subst0 invariance, s application...
                  sorry
            | none => sorry
        | prop =>         
          dsimp only [
            denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
            Term.denote_ty', Term.denote_ty
          ]
          induction n generalizing e with
          | zero => 
            --TODO: subst0 invariance...
            sorry
          | succ n I => 
            --TODO: subst0 invariance...
            sorry
    | @beta_zero Γ C z s HC Hz Hs IC Iz Is => 
        stop
        dsimp only [
          denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
          Term.denote_ty', Term.denote_ty
        ]
        exists by {
          simp only [if_pos, HC.stlc_ty_subst, Term.subst0]
          exact 
            @Stlc.HasType.natrec
            Γ.upgrade.stlc
            _ _ _ _
            Stlc.HasType.zero
            (HC.stlc_ty_subst ▸ Hz.stlc)
            (by {
              have Hs' := Hs.stlc;
              simp only [
                Term.alpha0, Term.wknth, stlc_ty
              ] at Hs';
              rw [HasType.stlc_ty_subst] at Hs';
              rw [Term.stlc_ty_wk] at Hs';
              exact Hs';
              exact HC.wk_sort (by repeat constructor);
            })
        }, Hz.stlc;
    | @beta_succ Γ C e z s HC He Hz Hs IC Ie Iz Is => 
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      simp only []
      exists sorry, sorry;
      simp only [
        Eq.mp, Ty.interp.app, Ty.interp.bind_val, Ty.interp.natrec_int
      ]
      split
      {
        rename_i n Hm;
        cases n with
        | zero => sorry
        | succ n =>
          simp only [Ty.interp.natrec_inner, Ty.interp.bind_val]
          split
          {
            --TODO: subst0 lemma...
            sorry
          }
          {
            sorry
          }
      }
      {
        sorry
      }
    | _ => exact True.intro
  }