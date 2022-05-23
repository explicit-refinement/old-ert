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
              have ⟨Hx, HG⟩ := HG;
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

theorem HasType.sym_axiom {Γ A} (HA: Γ ⊢ A: type):
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
    intro x Hx y Hy ⟨px, py, Hxy⟩;
    sorry
  }

theorem HasType.trans_axiom {Γ A} (HA: Γ ⊢ A: type):
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
    intro x Hx y Hy z Hz ⟨px, py, Hxy⟩ ⟨py, pz, Hyz⟩;
    sorry
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
      have HB: ((Hyp.val A type)::Γ) ⊢ B: type := by cases HAB; assumption;
      cases li with
      | some li => 
        cases ri with
        | some ri => 
          have Ilr := Il' (some ri) Ir';
          simp only []
          dsimp only [Annot.denote, Term.denote_ty, denote', Term.denote_ty'] at Il'
          dsimp only [Annot.denote, Term.denote_ty, denote']
          apply HasType.denote_subst0' Hr HΓ rfl HG HB HB.stlc_ty_subst.symm _ Hrg.symm Ilr
          rw [monorecursor]
          rfl
        | none => exact False.elim (HA.denote_ty_non_null Ir')
      | none => exact False.elim (HAB.denote_ty_non_null Il')
    | @pair Γ A B l r HAB Hl Hr IAB Il Ir => 
      dsimp only [denote', Term.denote_ty', Term.denote_ty, 
        Stlc.HasType.interp, Term.stlc, stlc_ty, term, Term.stlc_ty, 
        Ty.interp.pair]
      generalize Hli: Stlc.HasType.interp _ _ = li;
      have Il' := Hli ▸ Il HΓ G HG;
      generalize Hri: Stlc.HasType.interp _ _ = ri;
      have HB: (_::Γ) ⊢ B: type := by cases HAB; assumption;
      have Ir' := Ir HΓ G HG;
      --rw [HasType.stlc_ty_subst0] at Ir';
      cases li with
      | some li => 
        cases ri with
        | some ri => sorry
        | none => 
          apply Hr.term_regular.denote_ty_non_null
          dsimp only [denote'] at Ir'
          apply Term.denote_ty_transport rfl rfl rfl _ Ir'
          simp only []
          rw [<-Stlc.HasType.interp_transport_inner _ _ rfl HB.stlc_ty_subst.symm]
          exact (interp_eq_none' Hri).symm
      | none => exact Hl.term_regular.denote_ty_non_null Il'
    | @let_pair Γ A B C e e' k He HA HB HC He' Ie IA IB IC Ie' =>
      cases k with
      | type => sorry
      | prop => sorry
    | inj_l He HB Ie IB => 
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
      cases k with
      | type => 
        dsimp only [denote']
        dsimp only [Term.stlc, Term.stlc_ty, stlc_ty, Stlc.HasType.interp]
        have HAB: Γ ⊢ Term.coprod A B: type := HasType.coprod HA HB;
        have Ie' := Ie HΓ G HG;
        dsimp only [Term.stlc, Term.stlc_ty, stlc_ty, Stlc.HasType.interp] at Ie';
        generalize Hei: Stlc.HasType.interp (_ : _⊧Term.stlc e _:_) _ = ei;
        --TODO: wait for Zulip to answer regarding the requirement to have
        -- Stlc.HasType.interp_irrel here.
        rw [Stlc.HasType.interp_irrel] at Ie'
        rw [Hei] at Ie'
        cases ei with
        | some e => 
          cases e with
          | inl a => 
            simp only [Ty.interp.case]
            sorry --TODO: appropriate typecasting for Il
          | inr b => 
            simp only [Ty.interp.case]
            sorry --TODO: appropriate typecasting for Il
        | none => exact False.elim (HAB.denote_ty_non_null Ie')
      | prop => 
        dsimp only [denote']
        sorry
    | elem => sorry
    | let_set => sorry
    | lam_pr => sorry
    | app_pr HφA Hl Hr IφA Il Ir => 
      dsimp only [denote', Term.denote_ty, Term.denote_ty']
      sorry
    | lam_irrel => sorry
    | app_irrel => sorry
    | @repr Γ A B l r HAB Hl Hr IAB Il Ir =>
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      apply And.intro
      . sorry -- not_none + Ir?
      . exists Hl.stlc.interp G.downgrade
        sorry
    | let_repr => sorry
    | abort Hp HA Ip IA => exact False.elim (Ip HΓ G HG)
    | dconj => sorry
    | let_conj => sorry
    | disj_l He HB Ie IB => exact Or.inl (Ie HΓ G HG)
    | disj_r He HB Ie IB => exact Or.inr (Ie HΓ G HG)
    | case_pr He HA HB HC Hl Hr Ie IA IB IC Il Ir => 
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      have Ie' := Ie HΓ G HG;
      cases Ie' with
      | inl Ie' => sorry
      | inr Ie' => sorry
    | imp => sorry
    | mp => sorry
    | general => sorry
    | inst => sorry
    | @wit Γ A φ l r HAφ Hl Hr IAφ Il Ir =>
      exists Hl.stlc.interp G
      --TODO: upgrade theorems for IsCtx and context denotation
      have Il' := Il HΓ.upgrade (Context.upgrade_idem.symm ▸ G) HG.upgrade;
      apply And.intro
      . dsimp only [denote', Term.denote_ty'] at Il'
        sorry
      . sorry
    | let_wit => sorry
    | refl Ha => exact ⟨Ha.stlc, Ha.stlc, rfl⟩
    | sym HA => exact HA.sym_axiom
    | trans HA => exact HA.trans_axiom 
    | cong => 
      dsimp only [denote', Annot.denote]
      sorry
    | beta => 
      dsimp only [denote', Annot.denote]
      sorry
    | @eta Γ A B f Hf HA If IA => 
      have px
        : Γ.upgrade.stlc ⊧ (Term.eta_ex A B f).stlc Γ.upgrade.sparsity
          : Ty.arrow A.stlc_ty B.stlc_ty 
        := sorry;
      have py
        : Γ.upgrade.stlc ⊧ f.stlc Γ.upgrade.sparsity
          : Ty.arrow A.stlc_ty B.stlc_ty 
        := sorry;
      --TODO: get rid of double upgrade...
      have If' := If HΓ.upgrade (Context.upgrade_idem.symm ▸ G) HG.upgrade;
      have HAB := Hf.term_regular;
      have ⟨yi, Hyi⟩ := HAB.denote_ty_some If';
      dsimp only [denote'] at If';
      exists px, py;
      unfold Term.eta_ex
      dsimp only [Term.stlc_ty, Stlc.HasType.interp, Term.stlc]
      simp only []
      sorry
    | irir Hf Hx Hy => exact ⟨sorry, sorry, rfl⟩
    | prir Hf Hx Hy => exact ⟨sorry, sorry, rfl⟩
    | succ => 
      intro x H;
      cases x with
      | none => cases H
      | some x => exact True.intro
    | @natrec Γ C e z s k HC He Hz Hs IC Ie Iz Is => sorry
    | _ => exact True.intro
  }