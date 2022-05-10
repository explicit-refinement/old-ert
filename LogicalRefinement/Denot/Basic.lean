import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc

open AnnotSort
open Annot

def Term.denote_ty (A: Term) 
  {Γ: Stlc.Context}
  (σ: Sparsity)
  (G: Γ.interp)
  (a: A.stlc_ty.interp): Prop
  := match A with
  | const TermKind.unit => 
    match a with
    | some () => True
    | none => False
  | abs TermKind.pi A B => 
    match a with
    | some a =>
      ∀x: A.stlc_ty.interp,
        A.denote_ty σ G x ->
        @denote_ty B (A.stlc_ty::Γ) (true::σ) (x, G) (x.bind_val a)
    | none => False
  | abs TermKind.sigma A B => 
    match a with
    | some (a, b) => 
      let a := Ty.eager a;
      let b := Ty.eager b;
      A.denote_ty σ G a ∧ @denote_ty B (A.stlc_ty::Γ) (true::σ) (a, G) b
    | none => False
  | bin TermKind.coprod A B =>
    match a with
    | some a => 
      match a with
      | Sum.inl a => A.denote_ty σ G (Ty.eager a)
      | Sum.inr b => B.denote_ty σ G (Ty.eager b)
    | none => False
  | abs TermKind.assume φ A => 
    a ≠ none ∧
    ((φ.denote_ty σ G none) -> (A.denote_ty (false::σ) G a))
  | abs TermKind.set A φ => 
    A.denote_ty σ G a ∧ @denote_ty φ (A.stlc_ty::Γ) (true::σ) (a, G) none
  | abs TermKind.intersect A B => 
    a ≠ none ∧
    ∀x: A.stlc_ty.interp,
      A.denote_ty σ G x ->
      @denote_ty B (A.stlc_ty::Γ) (true::σ) (x, G) a
  | abs TermKind.union A B => 
    a ≠ none ∧
    ∃x: A.stlc_ty.interp,
      A.denote_ty σ G x ∧
      @denote_ty B (A.stlc_ty::Γ) (true::σ) (x, G) a
  | const TermKind.top => True
  | const TermKind.bot => False
  | abs TermKind.dimplies A B => 
    --TODO: think about this...
    (A.denote_ty σ G none) -> (B.denote_ty (false::σ) G none)
  | abs TermKind.dand A B =>
    --TODO: think about this...
    A.denote_ty σ G none ∧ B.denote_ty (false::σ) G none
  | bin TermKind.or A B => 
    A.denote_ty σ G none ∨ B.denote_ty σ G none
  | abs TermKind.forall_ A φ => 
    ∀x: A.stlc_ty.interp,
      A.denote_ty σ G x ->
      @denote_ty φ (A.stlc_ty::Γ) (true::σ) (x, G) none
  | abs TermKind.exists_ A φ => 
    ∃x: A.stlc_ty.interp,
      A.denote_ty σ G x ∧
      @denote_ty φ (A.stlc_ty::Γ) (true::σ) (x, G) none
  | tri TermKind.eq A x y => 
    ∃ px: Γ ⊧ x.stlc σ: A.stlc_ty, 
    ∃ py: Γ ⊧ y.stlc σ: A.stlc_ty,
    px.interp G = py.interp G
  | const TermKind.nats => 
    match a with
    | some _ => True
    | none => False
  | _ => False

def Term.denote_ty' (A: Term) {Γ: Context}
  (G: Γ.upgrade.stlc.interp)
  (a: A.stlc_ty.interp): Prop
  := A.denote_ty Γ.upgrade.sparsity G a

notation G "⊧" a "↓" σ "∈" A => Term.denote_ty A σ G a
notation G "⊧" a "∈" A => Term.denote_ty' A G a

theorem Term.denote_ty_transport 
  {A: Term} {Γ G} {a: A.stlc_ty.interp}
  {A' Γ' G' a'}
  (HA: A = A')
  (HΓ: Γ = Γ')
  (HG: G = HΓ ▸ G')
  (Ha: a' = HA ▸ a)
  : @denote_ty' A Γ G a -> @denote_ty' A' Γ' G' a'
  := by {
    cases HA;
    cases HΓ;
    cases HG;
    cases Ha;
    exact id
  }

theorem HasType.denote_ty_non_null {Δ: Stlc.Context} {G: Δ.interp}:
  (Γ ⊢ A: type) ->
  ¬(A.denote_ty σ G none)
  := by {
    generalize HS: sort type = S;
    intro HA;
    induction HA with
    | set _ _ IA Iφ => 
      dsimp only [Term.denote_ty]
      intro ⟨HA, Hφ⟩;
      exact IA rfl HA
    | assume _ _ Iφ IA => 
      intro ⟨H, _⟩;
      exact H rfl
    | intersect => 
      intro ⟨H, _⟩;
      exact H rfl
    | union => 
      intro ⟨H, _⟩;
      exact H rfl
    | _ => cases HS <;> intro H <;> cases H
  }

theorem interp_eq_none
  : @Eq.rec Ty a (λx _ => Ty.interp x) none x p = none := by {
    cases p <;> rfl
  }

theorem interp_eq_none' {n: Ty.interp a}
  : n = none -> @Eq.rec Ty a (λx _ => Ty.interp x) n x p = none := by {
    intro H;
    cases H <;>
    cases p <;> rfl
  }

theorem interp_eq_some
  : @Eq.rec Ty a (λx _ => Ty.interp x) (some v) x p = (some (p ▸ v)) := by {
    cases p <;> rfl
  }

theorem Term.denote_wk1_ty
  (A: Term) 
  (B: Term)
  (Γ: Context)
  (x: B.stlc_ty.interp) 
  (G: Γ.upgrade.stlc.interp) 
  (a: A.stlc_ty.interp)
  (a': A.wk1.stlc_ty.interp)
  (Haa': a' = A.stlc_ty_wk1 ▸ a)
  (H: A.denote_ty' G a) 
  : @denote_ty' A.wk1 ((Hyp.val B type)::Γ) (x, G) a'
  := sorry
  
theorem Term.denote_wk1_prop
  (A: Term) 
  (φ: Term)
  (Γ: Context)
  (G: Γ.upgrade.stlc.interp) 
  (a: A.stlc_ty.interp)
  (a': A.wk1.stlc_ty.interp)
  (Haa': a' = A.stlc_ty_wk1 ▸ a)
  (H: @denote_ty' A Γ G a) 
  : @denote_ty' A.wk1 ((Hyp.val φ prop)::Γ) G a'
  := sorry
  
theorem Term.denote_wk1_gst
  (A: Term) 
  (B: Term)
  (Γ: Context) 
  (x: B.stlc_ty.interp)
  (G: Γ.upgrade.stlc.interp) 
  (a: A.stlc_ty.interp)
  (a': A.wk1.stlc_ty.interp)
  (Haa': a' = A.stlc_ty_wk1 ▸ a)
  (H: A.denote_ty' G a) 
  : @denote_ty' A.wk1 ((Hyp.gst B)::Γ) (x, G) a'
  := sorry

abbrev Annot.denote (A: Annot) {Γ: Stlc.Context}
  (σ: Sparsity)
  (G: Γ.interp)
  (a: A.stlc_ty.interp): Prop
  := match A with
  | sort s => True
  | expr type A => A.denote_ty σ G a
  | expr prop A => A.denote_ty σ G none

abbrev Annot.denote' (A: Annot) (Γ: Context)
  (G: Γ.upgrade.stlc.interp)
  (a: A.stlc_ty.interp): Prop
  := match A with
  | sort s => True
  | expr type A => A.denote_ty' G a
  | expr prop A => A.denote_ty' G none

notation G "⊧" a "↓" σ "∈:" A => Annot.denote A σ G a
notation G "⊧" a "∈:" A => Annot.denote' A G a

-- NOTE: I don't think wk1 is necessary here, due to the fact that
-- A.wk1.stlc_ty = A.stlc_ty, and also that a is not passed to itself...
-- or something like that...
def Context.denote: (Γ: Context) -> Γ.upgrade.stlc.interp -> Prop
| [], () => True
| (Hyp.mk A (HypKind.val type))::Γ, (a, G) => 
  A.denote_ty (upgrade Γ).sparsity G a ∧ denote Γ G
| (Hyp.mk φ (HypKind.val prop))::Γ, G =>
  φ.denote_ty (upgrade Γ).sparsity G none ∧ denote Γ G
| (Hyp.mk A HypKind.gst)::Γ, (a, G) =>
  A.denote_ty (upgrade Γ).sparsity G a ∧ denote Γ G

--set_option pp.explicit true

theorem HasVar.denote_annot
  (Hv: HasVar Γ n (HypKind.val s) A)
  (HΓ: IsCtx Γ)
  (G: Γ.upgrade.stlc.interp)
  (HG: Γ.denote G)
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

theorem HasType.denote_subst0'
  {A: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} {a: A.stlc_ty.interp}
  {B: Term} {b: Term}
  {a': (A.subst0 b).stlc_ty.interp}
  {b'}
  (Hb: Γ ⊢ b: term B)
  (HAA': A.stlc_ty = (A.subst0 b).stlc_ty)
  (Haa': a' = HAA' ▸ a)
  (Hbb': b' = Hb.stlc.interp G.downgrade)
  (H: @Term.denote_ty A (B.stlc_ty::Γ.upgrade.stlc) (true::σ) (b', G) a)
  : @Term.denote_ty (A.subst0 b) Γ.upgrade.stlc σ G a'
  := sorry

theorem HasType.denote
  (H: Γ ⊢ a: A)
  (HΓ: IsCtx Γ)
  (G: Γ.upgrade.stlc.interp)
  (HG: Γ.denote G)
  : A.denote' Γ G (H.stlc.interp G.downgrade)
  := by {
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
      have HB: ((Hyp.val A type)::Γ) ⊢ B: type := by cases HAB; assumption;
      cases li with
      | some li => 
        cases ri with
        | some ri => 
          have Ilr := Il' (some ri) Ir';
          simp only []
          dsimp only [Annot.denote, Term.denote_ty, denote', Term.denote_ty'] at Il'
          dsimp only [Annot.denote, Term.denote_ty, denote']
          apply HasType.denote_subst0' Hr HB.stlc_ty_subst.symm _ Hrg.symm Ilr
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
    | let_pair => sorry
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
      stop
      dsimp only [
        denote', Term.denote_ty', Term.denote_ty, Term.stlc, 
        stlc_ty, Term.stlc_ty, Stlc.HasType.interp,
        Ty.interp.inl
      ]
      generalize Hei: Stlc.HasType.interp _ _ = ei;have Ie' := Hei ▸ Ie HΓ G HG;
      cases ei with
      | some ei => 
        dsimp only [Option.map, Option.bind, Function.comp]
        exact Ie'
      | none => exact He.term_regular.denote_ty_non_null Ie'
    | case => sorry
    | elem => sorry
    | let_set => sorry
    | lam_pr => sorry
    | app_pr => sorry
    | lam_irrel => sorry
    | app_irrel => sorry
    | repr => sorry
    | let_repr => sorry
    | abort => sorry
    | dconj => sorry
    | let_conj => sorry
    | disj_l => sorry
    | disj_r => sorry
    | case_pr => sorry
    | imp => sorry
    | mp => sorry
    | general => sorry
    | inst => sorry
    | @wit Γ A φ l r HAφ Hl Hr IAφ Il Ir => 
      dsimp only [denote', Term.denote_ty, Term.denote_ty']
      sorry
    | let_wit => sorry
    | refl Ha => exact ⟨Ha.stlc, Ha.stlc, rfl⟩
    | sym => 
      dsimp only [denote', Annot.denote]
      sorry
    | trans => 
      dsimp only [denote', Annot.denote]
      sorry
    | cong => 
      dsimp only [denote', Annot.denote]
      sorry
    | beta => 
      dsimp only [denote', Annot.denote]
      sorry
    | eta => 
      dsimp only [denote', Annot.denote]
      sorry
    | irir Hf Hx Hy => exact ⟨sorry, sorry, rfl⟩
    | prir Hf Hx Hy => exact ⟨sorry, sorry, rfl⟩
    | succ => 
      intro x H;
      cases x with
      | none => cases H
      | some x => exact True.intro
    | natrec => sorry
    | _ => exact True.intro
  }