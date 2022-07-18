import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc

open AnnotSort
open Annot

-- NOTE: this can't be an inductive type as far as I can tell, since'
-- the type former for pi is not strictly positive.
-- TODO: report spurious unused variable warning...
def Term.denote_ty (A: Term) 
  {Γ: Stlc.Context}
  (G: Γ.interp)
  (a: Option A.stlc_ty.interp): Prop
  := match A with
  | const TermKind.unit => 
    match a with
    | some () => True
    | none => False
  | abs TermKind.pi A B => 
    match a with
    | some a =>
      ∀x: Option A.stlc_ty.interp,
        A.denote_ty G x ->
        @denote_ty B (A.stlc_ty::Γ) (x, G) (x.bind a)
    | none => False
  | abs TermKind.sigma A B => 
    match a with
    | some (a, b) => 
      let a := return a;
      let b := return b;
      A.denote_ty G a ∧ @denote_ty B (A.stlc_ty::Γ) (a, G) b
    | none => False
  | bin TermKind.coprod A B =>
    match a with
    | some a => 
      match a with
      | Sum.inl a => A.denote_ty G (return a)
      | Sum.inr b => B.denote_ty G (return b)
    | none => False
  | abs TermKind.assume φ A =>
    match a with
    | some a =>
      (φ.denote_ty G none -> @denote_ty A (φ.stlc_ty::Γ) (none, G) (a ()))
    | none => False
  | abs TermKind.set A φ => 
    A.denote_ty G a ∧ @denote_ty φ (A.stlc_ty::Γ) (a, G) none
  | abs TermKind.intersect A B =>
    match a with
    | some a =>
      ∀x: Option A.stlc_ty.interp,
        A.denote_ty G x ->
        @denote_ty B (A.stlc_ty::Γ) (x, G) (a ())
    | none => False
  | abs TermKind.union A B =>
    ∃x: Option A.stlc_ty.interp,
      A.denote_ty G x ∧
      @denote_ty B (A.stlc_ty::Γ) (x, G) a
  | const TermKind.top => True
  | const TermKind.bot => False
  | abs TermKind.dimplies A B => 
    (A.denote_ty G none) -> (@denote_ty B (A.stlc_ty::Γ) (none, G) none)
  | abs TermKind.dand A B =>
    A.denote_ty G none ∧ @denote_ty B (A.stlc_ty::Γ) (none, G) none
  | bin TermKind.or A B => 
    A.denote_ty G none ∨ B.denote_ty G none
  | abs TermKind.forall_ A φ => 
    ∀x: Option A.stlc_ty.interp,
      A.denote_ty G x ->
      @denote_ty φ (A.stlc_ty::Γ) (x, G) none
  | abs TermKind.exists_ A φ => 
    ∃x: Option A.stlc_ty.interp,
      A.denote_ty G x ∧
      @denote_ty φ (A.stlc_ty::Γ) (x, G) none
  | tri TermKind.eq A x y => 
    --TODO: this should probably be a forall; makes life a little easier...
    ∃ px: Γ ⊧ x.stlc: A.stlc_ty, 
    ∃ py: Γ ⊧ y.stlc: A.stlc_ty,
    px.interp G = py.interp G
  | const TermKind.nats => 
    match a with
    | some _ => True
    | none => False
  | _ => False

theorem Term.denote_ctx_cast {A Γ} {X X': Ty} {x G a} 
  (H: X = X'):
  @Term.denote_ty A (X'::Γ) (cast (by cases H; rfl) x, G) a
  = @Term.denote_ty A (X::Γ) (x, G) a
  := by cases H; rfl

abbrev Term.denote_prop (A: Term) 
  {Γ: Stlc.Context}
  (G: Γ.interp): Prop
  := A.denote_ty G none

theorem HasType.denote_prop_eq {Γ Γs G} {A: Term} {a}
  (HA: HasType Γ A prop)
  : @Term.denote_ty A Γs G a = A.denote_prop G
  := by {
    generalize Hs: sort prop = s;
    rw [Hs] at HA;
    induction HA with
    | _ => first | rfl | cases Hs
  }

theorem HasType.denote_prop_eq' {Γ Γs G} {A: Term} {a a'}
  (HA: HasType Γ A prop)
  : @Term.denote_ty A Γs G a =  @Term.denote_ty A Γs G a'
  := by {
    generalize Hs: sort prop = s;
    rw [Hs] at HA;
    induction HA with
    | _ => first | rfl | cases Hs
  }
  
theorem HasType.denote_prop_none {Γ Γs G} {A: Term} {a}
  (HA: HasType Γ A prop)
  : @Term.denote_ty A Γs G a -> A.denote_prop G
  := by {
    rw [HA.denote_prop_eq]
    exact λx => x
  }

notation G "⊧" a "∈" A => Term.denote_ty A G a

theorem Term.denote_ty_transport 
  {A: Term} {Γ G} {a: Option A.stlc_ty.interp}
  {A' Γ' G' a'}
  (HA: A = A')
  (HΓ: Γ = Γ')
  (HG: G = HΓ ▸ G')
  (Ha: a' = HA ▸ a)
  : @denote_ty A Γ G a -> @denote_ty A' Γ' G' a'
  := by {
    cases HA;
    cases HΓ;
    cases HG;
    cases Ha;
    exact id
  }

theorem HasType.denote_ty_non_null 
  {Γ} {Δ: Stlc.Context} {G: Δ.interp} {A}:
  (Γ ⊢ A: type) ->
  ¬(A.denote_ty G none)
  := by {
    generalize HS: sort type = S;
    intro HA;
    induction HA generalizing Δ with
    | set _ _ IA _ => 
      dsimp only [Term.denote_ty]
      intro ⟨HA, _⟩;
      exact IA rfl HA
    | union _ _ _ IB => 
      intro ⟨_, _, Hn⟩
      exact IB rfl Hn
    | _ => cases HS <;> intro H <;> cases H
  }

--TODO: report spurious unused variable warning
theorem HasType.denote_ty_some {Δ: Stlc.Context} {G: Δ.interp}
  (H: Γ ⊢ A: type)
  (D: A.denote_ty G a)
  : ∃a': A.stlc_ty.interp, a = some a'
  := match a with
    | some a => ⟨a, rfl⟩
    | none => False.elim (H.denote_ty_non_null D)

--TODO: report spurious unused variable warning
abbrev Annot.denote (A: Annot) {Γ: Stlc.Context}
  (G: Γ.interp)
  (a: Option A.stlc_ty.interp): Prop
  := match A with
  | sort _ => True
  | expr type A => A.denote_ty G a
  | expr prop A => A.denote_ty G a

notation G "⊧" a "∈" A => Annot.denote A G a

def Context.denote: (Γ: Context) -> Γ.upgrade.stlc.interp -> Prop
| [], () => True
| (Hyp.mk A (HypKind.val _))::Γ, (a, G) => 
  A.denote_ty G a ∧ denote Γ G
| (Hyp.mk A HypKind.gst)::Γ, (a, G) =>
  A.denote_ty G a ∧ denote Γ G

theorem Context.denote.upgrade_helper {Γ: Context}
  : Γ.denote = Context.upgrade_idem.symm ▸ Γ.upgrade.denote
  := by {
    induction Γ with
    | nil => rfl
    | cons H Γ I =>
      rw [rec_to_cast']
      cases H with
      | mk A k =>
        cases k <;> (
          simp only [denote]
          funext ⟨x, G⟩;
          rw [cast_lam]
          apply congr (congr rfl _) _;
          rw [Context.upgrade_idem]
          rw [cast_pair' rfl (by rw [Context.upgrade_idem])]
          {
            simp only []
            apply congr _ rfl;
            let f: 
              (Γ : Stlc.Context) → Stlc.Context.interp Γ → 
              Option (Ty.interp (Term.stlc_ty A)) ->
              Prop
              := @Term.denote_ty A;
            have H: @Term.denote_ty A = f := rfl;
            rw [H]
            rw [cast_app_dep_first f]
            rw [Context.upgrade_idem]
          }
          {
            rw [I]
            rw [rec_to_cast', cast_pair']
            simp only []
            rw [cast_app_prop]
            rw [Context.upgrade_idem]
            rfl
          }
        )
  }

theorem Context.denote.upgrade_eq {Γ: Context} {G}
  : Γ.denote G = Γ.upgrade.denote (Context.upgrade_idem.symm ▸ G)
  := by {
    rw [Context.denote.upgrade_helper]
    rw [rec_to_cast']
    rw [rec_to_cast']
    rw [cast_app_prop]
  }

theorem Context.denote.upgrade {Γ: Context} {G}
  : Γ.denote G -> Γ.upgrade.denote (Context.upgrade_idem.symm ▸ G)
  := by {
    rw [Context.denote.upgrade_eq]
    exact id
  }

theorem Term.denote_upgrade_eq {Γ: Context} {G: Γ.upgrade.stlc.interp} {A a}:
  @Term.denote_ty A Γ.upgrade.stlc G a =
  @Term.denote_ty A Γ.upgrade.upgrade.stlc (Context.upgrade_idem.symm ▸ G) a
  := by {
    apply cast_app_dep_two (@Term.denote_ty A);
    rfl
    rw [Context.upgrade_idem]
    rw [rec_to_cast']
    rw [cast_merge]
    rfl
  }

theorem Term.denote_upgrade_eq_cast {Γ: Context} {G: Γ.upgrade.stlc.interp} {A a}:
  @Term.denote_ty A Γ.upgrade.stlc G a =
  @Term.denote_ty A Γ.upgrade.upgrade.stlc (cast (by rw [Context.upgrade_idem]) G) a
  := by {
    apply cast_app_dep_two (@Term.denote_ty A);
    rfl
    rw [Context.upgrade_idem]
    rw [cast_merge]
    rfl
  }


theorem HasType.succ_nat_stlc_denote {Γ Γ' e G D} 
  (H: Γ ⊢ e: term Term.nats) 
  (HD: @Term.denote_ty Term.nats Γ' G (H.stlc.interp D)):
  Term.nats.denote_ty G (H.succ_nat.stlc.interp D)
  := by {
    generalize HSe: H.stlc.interp D = Se;
    rw [HSe] at HD
    cases Se with
    | none => exact HD.elim
    | some Se =>
      dsimp only [Term.succ_nat]
      rw [Stlc.HasType.interp_app]
      rw [HSe]
      exact True.intro
      constructor
      rfl
  }

notation G "⊧" "✓" Γ => Context.denote Γ G

theorem denote_ty_cast_spine 
  {A B Γ Δ} {G: Γ.interp} {D: Δ.interp} {a b}
  (HAB: A = B)
  (HΓΔ: Γ = Δ)
  (HGD: G = HΓΔ ▸ D)
  (Hab: a = HAB ▸ b):
  @Term.denote_ty A Γ G a = @Term.denote_ty B Δ D b
  := by {
    cases HAB;
    cases HΓΔ;
    cases HGD;
    cases Hab;
    rfl
  }

theorem Term.denote_ty.inl {A B: Term} {Γ: Stlc.Context} 
  {G: Γ.interp} 
  {a: A.stlc_ty.interp} 
  (H: A.denote_ty G (some a))
  : ((A.coprod B).denote_ty G (some (Sum.inl a)))
  := by {
    dsimp only [Term.denote_ty]
    exact H
  }