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
      (φ.denote_ty G none -> A.denote_ty G (a ()))
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
    a ≠ none ∧
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
    induction HA with
    | set _ _ IA _ => 
      dsimp only [Term.denote_ty]
      intro ⟨HA, _⟩;
      exact IA rfl HA
    | union => 
      intro ⟨Hn, _⟩
      contradiction
    | _ => cases HS <;> intro H <;> cases H
  }

--TODO: report spurious unused variable warning
theorem HasType.denote_ty_some {Δ: Stlc.Context} {G: Δ.interp}
  (H: Γ ⊢ A: type)
  (D: A.denote_ty G a)
  : ∃a': Option A.stlc_ty.interp, a = some a'
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
| (Hyp.mk A (HypKind.val type))::Γ, (a, G) => 
  A.denote_ty G a ∧ denote Γ G
| (Hyp.mk φ (HypKind.val prop))::Γ, (a, G) =>
  φ.denote_ty G a ∧ denote Γ G
| (Hyp.mk A HypKind.gst)::Γ, (a, G) =>
  A.denote_ty G a ∧ denote Γ G

theorem Context.denote.upgrade_helper {Γ: Context}
  : Γ.denote = Context.upgrade_idem.symm ▸ Γ.upgrade.denote
  := sorry

theorem Context.denote.upgrade_eq {Γ: Context} {G}
  : Γ.denote G = Γ.upgrade.denote (Context.upgrade_idem.symm ▸ G)
  := by {
    rw [Context.denote.upgrade_helper]
    rw [rec_to_cast']
    rw [rec_to_cast']
    sorry
  }

theorem Context.denote.upgrade {Γ: Context} {G}
  : Γ.denote G -> Γ.upgrade.denote (Context.upgrade_idem.symm ▸ G)
  := by {
    rw [Context.denote.upgrade_eq]
    exact id
  }

notation G "⊧" "✓" Γ => Context.denote Γ G