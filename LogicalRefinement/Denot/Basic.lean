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
    --TODO: this should probably be a forall; makes life a little easier...
    ∃ px: Γ ⊧ x.stlc σ: A.stlc_ty, 
    ∃ py: Γ ⊧ y.stlc σ: A.stlc_ty,
    px.interp G = py.interp G
  | const TermKind.nats => 
    match a with
    | some _ => True
    | none => False
  | _ => False

abbrev Term.denote_prop (A: Term) 
  {Γ: Stlc.Context}
  (σ: Sparsity)
  (G: Γ.interp): Prop
  := A.denote_ty σ G none

abbrev Term.denote_ty' (A: Term) {Γ: Context}
  (G: Γ.upgrade.stlc.interp)
  (a: A.stlc_ty.interp): Prop
  := A.denote_ty Γ.upgrade.sparsity G a

abbrev Term.denote_prop' (A: Term) {Γ: Context}
  (G: Γ.upgrade.stlc.interp): Prop
  := A.denote_prop Γ.upgrade.sparsity G

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

theorem HasType.denote_ty_non_null 
  {Γ} {Δ: Stlc.Context} {G: Δ.interp} {A σ}:
  (Γ ⊢ A: type) ->
  ¬(A.denote_ty σ G none)
  := by {
    generalize HS: sort type = S;
    intro HA;
    induction HA with
    | set _ _ IA _ => 
      dsimp only [Term.denote_ty]
      intro ⟨HA, _⟩;
      exact IA rfl HA
    | assume => 
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

--TODO: report spurious unused variable warning
theorem HasType.denote_ty_some {Δ: Stlc.Context} {G: Δ.interp}
  (H: Γ ⊢ A: type)
  (D: A.denote_ty σ G a)
  : ∃a': A.stlc_ty.interp_val, a = some a'
  := match a with
    | some a => ⟨a, rfl⟩
    | none => False.elim (H.denote_ty_non_null D)

--TODO: report spurious unused variable warning
abbrev Annot.denote (A: Annot) {Γ: Stlc.Context}
  (σ: Sparsity)
  (G: Γ.interp)
  (a: A.stlc_ty.interp): Prop
  := match A with
  | sort _ => True
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

def Context.denote: (Γ: Context) -> Γ.upgrade.stlc.interp -> Prop
| [], () => True
| (Hyp.mk A (HypKind.val type))::Γ, (a, G) => 
  A.denote_ty (upgrade Γ).sparsity G a ∧ denote Γ G
| (Hyp.mk φ (HypKind.val prop))::Γ, G =>
  φ.denote_ty (upgrade Γ).sparsity G none ∧ denote Γ G
| (Hyp.mk A HypKind.gst)::Γ, (a, G) =>
  A.denote_ty (upgrade Γ).sparsity G a ∧ denote Γ G

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