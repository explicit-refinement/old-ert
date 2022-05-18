import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc
import LogicalRefinement.Denot.Basic

open AnnotSort
open Annot

def ValidSubst {Γ Δ: Context} 
  (I: Stlc.InterpSubst Γ.upgrade.stlc Δ.upgrade.stlc): Prop 
  := ∀G, (G ⊧ ✓Γ) -> (I.transport_ctx G ⊧ ✓Δ)

theorem SubstCtx.subst_denot
  {Γ Δ: Context} {σ} {G: Γ.upgrade.stlc.interp} {A: Term} {a s}
  (S: SubstCtx σ Γ Δ)
  (IΓ: IsCtx Γ) (IΔ: IsCtx Δ)
  (HG: G ⊧ ✓Γ)
  (V: ValidSubst (S.interp_up IΔ))
  (HA: Δ ⊢ A: sort s)
  : 
    A.denote_ty Δ.upgrade.sparsity (S.transport_interp_up IΔ G) a =
    (A.subst σ).denote_ty Γ.upgrade.sparsity G (HA.stlc_ty_subst ▸ a)
  := by {
    generalize HK: sort s = K;
    rw [HK] at HA;
    induction HA generalizing σ s with
    | pi => 
      cases a with
      | none => sorry
      | some a => sorry
    | sigma => 
      cases a with
      | none => sorry
      | some a => sorry
    | coprod => 
      cases a with
      | none => sorry
      | some a => sorry
    | assume => 
      cases a with
      | none => sorry
      | some a => sorry
    | set => 
      cases a with
      | none => sorry
      | some a => sorry
    | intersect => 
      cases a with
      | none => sorry
      | some a => sorry
    | union => 
      cases a with
      | none => sorry
      | some a => sorry
    | dimplies => 
      cases a with
      | none => sorry
      | some a => cases a
    | dand => 
      cases a with
      | none => sorry
      | some a => cases a
    | or => 
      cases a with
      | none => sorry
      | some a => cases a
    | forall_ => 
      cases a with
      | none => sorry
      | some a => cases a
    | exists_ => 
      cases a with
      | none => sorry
      | some a => cases a
    | @eq Γ A l r HA' Hl Hr IA Il Ir => 
      cases a with
      | none => 
        dsimp only [Term.denote_ty];
        apply propext;
        apply Iff.intro
        {
          intro ⟨px, py, Hxy⟩;
          exists (Hl.subst S.upgrade).stlc;
          exists (Hr.subst S.upgrade).stlc;
          rw [Hl.subst_stlc_interp_up_commute S IΔ G]
          rw [Hr.subst_stlc_interp_up_commute S IΔ G]
          dsimp only [transport_interp_up] at Hxy;
          rw [rec_down]
          exact Hxy
        }
        {
          intro ⟨px, py, Hxy⟩;
          exists Hl.stlc;
          exists Hr.stlc;
          sorry
        }
      | some a => cases a
    | _ => cases HK <;> cases a <;> rfl
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

theorem HasType.denote_antisubst0'
  {A: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} {a: A.stlc_ty.interp}
  {B: Term} {b: Term}
  {a': (A.subst0 b).stlc_ty.interp}
  {b'}
  (HA: Γ ⊢ A: S)
  (HS: S = sort s)
  (Hb: Γ ⊢ b: term B)
  (HAA': A.stlc_ty = (A.subst0 b).stlc_ty)
  (Haa': a' = HAA' ▸ a)
  (Hbb': b' = Hb.stlc.interp G.downgrade)
  (H: @Term.denote_ty (A.subst0 b) Γ.upgrade.stlc σ G a')
  : @Term.denote_ty A (B.stlc_ty::Γ.upgrade.stlc) (true::σ) (b', G) a
  := sorry