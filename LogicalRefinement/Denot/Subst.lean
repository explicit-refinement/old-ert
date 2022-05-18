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
  (Ha: A.denote_ty Δ.upgrade.sparsity (S.transport_interp_up IΔ G) a)
  (HG: G ⊧ ✓Γ)
  (V: ValidSubst (S.interp_up IΔ))
  (HA: Δ ⊢ A: sort s)
  : (A.subst σ).denote_ty 
    Γ.upgrade.sparsity
    G
    (HA.stlc_ty_subst ▸ a)
  := by {
    generalize HK: sort s = K;
    rw [HK] at HA;
    induction HA generalizing σ s with
    | pi => sorry
    | sigma => sorry
    | coprod => sorry
    | assume => sorry
    | set => sorry
    | intersect => sorry
    | union => sorry
    | top => sorry
    | bot => sorry
    | dimplies => sorry
    | dand => sorry
    | or => sorry
    | forall_ => sorry
    | exists_ => sorry
    | @eq Γ A l r HA' Hl Hr IA Il Ir => 
      cases a with
      | none => 
        dsimp only [Term.denote_ty];
        exists (Hl.subst S.upgrade).stlc;
        exists (Hr.subst S.upgrade).stlc;
        simp only [Term.subst_stlc_commute Hl S.upgrade]
        sorry
      | some a => cases a
    | _ => 
      cases HK <;>
      cases a with
      | none => cases Ha
      | some => exact True.intro
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