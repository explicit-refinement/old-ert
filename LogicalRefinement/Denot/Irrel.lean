import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc
import LogicalRefinement.Denot.Basic

open AnnotSort
open Annot

theorem HasType.eq_lrt_ty_denot
  {Γ Δ: Context} {A a s} 
  {G: Γ.upgrade.stlc.interp}
  {D: Δ.upgrade.stlc.interp}
  (HΓ: Γ ⊢ A: sort s)
  (HΔ: Δ ⊢ A: sort s)
  (HGD: G.eq_mod_lrt D Γ.upgrade Δ.upgrade)
  : A.denote_ty G a = A.denote_ty D a
  := by {
    generalize HS: sort s = S;
    rw [HS] at HΓ;
    induction HΓ generalizing Δ with
    | pi HA HB IA IB =>
      cases HΔ; 
      cases a with
      | none => rfl
      | some a => 
        dsimp only [Term.denote_ty]
        apply forall_helper;
        intro x;
        apply arrow_equivalence;
        apply IA;
        assumption
        exact HGD;
        rfl
        apply @IB 
          ((Hyp.mk _ (HypKind.val type))::Δ) 
          (x.bind a) (x, G) (x, D);
        assumption
        exact HGD.extend
        rfl
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
    | eq HA Hl Hr => 
      cases HΔ with
      | eq HA' Hl' Hr' =>
        dsimp only [Term.denote_ty]
        apply propext;
        apply Iff.intro;
        {
          intro ⟨px, py, HG⟩;
          exists Hl'.stlc, Hr'.stlc;
          rw [<-Hl.interp_irrel Hl' HGD]
          rw [<-Hr.interp_irrel Hr' HGD]
          exact HG
        }
        {
          intro ⟨px, py, HG⟩;
          exists Hl.stlc, Hr.stlc;
          rw [Hl.interp_irrel Hl' HGD]
          rw [Hr.interp_irrel Hr' HGD]
          exact HG
        }
    | _ => cases HS <;> rfl
  }

theorem HasType.eq_lrt_ty_denot'
  {Γ: Context} {A a s} 
  {G D: Γ.upgrade.stlc.interp}
  (HΓ: Γ ⊢ A: sort s)
  (HGD: G.eq_mod_lrt D Γ.upgrade Γ.upgrade)
  : A.denote_ty G a = A.denote_ty D a
  := HΓ.eq_lrt_ty_denot HΓ HGD