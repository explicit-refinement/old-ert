import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc
import LogicalRefinement.Denot.Basic

open AnnotSort
open Annot

theorem HasType.eq_lrt_ty_denot
  {Γ: Context} {A a s} {G G': Γ.upgrade.stlc.interp}
  (H: Γ ⊢ A: sort s)
  (HGG': G.eq_mod_lrt G' Γ.upgrade)
  : A.denote_ty G a = A.denote_ty G' a
  := by {
    generalize HS: sort s = S;
    rw [HS] at H;
    induction H with
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
    | eq HA Hl Hr => 
      dsimp only [Term.denote_ty]
      apply existential_helper;
      apply Or.inr;
      funext Hx';
      apply existential_helper;
      apply Or.inr;
      funext Hy';
      exact congr 
        (congr rfl (Hl.interp_irrel HGG')) 
        (Hr.interp_irrel HGG')
    | _ => cases HS <;> rfl
  }