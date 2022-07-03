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
    induction H generalizing s with
    | pi HA HB IA IB => 
      cases a with
      | none => rfl
      | some a => 
        dsimp only [Term.denote_ty]
        apply forall_helper;
        intro x;
        apply arrow_equivalence;
        apply IA;
        apply HGG';
        rfl
        apply IB;
        exact HGG'.extend
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