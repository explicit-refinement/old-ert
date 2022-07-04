import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.Subst
open Annot
open AnnotSort

theorem Term.wk_stlc_commute {ρ}
  (a: Term)
  : (a.wk ρ).stlc
  = a.stlc.wk ρ
  := by {
    induction a generalizing ρ with
    | var => rfl
    | const c => cases c <;> rfl
    | unary k t I => 
      (cases k <;> try rfl)
      rename Fin 2 => b;
      match b with
      | 0 => dsimp only [stlc]; rw [I]; rfl
      | 1 => dsimp only [stlc]; rw [I]; rfl
    | _ => 
      rename TermKind _ => k;
      cases k <;>
      (try rename AnnotSort => k <;> cases k) <;>
      dsimp only [stlc, Stlc.wk, Wk.liftn] <;>
      simp only [Term.stlc_ty_wk, *]
  }