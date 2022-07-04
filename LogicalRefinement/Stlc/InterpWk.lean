import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.Subst
open Annot
open AnnotSort

theorem Term.wk_stlc_commute {Γ Δ ρ}
  (a: Term)
  (R: WkCtx ρ Γ Δ)
  : (a.wk ρ).stlc
  = a.stlc.wk ρ
  := by {
    induction a generalizing ρ Γ Δ with
    | var => rfl
    | const c => cases c <;> rfl
    | unary k t I => 
      (cases k <;> try rfl)
      rename Fin 2 => b;
      match b with
      | 0 => dsimp only [stlc]; rw [I R]; rfl
      | 1 => dsimp only [stlc]; rw [I R]; rfl
    | _ => 
      rename TermKind _ => k;
      rename_i' I0 I1 I2 I3 I4;
      cases k <;>
      (try rename AnnotSort => k <;> cases k) <;>
      dsimp only [stlc, Stlc.wk, Wk.liftn] <;>
      simp only [Term.stlc_ty_wk] <;>
      (try rw [I0]) <;>
      (try rw [I1]) <;>
      (try rw [I2]) <;>
      (try rw [I3]) <;>
      (try rw [I4]) <;>
      repeat first | assumption | constructor
  }