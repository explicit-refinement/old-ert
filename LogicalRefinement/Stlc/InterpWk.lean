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

theorem Term.wk1_stlc_commute
  (a: Term)
  : a.wk1.stlc
  = a.stlc.wk1
  := a.wk_stlc_commute

theorem WkCtx.stlc {ρ Γ Δ} (R: WkCtx ρ Γ Δ): Stlc.WkCtx ρ Γ.stlc Δ.stlc
  := by {
    induction R with
    | id => constructor
    | step => simp [Context.stlc_hyp]; constructor <;> assumption
    | lift => 
      --TODO: clean?
      rename HypKind => k;
      cases k <;>
      simp [Context.stlc_hyp, Hyp.stlc, Term.stlc_ty_wk] <;>
      apply Stlc.WkCtx.lift <;>
      assumption
  }

theorem HasType.wk_stlc_interp_commute {Γ Δ ρ a} 
  (H: Δ ⊢ a: term A) 
  (R: WkCtx ρ Γ Δ)
  (G: Γ.stlc.interp)
  : H.stlc.interp.wk R.stlc G
  = Annot.stlc_ty_wk ▸ (H.wk R).stlc.interp G
  := by {
    rw [<-Stlc.HasType.interp_wk]
    rw [rec_to_cast']
    rw [Stlc.HasType.interp_transport_cast']
    rw [Term.wk_stlc_commute]
    rw [Annot.stlc_ty_wk]
  }

theorem HasType.wk_stlc_interp_commute' {Γ Δ ρ a} 
  (H: Δ ⊢ a: term A) 
  (H': Γ ⊢ a.wk ρ: term (A.wk ρ))
  (R: WkCtx ρ Γ Δ)
  (G: Γ.stlc.interp)
  : H'.stlc.interp G
  = Annot.stlc_ty_wk.symm ▸ H.stlc.interp.wk R.stlc G
  := by {
    rw [<-Stlc.HasType.interp_wk]
    rw [rec_to_cast']
    rw [Stlc.HasType.interp_transport_cast']
    rw [Term.wk_stlc_commute]
    rw [Annot.stlc_ty_wk]
  }