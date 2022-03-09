import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
open Untyped
open Annot
open AnnotSort

inductive WkCtx: Wk -> Context -> Context -> Type
  | id: WkCtx Wk.id Γ Γ
  | step {ρ Γ Δ H}: WkCtx ρ Γ Δ -> WkCtx ρ.step (H::Γ) Δ 
  | lift {ρ Γ Δ k} {A: Untyped}: WkCtx ρ Γ Δ 
    -> WkCtx ρ.lift ((Hyp.mk (A.wk ρ) k)::Γ) ((Hyp.mk A k)::Δ)

def WkCtx.lift_loose: 
  ρ' = ρ.lift -> A' = A.wk ρ -> WkCtx ρ Γ Δ -> WkCtx ρ' ((Hyp.mk A' k)::Γ) ((Hyp.mk A k)::Δ) := by {
    intro Hρ HA R;
    rw [Hρ, HA];
    exact WkCtx.lift R
  }

def WkCtx.wk1 {Γ H}: WkCtx Wk.wk1 (H::Γ) Γ := WkCtx.step WkCtx.id

theorem WkCtx.upgrade: WkCtx ρ Γ Δ 
  -> WkCtx ρ Γ.upgrade Δ.upgrade := by {
  intro R;
  induction R with
  | id => exact id
  | step R => apply step; assumption
  | lift R =>
    simp only [Context.upgrade, Hyp.upgrade_wk_commute]
    apply lift <;> assumption
}

theorem HasVar.wk:
  (ρ: Wk) -> {Γ Δ: Context} -> (Hs: WkCtx ρ Γ Δ) ->
  {n: Nat} -> {A: Untyped} -> {s: HypKind} ->
  HasVar Δ A s n -> HasVar Γ (A.wk ρ) s (ρ.var n) 
  := by {
    intros ρ;
    induction ρ <;> intro Γ Δ R <;> cases R;
    case id => 
      intros n A s H;
      simp [H] 
    case step ρ I Γ H R =>
      intros n A s HΔ;
      simp only [Untyped.step_wk1]
      exact var_succ (I R HΔ)
    case lift ρ I Γ Δ k A R =>
      intros n A s HΔ;
      cases HΔ with
      | var0 =>
        simp only [
          Wk.lift,
          Untyped.wk_composes,
          Wk.var, Untyped.lift_wk1
        ]
        apply var0
        assumption
      | var_succ =>
        simp only [
          Wk.lift,
          Untyped.wk_composes,
          Wk.var, Nat.add, Untyped.lift_wk1
        ]
        apply var_succ
        apply I
        apply R
        assumption
  } 

theorem HasType.wk {Δ a A} (HΔ: Δ ⊢ a: A):
  {ρ: Wk} -> {Γ: Context} -> WkCtx ρ Γ Δ ->
  (Γ ⊢ (a.wk ρ): (A.wk ρ)) := by {
    induction HΔ;
    case var I =>
      intros
      apply var
      apply I
      assumption
      apply HasVar.wk
      repeat assumption

    all_goals (
      intro ρ Γ R;
      rename_i' I5 I4 I3 I2 I1 I0;
      simp only [
        Annot.sym_ty_wk,
        Annot.trans_ty_wk
      ]
      simp only [Annot.wk, term, proof, implies_wk, const_arrow_wk, assume_wf_subst] at *
      try rw [eta_ex_eq_wk]
      simp only [Untyped.wk, Untyped.subst0_wk, Untyped.wk1] at *
      constructor <;>
      (try rw [Untyped.alpha00_wk_comm (by simp)]) <;>
      (try rw [Untyped.let_bin_ty_alpha_wk_pair]) <;>
      (try rw [Untyped.let_bin_ty_alpha_wk_elem]) <;>
      (try rw [Untyped.let_bin_ty_alpha_wk_repr]) <;>
      (try rw [Untyped.let_bin_ty_alpha_wk_wit]) <;>
      (try rw [Untyped.var2_var1_alpha_wk]) <;>
      (first | apply I0 | apply I1 | apply I2 | apply I3 | apply I4 | apply I5) <;> 
      simp only [<-Hyp.wk_components] <;> 
      first 
      | exact R
      | (exact R.upgrade)
      | {
        repeat (apply WkCtx.lift_loose rfl; rfl)
        exact R
      }
    )
  }

def HasType.wk1 {H} (Ha: Γ ⊢ a: A): (H::Γ) ⊢ a.wk1: A.wk1 
:= wk Ha WkCtx.wk1

def HasType.wk1_sort {H} (Ha: Γ ⊢ a: sort s): (H::Γ) ⊢ a.wk1: sort s 
:= wk Ha WkCtx.wk1