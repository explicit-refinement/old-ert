import Std.Tactic.SolveByElim

import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic

open Term
open Annot
open AnnotSort

inductive WkCtx: Wk -> Context -> Context -> Type
  | id: WkCtx Wk.id Γ Γ
  | step {ρ Γ Δ H}: WkCtx ρ Γ Δ -> WkCtx ρ.step (H::Γ) Δ
  | lift {ρ Γ Δ k} {A: Term}: WkCtx ρ Γ Δ
    -> WkCtx ρ.lift ((Hyp.mk (A.wk ρ) k)::Γ) ((Hyp.mk A k)::Δ)

def WkCtx.lift_loose:
  ρ' = ρ.lift -> A' = A.wk ρ -> WkCtx ρ Γ Δ
  -> WkCtx ρ' ((Hyp.mk A' k)::Γ) ((Hyp.mk A k)::Δ) := by {
    intro Hρ HA R;
    rw [Hρ, HA];
    exact WkCtx.lift R
  }

def WkCtx.wk1 {Γ H}: WkCtx Wk.wk1 (H::Γ) Γ := WkCtx.step WkCtx.id
def WkCtx.wk2 {Γ A k X}: WkCtx (Wk.wknth 1) ((Hyp.mk A.wk1 k)::X::Γ) ((Hyp.mk A k)::Γ) :=
  WkCtx.lift WkCtx.wk1

theorem WkCtx.upgrade: WkCtx ρ Γ Δ
  -> WkCtx ρ Γ.upgrade Δ.upgrade := by {
  intro R;
  induction R with
  | id => exact id
  | step _ => apply step; assumption
  | lift R =>
    simp only [Context.upgrade, Hyp.upgrade_wk_commute]
    apply lift; assumption
}

theorem HasVar.wk:
  {ρ: Wk} -> {Γ Δ: Context} -> (Hs: WkCtx ρ Γ Δ) ->
  {n: Nat} -> {A: Term} -> {s: HypKind} ->
  HasVar Δ n s A -> HasVar Γ (ρ.var n) s (A.wk ρ)
  := by {
    intros ρ;
    induction ρ <;> intro Γ Δ R <;> cases R;
    case id =>
      intros n A s H;
      simp [H]
    case step ρ I Γ H R =>
      intros n A s HΔ;
      simp only [Term.step_wk1]
      exact HasVar.succ (I R HΔ)
    case lift ρ I Γ Δ k A R =>
      intros n A s HΔ;
      cases HΔ with
      | zero =>
        simp only [
          Wk.lift,
          Term.wk_composes,
          Wk.var, Term.lift_wk1
        ]
        apply HasVar.zero
      | succ =>
        simp only [
          Wk.lift,
          Term.wk_composes,
          Wk.var, Nat.add, Term.lift_wk1
        ]
        apply HasVar.succ
        apply I
        apply R
        assumption
  }

theorem HasVar'.wk:
  {ρ: Wk} -> {Γ Δ: Context} -> (Hs: WkCtx ρ Γ Δ) ->
  {n: Nat} -> {A: Term} -> {s: HypKind} ->
  HasVar' Δ n s A -> HasVar' Γ (ρ.var n) s (A.wk ρ)
  := by {
    intros ρ;
    induction ρ <;> intro Γ Δ R <;> cases R;
    case id =>
      intros n A s H;
      simp [H]
    case step ρ I Γ H R =>
      intros n A s HΔ;
      simp only [Term.step_wk1]
      exact HasVar'.succ (I R HΔ)
    case lift ρ I Γ Δ k A R =>
      intros n A s HΔ;
      cases HΔ with
      | zero =>
        simp only [
          Wk.lift,
          Term.wk_composes,
          Wk.var, Term.lift_wk1
        ]
        apply HasVar'.zero
        assumption
      | succ =>
        simp only [
          Wk.lift,
          Term.wk_composes,
          Wk.var, Nat.add, Term.lift_wk1
        ]
        apply HasVar'.succ
        apply I
        apply R
        assumption
  }


theorem Term.alpha0_natrec_wk_helper {C: Term} {ρ: Wk}:
  ((C.wk ρ.lift).wknth 1).alpha0 (Term.app (Term.arrow Term.nats Term.nats) Term.succ (Term.var 1))
  = ((C.wknth 1).alpha0 (Term.app (Term.arrow Term.nats Term.nats) Term.succ (Term.var 1))).wk (ρ.liftn 2)
  := by {
    simp only [
      subst01, wknth, alpha0, subst0,
      <-Subst.subst_wk_compat,
      subst_composes
    ]
    apply congr rfl;
    funext n;
    cases n <;> rfl
  }

theorem Term.pi_funext_helper {A B f: Term} {ρ: Wk}:
  Term.app
    (Term.wk1 (Term.pi (Term.wk A ρ) (Term.wk B (Wk.lift ρ))))
    (Term.wk1 (Term.wk f ρ))
    (Term.var 0)
  = tri TermKind.app
        (abs TermKind.pi (Term.wk (Term.wk A Wk.wk1) (Wk.lift ρ))
          (Term.wk (Term.wk B (Wk.lift Wk.wk1)) (Wk.lift (Wk.lift ρ))))
        (Term.wk (Term.wk f Wk.wk1) (Wk.lift ρ))
        (Term.var (Wk.var (Wk.lift ρ) 0))
  := by {
    apply congr _ rfl;
    apply congr;
    apply congr rfl _;
    simp only [wk1, wk]
    apply congr;
    apply congr rfl;
    simp
    simp
    rw [<-Term.lift_wk1]
    rfl
  }

theorem HasType.wk {ρ Γ Δ a A} (HΔ: Δ ⊢ a: A) (R: WkCtx ρ Γ Δ):
  (Γ ⊢ (a.wk ρ): (A.wk ρ)) := by {
    induction HΔ generalizing ρ Γ;
    case var I =>
      apply var
      apply I
      assumption
      apply HasVar.wk
      repeat assumption

    all_goals (
      rename_i' I5 I4 I3 I2 I1 I0;
      try simp only [
        Annot.sym_ty_wk,
        Annot.trans_ty_wk
      ]
      simp only [
        Annot.wk, term, proof, implies_wk, const_arrow_wk, assume_wf_wk
      ] at *
      try rw [eta_ex_eq_wk]
      try rw [irir_ex_eq_wk]
      try rw [prir_ex_eq_wk]
      simp only [
        Term.wk, Term.subst0_wk, Wk.subst01_wk, Term.wk1
      ] at *
      constructor <;>
      (try rw [Term.alpha00_wk_comm (by simp)]) <;>
      (try simp only [
        Term.let_bin_ty_alpha_wk_pair,
        Term.let_bin_ty_alpha_wk_elem,
        Term.let_bin_ty_alpha_wk_repr,
        Term.let_bin_ty_alpha_wk_wit,
        Term.var2_var1_alpha_wk,
        Term.let_bin_ty_alpha_wk_conj,
        Term.alpha0_natrec_wk_helper,
        Term.pi_funext_helper]) <;>
      (first | apply I0 | apply I1 | apply I2 | apply I3 | apply I4 | apply I5) <;>
      (try simp only [<-Hyp.wk_components]) <;>
      {
        repeat (apply WkCtx.lift_loose rfl; rfl)
        first | exact R | exact R.upgrade
      }
    )
  }

theorem HasType.wk_sort {ρ Γ Δ a s}
  (H: Δ ⊢ a: sort s) (R: WkCtx ρ Γ Δ):
  (Γ ⊢ (a.wk ρ): sort s) := H.wk R

theorem HasType.wk1 {H} (Ha: Γ ⊢ a: A): (H::Γ) ⊢ a.wk1: A.wk1
:= wk Ha WkCtx.wk1

theorem HasType.wk1_sort {H} (Ha: Γ ⊢ a: sort s): (H::Γ) ⊢ a.wk1: sort s
:= wk Ha WkCtx.wk1

theorem HasType.wk2 {A B k X} (Ha: ((Hyp.mk B k)::Γ) ⊢ a: A): ((Hyp.mk B.wk1 k)::X::Γ) ⊢ (a.wknth 1): (A.wk (Wk.wknth 1))
:= wk Ha WkCtx.wk2

theorem HasType.wk2_sort {k X} (Ha: ((Hyp.mk B k)::Γ) ⊢ a: sort s): ((Hyp.mk B.wk1 k)::X::Γ) ⊢ (a.wknth 1): sort s
:= wk Ha WkCtx.wk2

theorem IsCtx.var_valid' {Γ} (H: IsCtx Γ)
  : HasVar' Γ n k A -> Γ ⊢ A: k.annot
  := by {
    intro Hv;
    induction Hv with
    | zero =>
      cases H <;>
      apply HasType.wk1_sort <;>
      rename HypKind.is_sub _ _ => Hsub <;>
      cases Hsub <;>
      assumption
    | succ _Hk Hv =>
      apply HasType.wk1_sort
      apply Hv
      cases H <;> assumption
  }

theorem IsCtx.var_valid {Γ} (H: IsCtx Γ) (Hv: HasVar Γ n k A):
  Γ ⊢ A: k.annot
  := H.var_valid' Hv.v

theorem IsCtx.var {Γ} (H: IsCtx Γ) (Hv: HasVar Γ n (HypKind.val s) A)
  : Γ ⊢ var n: expr s A
  := HasType.var (H.var_valid Hv) Hv

theorem HasType.eta_ex_ty {Γ f A B}
  (HAB: Γ ⊢ Term.pi A B: type)
  (H: Γ ⊢ f: term (Term.pi A B))
  : Γ ⊢ eta_ex A B f: term (Term.pi A B)
  := by {
    constructor;
    conv =>
      arg 3
      rw [<-@Term.wknth1_subst0_var0 B]
    apply HasType.app;
    exact HAB.wk1;
    exact H.wk1;
    constructor;
    cases HAB with
    | pi HA => exact HA.wk1
    constructor
    cases HAB; assumption
  }
