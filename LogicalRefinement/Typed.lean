import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Wk
open Untyped
open Annot
open AnnotSort

--TODO: fill in with proper definition

inductive SubstVar: Subst -> Context -> Nat -> Untyped -> HypKind -> Prop
  | expr {σ Γ n A k}: (Γ ⊢ σ n: expr k.annot (A.subst σ)) -> SubstVar σ Γ n A k
  | var {σ Γ n A k m}: σ n = var m -> HasVar Γ (A.subst σ) k m -> SubstVar σ Γ n A k

def SubstCtx (σ: Subst) (Γ Δ: Context): Prop :=  
  ∀{n A k}, HasVar Δ A k n -> SubstVar σ Γ n A k

--TODO: this is inconsistent, fill in with proper definition
theorem SubstCtx.lift_primitive 
  {σ: Subst} {Γ Δ: Context} {A: Untyped} {k k': HypKind}:
  SubstCtx σ Γ Δ ->
  k.is_sub k' ->
  IsHyp Γ (Hyp.mk (A.subst σ) k') ->
  SubstCtx σ.lift ((Hyp.mk (A.subst σ) k')::Γ) ((Hyp.mk A k)::Δ) := by {
    intro S Hk HH n A k HΔ;
    cases n with
    | zero =>
      simp only [Annot.subst]
      cases HΔ with
      | var0 Hkk' =>
        rename_i k'
        simp only [Subst.lift_wk]
        simp only [Subst.lift]
        -- apply HasType.var
        -- case a =>
        --   apply HasType.wk1_sort
        --   rw [HypKind.annot_wk_eq Hkk']
        --   rw [HypKind.annot_wk_eq Hk]
        --   apply HH
        -- case a =>
        --   apply HasVar.var0
        --   cases Hk <;> 
        --   cases Hkk' <;>
        --   (try cases k) <;> 
        --   try exact HypKind.is_sub.refl
        --   cases k'
        --   exact HypKind.is_sub.refl
        --   sorry
        sorry

    | succ n =>
      simp only [Annot.subst, Hyp.annot]
      cases HΔ;
      rename_i A n H
      simp only [Subst.lift_wk, Nat.add]
      simp only [Subst.lift, Subst.wk1]
      -- rw [<-Annot.wk1_expr_def]
      -- exact HasType.wk1 (S H)
      sorry
  }

theorem SubstCtx.lift_loose
  {σ σ': Subst} {Γ Δ: Context} {A A': Untyped} {k: HypKind} {s: AnnotSort}:
  σ' = σ.lift ->
  A' = A.subst σ ->
  SubstCtx σ Γ Δ ->
  k.is_sub (HypKind.val s) ->
  IsHyp Γ (Hyp.mk A' (HypKind.val s)) ->
  SubstCtx σ' ((Hyp.mk A' (HypKind.val s))::Γ) ((Hyp.mk A k)::Δ) := by {
    intro Hσ HA;
    rw [Hσ, HA];
    apply lift_primitive
  }

theorem SubstCtx.upgrade (S: SubstCtx ρ Γ Δ): SubstCtx ρ Γ.upgrade Δ.upgrade 
:= by {
  intro n A k H;
  sorry
}

theorem HasType.subst {Δ a A} (HΔ: Δ ⊢ a: A):
  {σ: Subst} -> {Γ: Context} -> SubstCtx σ Γ Δ ->
  (Γ ⊢ (a.subst σ): (A.subst σ)) := by {
    induction HΔ;

    case var H I =>
      intros σ Γ S;
      cases S H with
      | expr E => exact E
      | var Hv HΓ =>
        simp only [Untyped.subst]
        rw [Hv]
        exact HasType.var (I S) HΓ

    all_goals (
      intros σ Γ S
      simp only [
        Untyped.subst, Annot.subst, term, proof, Untyped.subst0_subst
      ] at *
      constructor <;>
      rename_i' I5 I4 I3 I2 I1 I0 <;> repeat (
        try constructor
        try rw [Untyped.alpha00_comm (by simp)]
        try rw [Untyped.let_bin_ty_alpha_pair]
        try rw [Untyped.let_bin_ty_alpha_elem]
        try rw [Untyped.let_bin_ty_alpha_repr]
        try rw [Untyped.let_bin_ty_alpha_wit]
        first 
        | apply I0 | apply I1 | apply I2 | apply I3 | apply I4 | apply I5
        | exact I4 S
        first
        | exact S
        | exact SubstCtx.upgrade S
        | repeat any_goals (
          apply SubstCtx.lift_primitive _ (by constructor <;> simp only [HypKind, Hyp.subst]) <;>
          try exact S
        )
      )
    )
  }

--TODO: basic substitution helpers, in particular for subst0. See HasType.regular

inductive Annot.regular: Annot -> Context -> Prop
  | sort {Γ s}: regular (sort s) Γ
  | expr {Γ s A}: (Γ ⊢ A: sort s) -> regular (expr s A) Γ

def Annot.regular_expr: regular (expr s A) Γ -> (Γ ⊢ A: sort s)
  | Annot.regular.expr Hr => Hr

-- theorem HasType.regular (p: Γ ⊢ a: A): A.regular Γ := by {
--   induction p;

--   all_goals try exact Annot.regular.sort

--   case lam =>
--     constructor; constructor <;>
--     first | assumption | { apply Annot.regular_expr; assumption }

--   --TODO: general tactic for app requires substitution lemma for subst0

--   repeat sorry
-- }

-- theorem HasType.term_regular (p: HasType Γ a (term A)): HasType Γ A type 
--   := by {
--     let H := regular p;
--     cases H with
--     | expr H => exact H
--   }

-- theorem HasType.proof_regular (p: HasType Γ a (proof A)): HasType Γ A prop 
--   := by {
--     let H := regular p;
--     cases H with
--     | expr H => exact H
--   }