import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Wk
open Term
open Annot
open AnnotSort

inductive SubstVar: Subst -> Context -> Nat -> Term -> HypKind -> Prop
  | expr {σ Γ n A k}: (Γ ⊢ σ n: expr k.annot (A.subst σ)) -> SubstVar σ Γ n A k
  | var {σ Γ n A k m}: σ n = var m -> HasVar Γ m k (A.subst σ) -> SubstVar σ Γ n A k

def SubstCtx (σ: Subst) (Γ Δ: Context): Prop :=  
  ∀n A k, HasVar Δ n k A -> SubstVar σ Γ n A k

theorem SubstCtx.id {Γ}: SubstCtx Subst.id Γ Γ := 
  λ_ _ _ Hv => SubstVar.var rfl (Term.subst_id _ ▸ Hv)

theorem SubstCtx.lift_primitive 
  {σ: Subst} {Γ Δ: Context} {A: Term} {k k': HypKind}:
  SubstCtx σ Γ Δ ->
  k.is_sub k' ->
  IsHyp Γ (Hyp.mk (A.subst σ) k') ->
  SubstCtx σ.lift ((Hyp.mk (A.subst σ) k')::Γ) ((Hyp.mk A k)::Δ) := by {
    intro S Hk _ n A k HΔ;
    cases n with
    | zero =>
      simp only [Annot.subst]
      cases HΔ with
      | zero Hkk' =>
        apply SubstVar.var
        rfl
        simp only [Subst.lift_wk]
        simp only [Subst.lift]
        apply HasVar.zero
        apply HypKind.is_sub.trans
        assumption
        assumption
    | succ n =>
      simp only [Annot.subst, Hyp.annot]
      cases HΔ;
      rename_i A n H
      cases S _ _ _ H with
      | expr S =>
        apply SubstVar.expr
        simp only [Subst.lift_wk, Nat.add]
        simp only [Subst.lift, Subst.wk1]
        rw [<-Annot.wk1_expr_def]
        exact HasType.wk1 S
      | var Hv HΓ =>
        apply SubstVar.var
        simp [Subst.wk1, Hv]
        rfl
        simp only [Subst.lift_wk]
        exact HasVar.succ HΓ
  }

theorem SubstCtx.lift_loose
  {σ σ': Subst} {Γ Δ: Context} {A A': Term} {k: HypKind} {s: AnnotSort}:
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
  have H' := HasVar.downgrade H;
  cases S _ _ _ H' with
  | expr S =>
    rw [HypKind.annot_downgrade] at S
    exact SubstVar.expr (HasType.upgrade S)
  | var Hv HΓ =>
    exact SubstVar.var Hv (HasVar.upgrade_downgraded HΓ)
}

theorem SubstCtx.upgrade_left (S: SubstCtx ρ Γ Δ): SubstCtx ρ Γ.upgrade Δ
:= by {
  intro n A k H;
  cases S _ _ _ H with
  | expr S =>
    exact SubstVar.expr (HasType.upgrade S)
  | var Hv HΓ =>
    exact SubstVar.var Hv HΓ.upgrade_weak
}

theorem HasType.subst {Δ a A} (HΔ: Δ ⊢ a: A):
  {σ: Subst} -> {Γ: Context} -> SubstCtx σ Γ Δ ->
  (Γ ⊢ (a.subst σ): (A.subst σ)) := by {
    induction HΔ;

    case var H I =>
      intros σ Γ S;
      cases S _ _ _ H with
      | expr E => exact E
      | var Hv HΓ =>
        dsimp only [Term.subst]
        rw [Hv]
        exact HasType.var (I S) HΓ

    case natrec => sorry
    case natrec_zero => sorry
    case natrec_succ => sorry

    all_goals (
      intro σ Γ S;
      rename_i' I5 I4 I3 I2 I1 I0;
      simp only [
        Annot.sym_ty_subst,
        Annot.trans_ty_subst
      ]
      simp only [Annot.subst, term, proof, implies_subst, const_arrow_subst, assume_wf_subst] at *
      try rw [eta_ex_eq_subst]
      try rw [irir_ex_eq_subst]
      try rw [prir_ex_eq_subst]
      simp only [Term.subst, Term.subst0_subst, Subst.subst01_subst] at *
      constructor <;>
      repeat (
        try rw [Term.alpha00_comm (by simp)]
        try rw [Term.let_bin_ty_alpha_pair]
        try rw [Term.let_bin_ty_alpha_elem]
        try rw [Term.let_bin_ty_alpha_repr]
        try rw [Term.let_bin_ty_alpha_wit]
        try rw [Term.let_bin_ty_alpha_conj]
        try rw [Term.var2_var1_alpha]
        first | apply I0 | apply I1 | apply I2 | apply I3 | apply I4 | apply I5 | constructor
        first
        | exact S
        | exact SubstCtx.upgrade S
        | exact SubstCtx.upgrade_left S
        | repeat any_goals (
          apply SubstCtx.lift_primitive _ (by constructor <;> simp only [HypKind, Hyp.subst]) <;>
          first 
          | exact S 
          | exact SubstCtx.upgrade S 
          | exact SubstCtx.upgrade_left S
          | skip
        )
      )
    )
  }

theorem HasType.subst_sort {Γ Δ σ a k} 
  (HΔ: Δ ⊢ a: sort k) (S: SubstCtx σ Γ Δ):
  (Γ ⊢ (a.subst σ): sort k) := HΔ.subst S

theorem HasType.to_subst {Γ a s A} (H: HasType Γ a (expr s A)):
  SubstCtx a.to_subst Γ ((Hyp.mk A (HypKind.val s))::Γ) := by {
    intro n A k Hv;
    cases Hv with
    | zero Hs => 
      apply SubstVar.expr
      rw [<-Term.subst0_def]
      rw [Term.subst0_wk1]
      cases Hs <;> exact H
    | succ Hv => 
      apply SubstVar.var
      rfl
      rw [<-Term.subst0_def]
      rw [Term.subst0_wk1]
      exact Hv
  }

theorem HasType.subst0 {Γ e B t s A} 
  (He: HasType ((Hyp.mk A (HypKind.val s))::Γ) e B)
  (Ht: HasType Γ t (expr s A))
  : Γ ⊢ (e.subst0 t): (B.subst0 t) 
  := He.subst Ht.to_subst

theorem HasType.subst0_expr {Γ e s' t s A B} 
  (He: HasType ((Hyp.mk A (HypKind.val s))::Γ) e (expr s' B))
  (Ht: HasType Γ t (expr s A))
  : Γ ⊢ (e.subst0 t): expr s' (B.subst0 t)
  := He.subst Ht.to_subst

theorem HasType.subst0_sort {Γ e s' t s A} 
  (He: HasType ((Hyp.mk A (HypKind.val s))::Γ) e (sort s'))
  (Ht: HasType Γ t (expr s A))
  : Γ ⊢ (e.subst0 t): sort s'
  := He.subst Ht.to_subst

theorem HasType.subst0_gen {Γ e B t s A B'} 
  (He: HasType ((Hyp.mk A (HypKind.val s))::Γ) e B)
  (Ht: HasType Γ t (expr s A))
  (HBB': B' = B.subst0 t)
  : Γ ⊢ (e.subst0 t): (B') 
  := HBB' ▸ He.subst Ht.to_subst

theorem HasType.subst01 {Γ e C l r sl sr A B} 
  (He: HasType 
    ((Hyp.mk B (HypKind.val sl))
    ::(Hyp.mk A (HypKind.val sr))::Γ) e C)
  (Hl: HasType Γ l (expr sl (B.subst0 r)))
  (Hr: HasType Γ r (expr sr A))
  : Γ ⊢ (e.subst01 l r): (C.subst01 l r) 
  := by {
    unfold Term.subst01;
    unfold Annot.subst01;
    apply subst;
    exact He;
    intro n;
    cases n with
    | zero =>
      intro n A Hv;
      cases Hv with
      | zero HA =>
        cases HA <;>
        apply SubstVar.expr <;>
        rw [<-Term.subst01_wk1] at Hl <;>
        exact Hl
    | succ n => 
      cases n with
      | zero => 
        intro n A Hv;
        cases Hv with
        | succ Hv =>
          cases Hv with
          | zero HA =>
            cases HA <;>
            apply SubstVar.expr <;>
            rw [Term.subst01_def, Term.subst01_wk1_wk1] <;>
            exact Hr
      | succ n => 
        intro n A Hv;
        apply SubstVar.var;
        rfl
        cases Hv with
        | succ Hv =>
          cases Hv with
          | succ Hv => 
            rw [Term.subst01_def, Term.subst01_wk1_wk1]
            exact Hv
  }

theorem HasType.subst01_gen {Γ e C l r sl sr A B} 
  (He: HasType 
    ((Hyp.mk B (HypKind.val sl))
    ::(Hyp.mk A (HypKind.val sr))::Γ) e C)
  (Hl: HasType Γ l (expr sl (B.subst0 r)))
  (Hr: HasType Γ r (expr sr A))
  (HCC': C' = C.subst01 l r)
  : Γ ⊢ (e.subst01 l r): C' 
  := HCC' ▸ (He.subst01 Hl Hr)

theorem HasType.subst01_gen_gst {Γ e C l r sl A B} 
  (He: HasType 
    ((Hyp.mk B (HypKind.val sl))
    ::(Hyp.mk A HypKind.gst)::Γ) e C)
  (Hl: HasType Γ l (expr sl (B.subst0 r)))
  (Hr: HasType Γ r (expr type A))
  (HCC': C' = C.subst01 l r)
  : Γ ⊢ (e.subst01 l r): C' 
  := by {
    apply subst01_gen _ Hl Hr HCC';
    upgrade_ctx assumption
  }

theorem HasType.subst01_sort {Γ e s' l r sl sr A B} 
  (He: HasType 
    ((Hyp.mk B (HypKind.val sl))
    ::(Hyp.mk A (HypKind.val sr))::Γ) e (sort s'))
  (Hl: HasType Γ l (expr sl (B.subst0 r)))
  (Hr: HasType Γ r (expr sr A))
  : Γ ⊢ (e.subst01 l r): sort s' 
  := He.subst01 Hl Hr

theorem HasType.sym_ty (H: Γ ⊢ A: type): Γ ⊢ A.sym_ty: prop
  := by {
    constructor
    exact H;
    constructor
    exact H.wk1_sort;
    constructor
    constructor
    apply H.wk1_sort.wk_sort;
    repeat constructor
    exact H.upgrade.wk1_sort.wk1_sort;
    repeat constructor
    exact H.upgrade.wk1_sort.wk1_sort;
    constructor
    constructor
    simp only [Term.subst, Wk.var, Subst.lift, Subst.wk1]
    constructor
    exact H.wk1_sort.wk1_sort.wk1_sort;
    constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
  }
  
theorem HasType.trans_ty (H: Γ ⊢ A: type): Γ ⊢ A.trans_ty: prop
  := by {
    constructor
    exact H;
    constructor
    exact H.wk1_sort;
    constructor
    exact H.wk1_sort.wk1_sort;
    constructor
    constructor
    exact H.wk1_sort.wk1_sort.wk1_sort;
    constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
    exact H.wk1_sort.wk1_sort.wk1_sort.wk1_sort;
    constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
    exact H.wk1_sort.wk1_sort.wk1_sort.wk1_sort.wk1_sort;
    constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
  }

theorem SubstCtx.subst_var 
  (S: SubstCtx σ Γ Δ) 
  (HA: Δ ⊢ A: sort s) 
  (HΔ: HasVar Δ n (HypKind.val s) A)
  : Γ ⊢ σ n: expr s (A.subst σ)
  := (HasType.var HA HΔ).subst S

theorem SubstCtx.lift_delta {σ Γ Δ A k}
  (S: SubstCtx σ Γ Δ)
  (HA: Δ ⊢ A: sort k.annot):
  SubstCtx σ.lift ((Hyp.mk (A.subst σ) k)::Γ) ((Hyp.mk A k)::Δ)
  := by {
    -- Again, the strange "exact" bug...
    -- 
    -- Note: I think this is not actually a bug, but rather the `constructor` tactic
    -- failing to infer an appropriate constructor due to being confused by the
    -- additional constraints induced by the `HA.subst S` argument
    apply S.lift_primitive;
    constructor
    exact HA.subst S
  }

theorem SubstCtx.lift_type {σ Γ Δ A}
  (S: SubstCtx σ Γ Δ)
  (HA: Δ ⊢ A: sort type):
  SubstCtx σ.lift 
  ((Hyp.mk (A.subst σ) (HypKind.val type))::Γ) 
  ((Hyp.mk A (HypKind.val type))::Δ)
  := @SubstCtx.lift_delta σ Γ Δ A (HypKind.val type) S HA

theorem SubstCtx.lift_gst {σ Γ Δ A}
  (S: SubstCtx σ Γ Δ)
  (HA: Δ ⊢ A: sort type):
  SubstCtx σ.lift 
  ((Hyp.mk (A.subst σ) HypKind.gst)::Γ) 
  ((Hyp.mk A HypKind.gst)::Δ)
  := @SubstCtx.lift_delta σ Γ Δ A HypKind.gst S HA

theorem SubstCtx.lift_prop {σ Γ Δ A}
  (S: SubstCtx σ Γ Δ)
  (HA: Δ ⊢ A: sort prop):
  SubstCtx σ.lift 
  ((Hyp.mk (A.subst σ) (HypKind.val prop))::Γ) 
  ((Hyp.mk A (HypKind.val prop))::Δ)
  := @SubstCtx.lift_delta σ Γ Δ A (HypKind.val prop) S HA

theorem SubstCtx.lift_delta' {σ Γ Δ A}
  (S: SubstCtx σ Γ Δ)
  (k: HypKind)
  (HA: Δ ⊢ A: sort k.annot):
  SubstCtx σ.lift ((Hyp.mk (A.subst σ) k)::Γ) ((Hyp.mk A k)::Δ)
  := S.lift_delta HA

theorem WkCtx.to_subst {ρ Γ Δ} (R: WkCtx ρ Γ Δ): SubstCtx ρ Γ Δ
  := λ_ _ _ Hv => SubstVar.var rfl (Subst.subst_wk_compat.symm ▸ Hv.wk R)