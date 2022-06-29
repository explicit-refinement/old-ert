import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Untyped
import LogicalRefinement.Typed
open Term
open TermKind
open Annot
open AnnotSort

def Term.stlc_ty: Term -> Ty
| const TermKind.unit => Ty.unit
| abs TermKind.pi A B => Ty.arrow A.stlc_ty B.stlc_ty
| abs TermKind.sigma A B => Ty.prod A.stlc_ty B.stlc_ty
| bin TermKind.coprod A B => Ty.coprod A.stlc_ty B.stlc_ty
| abs TermKind.assume _ A => Ty.arrow Ty.unit A.stlc_ty
| abs TermKind.set A _ => A.stlc_ty
| abs TermKind.intersect _ B => Ty.arrow Ty.unit B.stlc_ty
| abs TermKind.union _ B => B.stlc_ty
| const TermKind.nats => Ty.nats
| _ => Ty.unit

theorem HasType.prop_is_unit {Γ A}: (Γ ⊢ A: prop) -> A.stlc_ty = Ty.unit
:= by {
  intro H;
  cases H <;> rfl
}

def Annot.stlc_ty: Annot -> Ty
| expr _ A => A.stlc_ty
| _ => Ty.unit

theorem Annot.prop_is_unit {Γ A s}: 
  (Γ ⊢ A: prop) -> (expr s A).stlc_ty = Ty.unit
  := by {
    intro H;
    exact H.prop_is_unit
  }

theorem Annot.sort_case {Γ A s} (H: Γ ⊢ A: sort s): 
  (expr s A).stlc_ty = A.stlc_ty
  := by {
    cases s with
    | type => simp only [stlc_ty]
    | prop => rw [Annot.prop_is_unit H, HasType.prop_is_unit H]
  }

def Context.stlc: Context -> Stlc.Context
| [] => []
| (Hyp.mk A (HypKind.val _))::Hs => A.stlc_ty::(stlc Hs)
| (Hyp.mk _ HypKind.gst)::Hs => Ty.unit::(stlc Hs)

def Term.stlc: Term -> Stlc
| var n => Stlc.var n
| const TermKind.nil => Stlc.nil
| abs TermKind.lam A x => Stlc.lam A.stlc_ty x.stlc
| tri TermKind.app P l r => Stlc.app P.stlc_ty l.stlc r.stlc
| bin TermKind.pair l r => Stlc.pair l.stlc r.stlc
| let_bin TermKind.let_pair P e e' => 
  Stlc.let_pair P.stlc_ty e.stlc e'.stlc
| unary (TermKind.inj i) e => Stlc.inj i e.stlc
| cases TermKind.case P d l r => 
  Stlc.case P.stlc_ty d.stlc l.stlc r.stlc
| abs TermKind.lam_pr _ x => x.stlc
| tri TermKind.app_pr _ e _ => e.stlc
| bin TermKind.elem e _ => e.stlc
| let_bin TermKind.let_set P e e' =>
  Stlc.let_in P.stlc_ty e.stlc (Stlc.let_in Ty.unit Stlc.nil e'.stlc)
| abs TermKind.lam_irrel _ x => x.stlc
| tri TermKind.app_irrel _ l _ => l.stlc
| bin TermKind.repr _ r => r.stlc
| let_bin TermKind.let_repr P e e' => 
  Stlc.let_in Ty.unit Stlc.nil (Stlc.let_in P.stlc_ty e.stlc e'.stlc)
| const TermKind.zero => Stlc.zero
| const TermKind.succ => Stlc.succ
| nr (TermKind.natrec type) K n z s 
  => Stlc.natrec K.stlc_ty n.stlc z.stlc 
    (Stlc.let_in Ty.unit Stlc.nil 
      (Stlc.let_in K.stlc_ty (Stlc.var 1) s.stlc))
| unary TermKind.abort _ => Stlc.abort
| _ => Stlc.abort

theorem Term.stlc_var: (Term.var v).stlc = Stlc.var v := rfl

-- theorem Context.stlc_subst_ctx {Γ: Context}
--   : Stlc.SubstCtx Γ.stlc_subst Γ.stlc_strict Γ.stlc
--   := by sorry

set_option maxHeartbeats 10000000

theorem HasType.stlc_ty_subst {Γ A σ s} (H: Γ ⊢ A: sort s):
  (A.subst σ).stlc_ty = A.stlc_ty := by {
  revert H s σ Γ;
  induction A <;> intro Γ σ s H <;> cases H <;> try rfl
  all_goals (
    dsimp only [Term.stlc_ty, Term.subst]
    rename_i' I0 I1 I2 I3
    try rw [I0]
    try rw [I1]
    try rw [I2]
    try rw [I3]
    all_goals assumption
  )
}

theorem HasType.stlc_ty_subst0 {Γ A b} (H: Γ ⊢ A: sort s):
  (A.subst0 b).stlc_ty = A.stlc_ty := H.stlc_ty_subst

theorem Term.stlc_ty_wk (A: Term) (ρ: Wk): (A.wk ρ).stlc_ty = A.stlc_ty 
:= by {
  induction A generalizing ρ <;> 
  simp only [Term.stlc_ty, Term.wk]

  case bin k l r Il Ir =>
    cases k <;>
    dsimp only [Term.stlc_ty, Term.wk] <;>
    simp only [*]
  case abs k l r Il Ir =>
    cases k <;>
    dsimp only [Term.stlc_ty, Term.wk] <;>
    simp only [*]
}

theorem Term.stlc_ty_wknth {A: Term}: (A.wknth n).stlc_ty = A.stlc_ty 
:= by {
  simp only [wknth]
  apply Term.stlc_ty_wk
}

theorem Term.stlc_ty_wk1 (A: Term): (A.wk1).stlc_ty = A.stlc_ty 
:= by {
  simp only [wk1]
  apply Term.stlc_ty_wk
}

theorem Annot.stlc_ty_subst {Γ A σ s k} (H: Γ ⊢ A: sort s):
  (expr k (A.subst σ)).stlc_ty = (expr k A).stlc_ty := H.stlc_ty_subst

theorem Annot.stlc_ty_wk {A k}: ∀{ρ},
  (expr k (A.wk ρ)).stlc_ty = (expr k A).stlc_ty := by {
    apply A.stlc_ty_wk
  }

theorem Annot.stlc_ty_subst' {Γ A σ s k} (H: Γ ⊢ A: sort s):
  ((expr k A).subst σ).stlc_ty = (expr k A).stlc_ty := H.stlc_ty_subst

theorem Annot.stlc_ty_wk' {A k}: ∀{ρ},
  ((expr k A).wk ρ).stlc_ty = (expr k A).stlc_ty := by {
    apply A.stlc_ty_wk
  }


theorem HasVar.stlc {Γ A n}: 
  HasVar Γ n (HypKind.val s) A ->
  Stlc.HasVar Γ.stlc n A.stlc_ty := by {
    revert Γ A;
    induction n with
    | zero => 
      intro Γ A Hv;
      cases Hv with
      | zero Hk =>
        cases Hk;
        simp only [Term.wk1, Term.stlc_ty_wk]
        exact Stlc.HasVar.zero
    | succ n I => 
      intro Γ A Hv;
      cases Γ with
      | nil => cases Hv
      | cons H Γ =>
        cases Hv with
        | succ Hv =>
          simp only [Term.wk1, Term.stlc_ty_wk]
          cases H with
          | mk B k => cases k <;> exact (I Hv).succ
  }

-- But why...
set_option maxHeartbeats 1000000

theorem HasType.stlc {Γ a A}:
  (Γ ⊢ a : A) -> Stlc.HasType Γ.stlc a.stlc A.stlc_ty := by {
    intro H;
    induction H with
    | var _ Hv => 
      constructor
      exact Hv.stlc
    | natrec HC _ _ Hs IC Ie Iz Is => 
      rename AnnotSort => k;
      cases k with
      | type =>
        dsimp only [
          Term.stlc, Term.stlc_ty, Term.subst0
        ] at *;
        rw [Annot.stlc_ty_subst] at *
        apply Stlc.HasType.natrec;
        assumption
        assumption
        constructor
        constructor
        constructor
        constructor
        constructor
        constructor
        --TODO: fix this...
        sorry
        assumption
        assumption
      | prop => exact Stlc.HasType.abort
    | lam_pr => sorry
    | app_pr => sorry
    | let_set => sorry
    | lam_irrel => sorry
    | app_irrel => sorry
    | let_repr => sorry
    | _ =>
      stop
      first
      | exact Stlc.HasType.abort
      | assumption
      | (
        dsimp only [Term.stlc, Term.stlc_ty] at *
        simp only [
          Term.alpha0, Term.subst0, Annot.subst0,
          Annot.stlc_ty_subst, Annot.stlc_ty_wk,
          Term.stlc_ty_wk, wknth,
          term, proof
        ] at *
        repeat rw [Annot.stlc_ty_subst] at *
        repeat rw [Annot.stlc_ty_wk] at *
        first | assumption | (constructor <;> assumption)
        repeat first
        | assumption
        | (
          apply HasType.wk_sort
          assumption
          repeat constructor
          assumption
        )
        | (
        rename (HasType _ (Term.abs _ _ _) _) => Habs
        cases Habs <;> assumption
        )
      )
  }

-- theorem HasType.stlc_prop_is_none {Γ a A G} (H: Γ ⊢ a: expr prop A)
--   : H.stlc.interp G = none
--   := by {
--     generalize Stlc.HasType.interp _ _ = x;
--     cases x with
--     | some x => cases x
--     | none => rfl
--   }