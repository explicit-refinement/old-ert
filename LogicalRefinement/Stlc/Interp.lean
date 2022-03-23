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
| abs TermKind.assume φ A => A.stlc_ty
| abs TermKind.set A φ => A.stlc_ty
| abs TermKind.intersect A B => B.stlc_ty
| abs TermKind.union A B => B.stlc_ty
| const TermKind.nats => Ty.nats
| _ => Ty.unit

theorem HasType.prop_is_unit {Γ A}: (Γ ⊢ A: prop) -> A.stlc_ty = Ty.unit
:= by {
  intro H;
  cases H <;> rfl
}

def Annot.stlc_ty: Annot -> Ty
| expr _ A => A.stlc_ty
| sort _ => Ty.unit

theorem Annot.prop_is_unit {Γ A s}: 
  (Γ ⊢ A: prop) -> (expr s A).stlc_ty = Ty.unit
  := HasType.prop_is_unit

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
| abs TermKind.lam_pr φ x => x.stlc.lower0
| tri TermKind.app_pr P e φ => e.stlc
| bin TermKind.elem e φ => e.stlc
| let_bin TermKind.let_set P e e' =>
  Stlc.let_in P.stlc_ty e.stlc e'.stlc.lower0
| abs TermKind.lam_irrel A x => x.stlc.lower0
| tri TermKind.app_irrel P l r => l.stlc
| bin TermKind.repr l r => r.stlc
| let_bin TermKind.let_repr P e e' => 
  Stlc.let_in P.stlc_ty e.stlc e'.stlc.lower1
| const TermKind.zero => Stlc.zero
| const TermKind.succ => Stlc.succ
| unary TermKind.abort _ => Stlc.abort
| natrec K n z s => Stlc.natrec n.stlc z.stlc s.stlc.lower1
| _ => Stlc.abort

def Hyp.stlc: Hyp -> Ty
| Hyp.mk A (HypKind.val s) => A.stlc_ty
| Hyp.mk A HypKind.gst => Ty.unit

def Context.stlc: Context -> Stlc.Context
| [] => []
| H::Hs => H.stlc::(stlc Hs)

def Context.stlc_strict: Context -> Stlc.Context
| [] => []
| (Hyp.mk A (HypKind.val type))::Hs => A.stlc_ty::(stlc Hs)
| H::Hs => stlc Hs

def Context.stlc_subst: (Γ: Context) -> Stlc.Subst
| [] => (λn => Stlc.var n)
| (Hyp.mk A (HypKind.val type))::Hs => (stlc_subst Hs).lift
| H::Hs => (λn => match n with
                  | 0 => Stlc.abort
                  | Nat.succ n => stlc_subst Hs n)

-- theorem Context.stlc_subst_ctx {Γ: Context}
--   : Stlc.SubstCtx Γ.stlc_subst Γ.stlc_strict Γ.stlc
--   := by sorry

theorem HasType.stlc_ty_subst {Γ A σ s} (H: Γ ⊢ A: sort s):
  (A.subst σ).stlc_ty = A.stlc_ty := by {
  revert H s σ Γ;
  induction A <;> intro Γ σ s H <;> cases H <;> try rfl
  all_goals (
    simp only [Term.stlc_ty, Term.subst]
    rename_i' I0 I1 I2 I3
    try rw [I0]
    try rw [I1]
    try rw [I2]
    try rw [I3]
    all_goals assumption
  )
}

theorem Term.stlc_ty_wk {A: Term}: ∀{ρ}, (A.wk ρ).stlc_ty = A.stlc_ty 
:= by {
  induction A <;> intro ρ <;> 
  simp only [Term.stlc_ty, Term.wk]

  case bin k l r Il Ir =>
    cases k <;>
    simp only [Term.stlc_ty, Term.wk, *]
  case abs k l r Il Ir =>
    cases k <;>
    simp only [Term.stlc_ty, Term.wk, *]
}

theorem Annot.stlc_ty_subst {Γ A σ s k} (H: Γ ⊢ A: sort s):
  (expr k (A.subst σ)).stlc_ty = (expr k A).stlc_ty := H.stlc_ty_subst

theorem Annot.stlc_ty_wk {A k}: ∀{ρ},
  (expr k (A.wk ρ)).stlc_ty = (expr k A).stlc_ty := Term.stlc_ty_wk

theorem HasVar.stlc_val {Γ A s n}: 
  HasVar Γ n (HypKind.val s) A ->
  Stlc.HasVar Γ.stlc n (Annot.expr s A).stlc_ty := by {    
    revert A s n;
    induction Γ with
    | nil => intro A s n H; cases H
    | cons H Γ I =>
      intro A s n HΓ;
      cases HΓ with
      | zero S =>
        cases S;
        simp only [Annot.stlc_ty, Context.stlc, Term.wk1]
        rw [Term.stlc_ty_wk]
        constructor
      | succ =>
        apply Stlc.HasVar.succ
        simp only [Term.wk1]
        rw [Annot.stlc_ty_wk]
        apply I
        assumption

  }

-- But why...
set_option maxHeartbeats 1000000

theorem HasType.stlc {Γ a A} (H: Γ ⊢ a: A):
  Stlc.HasType Γ.stlc a.stlc A.stlc_ty
  := by {
    induction H <;> try exact Stlc.HasType.abort

    case var Hv IA => exact Stlc.HasType.var Hv.stlc_val

    --TODO: automate remaining cases with rename_i' or something like
    case app HAB _ _ _ _ _ =>
      simp only [Term.stlc, Term.stlc_ty, subst0, term] at *
      repeat rw [Annot.stlc_ty_subst] at *
      constructor
      assumption
      assumption
      cases HAB; assumption

    case pair  HAB _ _ _ _ _ =>
      simp only [Term.stlc, Term.stlc_ty, subst0, term] at *
      repeat rw [Annot.stlc_ty_subst] at *
      constructor
      assumption
      assumption
      cases HAB; assumption

    case elem HAφ _ _ _ _ _ =>
      simp only [Term.stlc, Term.stlc_ty, subst0, term] at *
      repeat rw [Annot.stlc_ty_subst] at *
      assumption

    case app_pr HφA _ _ _ _ _ =>
      simp only [Term.stlc, Term.stlc_ty, subst0, term]
      repeat rw [Annot.stlc_ty_subst] at *
      assumption
      cases HφA; assumption

    case app_irrel HAB _ _ _ _ _ =>
      simp only [Term.stlc, Term.stlc_ty, subst0, term]
      repeat rw [Annot.stlc_ty_subst] at *
      assumption
      cases HAB; assumption

    case repr HAB _ _ _ _ _ =>
      simp only [Term.stlc, Term.stlc_ty, subst0, term] at *
      repeat rw [Annot.stlc_ty_subst] at *
      assumption
      cases HAB; assumption

    case lam_pr =>
      apply Stlc.HasType.lower0;
      assumption
    case lam_irrel =>
      apply Stlc.HasType.lower0;
      assumption

    all_goals (
      constructor <;>
      simp only [
        subst0, alpha0, term, proof, wknth, wk1
      ] at * <;>
      (repeat rw [Annot.stlc_ty_subst] at *) <;>
      (repeat rw [Annot.stlc_ty_wk] at *) <;>
      first 
      | assumption
      | (
        apply Stlc.HasType.lower0;
        assumption
      )
      | (
        apply Stlc.HasType.lower1;
        assumption
      ) 
      | (
        apply HasType.wk_sort
        assumption
        repeat constructor
      )
    )
  }