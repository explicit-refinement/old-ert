import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Untyped
import LogicalRefinement.Typed
open Term
open TermKind
open Annot
open AnnotSort

-- tfw your termination checker doesn't terminate
set_option maxHeartbeats 1000000

def Term.stlc_nil_ty: Term -> Ty
| const TermKind.unit => Ty.unit
| abs TermKind.pi A B => Ty.arrow A.stlc_nil_ty B.stlc_nil_ty
| abs TermKind.sigma A B => Ty.prod A.stlc_nil_ty B.stlc_nil_ty
| bin TermKind.coprod A B => Ty.coprod A.stlc_nil_ty B.stlc_nil_ty
| abs TermKind.assume φ A => Ty.arrow φ.stlc_nil_ty A.stlc_nil_ty
| abs TermKind.set A φ => Ty.prod A.stlc_nil_ty φ.stlc_nil_ty
| abs TermKind.intersect A B => Ty.arrow Ty.unit B.stlc_nil_ty
| abs TermKind.union A B => Ty.prod Ty.unit B.stlc_nil_ty
| const TermKind.nats => Ty.nats
| _ => Ty.unit

theorem HasType.prop_is_unit {Γ A}: (Γ ⊢ A: prop) -> A.stlc_nil_ty = Ty.unit
:= by {
  intro H;
  cases H <;> rfl
}

def Annot.stlc_nil_ty: Annot -> Ty
| expr _ A => A.stlc_nil_ty
| sort _ => Ty.unit

theorem Annot.prop_is_unit {Γ A s}: 
  (Γ ⊢ A: prop) -> (expr s A).stlc_nil_ty = Ty.unit
  := HasType.prop_is_unit

def Term.stlc_nil: Term -> Stlc
| var n => Stlc.var n
| const TermKind.nil => Stlc.nil
| abs TermKind.lam A x => Stlc.lam A.stlc_nil_ty x.stlc_nil
| tri TermKind.app P l r => Stlc.app P.stlc_nil_ty l.stlc_nil r.stlc_nil
| bin TermKind.pair l r => Stlc.pair l.stlc_nil r.stlc_nil
| let_bin TermKind.let_pair P e e' => 
  Stlc.let_pair P.stlc_nil_ty e.stlc_nil e'.stlc_nil
| unary (TermKind.inj i) e => Stlc.inj i e.stlc_nil
| cases TermKind.case P d l r => 
  Stlc.case P.stlc_nil_ty d.stlc_nil l.stlc_nil r.stlc_nil
| abs TermKind.lam_pr φ x => Stlc.lam φ.stlc_nil_ty x.stlc_nil
| tri TermKind.app_pr P e φ => Stlc.app P.stlc_nil_ty e.stlc_nil Stlc.nil
| bin TermKind.elem e φ => Stlc.pair e.stlc_nil Stlc.nil
| let_bin TermKind.let_set P e e' =>
  Stlc.let_pair P.stlc_nil_ty e.stlc_nil e'.stlc_nil
| abs TermKind.lam_irrel A x => Stlc.lam Ty.unit x.stlc_nil
| tri TermKind.app_irrel P l r => Stlc.app P.stlc_nil_ty l.stlc_nil Stlc.nil
| bin TermKind.repr l r => Stlc.pair Stlc.nil r.stlc_nil
| let_bin TermKind.let_repr P e e' => 
  Stlc.let_pair P.stlc_nil_ty e.stlc_nil e'.stlc_nil
| const TermKind.zero => Stlc.zero
| const TermKind.succ => Stlc.succ
| unary TermKind.abort _ => Stlc.abort
| natrec K n z s => Stlc.natrec n.stlc_nil z.stlc_nil s.stlc_nil
| _ => Stlc.nil

def Hyp.stlc_nil: Hyp -> Ty
| Hyp.mk A (HypKind.val s) => A.stlc_nil_ty
| Hyp.mk A HypKind.gst => Ty.unit

def Context.stlc_nil: Context -> Stlc.Context
| [] => []
| H::Hs => H.stlc_nil::(stlc_nil Hs)

theorem HasType.stlc_nil_ty_subst {Γ A σ s} (H: Γ ⊢ A: sort s):
  (A.subst σ).stlc_nil_ty = A.stlc_nil_ty := by {
  revert H s σ Γ;
  induction A <;> intro Γ σ s H <;> cases H <;> try rfl
  all_goals (
    simp only [Term.stlc_nil_ty, Term.subst]
    rename_i' I0 I1 I2 I3
    try rw [I0]
    try rw [I1]
    try rw [I2]
    try rw [I3]
    all_goals assumption
  )
}

theorem Term.stlc_nil_ty_wk {A: Term}: ∀{ρ}, (A.wk ρ).stlc_nil_ty = A.stlc_nil_ty 
:= by {
  induction A <;> intro ρ <;> 
  simp only [Term.stlc_nil_ty, Term.wk]

  case bin k l r Il Ir =>
    cases k <;>
    simp only [Term.stlc_nil_ty, Term.wk, *]
  case abs k l r Il Ir =>
    cases k <;>
    simp only [Term.stlc_nil_ty, Term.wk, *]
}

theorem Annot.stlc_nil_ty_subst {Γ A σ s k} (H: Γ ⊢ A: sort s):
  (expr k (A.subst σ)).stlc_nil_ty = (expr k A).stlc_nil_ty := H.stlc_nil_ty_subst

theorem Annot.stlc_nil_ty_wk {A k}: ∀{ρ},
  (expr k (A.wk ρ)).stlc_nil_ty = (expr k A).stlc_nil_ty := Term.stlc_nil_ty_wk

theorem HasVar.stlc_nil_val {Γ A s n}: 
  HasVar Γ n (HypKind.val s) A ->
  Stlc.HasVar Γ.stlc_nil n (Annot.expr s A).stlc_nil_ty := by {
    revert A s n;
    induction Γ with
    | nil => intro A s n H; cases H
    | cons H Γ I =>
      intro A s n HΓ;
      cases HΓ with
      | var0 S =>
        cases S;
        simp only [Annot.stlc_nil_ty, Context.stlc_nil, Term.wk1]
        rw [Term.stlc_nil_ty_wk]
        constructor
      | var_succ =>
        apply Stlc.HasVar.succ
        simp only [Term.wk1]
        rw [Annot.stlc_nil_ty_wk]
        apply I
        assumption
  }

theorem HasType.stlc_nil {Γ a A} (H: Γ ⊢ a: A):
  Stlc.HasType Γ.stlc_nil a.stlc_nil A.stlc_nil_ty
  := by {
    induction H;

    case var Hv IA => exact Stlc.HasType.var Hv.stlc_nil_val

    case app HAB _ _ _ _ _ =>
      simp only [Term.stlc_nil, Term.stlc_nil_ty, subst0, term]
      repeat rw [Annot.stlc_nil_ty_subst] at *
      constructor
      assumption
      assumption
      cases HAB; assumption

    case pair  HAB _ _ _ _ _ =>
      simp only [Term.stlc_nil, Term.stlc_nil_ty, subst0, term] at *
      repeat rw [Annot.stlc_nil_ty_subst] at *
      constructor
      assumption
      assumption
      cases HAB; assumption

    case elem HAφ _ _ _ _ _ =>
      simp only [Term.stlc_nil, Term.stlc_nil_ty, subst0, term] at *
      repeat rw [Annot.stlc_nil_ty_subst] at *
      constructor
      assumption
      simp only [Term.stlc_nil, Term.stlc_nil_ty, subst0, term] at *
      rw [HasType.prop_is_unit]
      constructor
      cases HAφ; assumption

    case app_pr HφA _ _ _ _ _ =>
      simp only [Term.stlc_nil, Term.stlc_nil_ty, subst0, term]
      repeat rw [Annot.stlc_nil_ty_subst] at *
      constructor
      assumption
      simp only [Term.stlc_nil, Term.stlc_nil_ty, subst0, term] at *
      rw [HasType.prop_is_unit]
      constructor
      cases HφA; assumption
      cases HφA; assumption

    case app_irrel HAB _ _ _ _ _ =>
      simp only [Term.stlc_nil, Term.stlc_nil_ty, subst0, term]
      repeat rw [Annot.stlc_nil_ty_subst] at *
      constructor
      assumption
      constructor
      cases HAB; assumption

    case repr HAB _ _ _ _ _ =>
      simp only [Term.stlc_nil, Term.stlc_nil_ty, subst0, term] at *
      repeat rw [Annot.stlc_nil_ty_subst] at *
      constructor
      constructor
      assumption
      cases HAB; assumption

    all_goals try (
      constructor <;>
      simp only [
        subst0, alpha0, term, proof, wknth, wk1
      ] at * <;>
      (repeat rw [Annot.stlc_nil_ty_subst] at *) <;>
      (repeat rw [Annot.stlc_nil_ty_wk] at *) <;>
      first 
      | assumption 
      | (
        apply HasType.wk_sort (by assumption); 
        repeat first | assumption | constructor
      )
    )

    all_goals (
      simp only [proof, subst0]
      rw [Annot.stlc_nil_ty_subst]
      rw [Annot.prop_is_unit]
      constructor
      repeat assumption
    )

    repeat case mp Hφψ _ _ _ _ _ => 
      cases Hφψ; assumption
    repeat case inst HφA _ _ _ _ _ =>
      cases HφA; assumption
  }