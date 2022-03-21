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
| _ => Stlc.nil

def Hyp.stlc: Hyp -> Ty
| Hyp.mk A (HypKind.val s) => A.stlc_ty
| Hyp.mk A HypKind.gst => Ty.unit

def Context.stlc: Context -> Stlc.Context
| [] => []
| H::Hs => H.stlc::(stlc Hs)

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
    sorry
  }

theorem HasType.stlc {Γ a A} (H: Γ ⊢ a: A):
  Stlc.HasType Γ.stlc a.stlc A.stlc_ty
  := by {
    induction H;
    all_goals sorry
  }