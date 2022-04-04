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
| expr type A => A.stlc_ty
| _ => Ty.unit

theorem Annot.prop_is_unit {Γ A s}: 
  (Γ ⊢ A: prop) -> (expr s A).stlc_ty = Ty.unit
  := by {
    intro H;
    cases s with
    | type => exact H.prop_is_unit
    | prop => rfl
  }

def Context.stlc: Context -> Stlc.Context
| [] => []
| (Hyp.mk A (HypKind.val type))::Hs => A.stlc_ty::(stlc Hs)
| H::Hs => stlc Hs

def Sparsity := List Bool

def Hyp.sparsity: Hyp -> Bool
| Hyp.mk A k => k == HypKind.val type

def Context.sparsity: Context -> Sparsity
| [] => []
| H::Hs => H.sparsity::(sparsity Hs)

def Sparsity.ix: Sparsity -> Nat -> Nat
| _, 0 => 0
| [], n => n
| true::Hs, Nat.succ n => (ix Hs n) + 1
| false::Hs, Nat.succ n => ix Hs n

def Context.stlc_ix (Γ: Context): Nat -> Nat := Γ.sparsity.ix

def Term.stlc: Term -> Sparsity -> Stlc
| var n, σ => 
  if σ.get? n = some true 
  then Stlc.var (σ.ix n) 
  else Stlc.abort
| const TermKind.nil, _ => Stlc.nil
| abs TermKind.lam A x, σ => Stlc.lam A.stlc_ty (x.stlc (true::σ))
| tri TermKind.app P l r, σ => Stlc.app P.stlc_ty (l.stlc σ) (r.stlc σ)
| bin TermKind.pair l r, σ => Stlc.pair (l.stlc σ) (r.stlc σ)
| let_bin TermKind.let_pair P e e', σ => 
  Stlc.let_pair P.stlc_ty (e.stlc σ) (e'.stlc (true::true::σ))
| unary (TermKind.inj i) e, σ => Stlc.inj i (e.stlc σ)
| cases TermKind.case P d l r, σ => 
  Stlc.case P.stlc_ty (d.stlc σ) (l.stlc (true::σ)) (r.stlc (true::σ))
| abs TermKind.lam_pr φ x, σ => x.stlc (false::σ)
| tri TermKind.app_pr P e φ, σ => e.stlc σ
| bin TermKind.elem e φ, σ => e.stlc σ
| let_bin TermKind.let_set P e e', σ =>
  Stlc.let_in P.stlc_ty (e.stlc σ) (e'.stlc (false::σ))
| abs TermKind.lam_irrel A x, σ => x.stlc (false::σ)
| tri TermKind.app_irrel P l r, σ => l.stlc σ
| bin TermKind.repr l r, σ => r.stlc σ
| let_bin TermKind.let_repr P e e', σ => 
  Stlc.let_in P.stlc_ty (e.stlc σ) (e'.stlc (false::σ))
| const TermKind.zero, σ => Stlc.zero
| const TermKind.succ, σ => Stlc.succ
| natrec K n z s, σ => Stlc.natrec K.stlc_ty (n.stlc σ) (z.stlc σ) (s.stlc (true::false::σ))
| unary TermKind.abort _, σ => Stlc.abort
| _, σ => Stlc.abort

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
  (expr k (A.subst σ)).stlc_ty = (expr k A).stlc_ty := by {
    cases k with
    | type => exact H.stlc_ty_subst
    | prop => rfl
  }

theorem Annot.stlc_ty_wk {A k}: ∀{ρ},
  (expr k (A.wk ρ)).stlc_ty = (expr k A).stlc_ty := by {
    cases k with
    | type => exact Term.stlc_ty_wk
    | prop => rfl
  }

theorem HasVar.stlc {Γ A n}: 
  HasVar Γ n (HypKind.val type) A ->
  Stlc.HasVar Γ.stlc (Γ.stlc_ix n) A.stlc_ty := by {
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
          | mk B k =>
            cases k with
            | val s =>
              cases s with
              | type => exact (I Hv).succ
              | prop => exact (I Hv)
            | gst => exact (I Hv)
  }

theorem HasVar.sigma {Γ A n s}:
  HasVar Γ n (HypKind.val s) A ->
  Γ.sparsity.get? n = some (s == type)
  := by {
    revert Γ A s;
    induction n with
    | zero =>
      intro Γ A s Hv;
      cases Hv with
      | zero Hk =>
        cases Hk with
        | refl =>
          rename AnnotSort => s;
          cases s <;> rfl
    | succ n I =>
      intro Γ A s Hv;
      cases Γ <;> cases Hv
      rw [<-I (by assumption)]
      rfl
  }

-- But why...
set_option maxHeartbeats 1000000

theorem HasType.stlc {Γ a A}:
  (Γ ⊢ a : A) -> Stlc.HasType Γ.stlc (a.stlc Γ.sparsity) A.stlc_ty := by {
    intro H;
    induction H with
    | var _ Hv => 
      rename AnnotSort => s;
      simp only [Term.stlc]
      rw [Hv.sigma]
      cases s with
      | type => exact Stlc.HasType.var Hv.stlc
      | prop => exact Stlc.HasType.abort
    | app => sorry
    | lam => sorry
    | pair => sorry
    | let_pair => sorry
    | inj_l => sorry
    | inj_r => sorry
    | case => sorry
    | elem => sorry
    | let_set => sorry
    | lam_pr => sorry
    | app_pr => sorry
    | lam_irrel => sorry
    | app_irrel => sorry
    | repr => sorry
    | let_repr => sorry
    | natrec => sorry
    | _ => 
      simp only [
        Term.alpha0, Term.subst0, Annot.subst0,
        Annot.stlc_ty_subst, Annot.stlc_ty_wk,
        HasType.stlc_ty_subst, Term.stlc_ty_wk,
        term, proof
      ] at *
      constructor
  }