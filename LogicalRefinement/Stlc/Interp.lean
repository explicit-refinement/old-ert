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

def Hyp.stlc: Hyp -> Ty
| (Hyp.mk A (HypKind.val _)) => A.stlc_ty
| (Hyp.mk _ HypKind.gst) => Ty.unit

def Context.stlc: Context -> Stlc.Context
| [] => []
| (Hyp.mk A (HypKind.val _))::Hs => A.stlc_ty::(stlc Hs)
| (Hyp.mk _ HypKind.gst)::Hs => Ty.unit::(stlc Hs)

theorem Context.stlc_hyp {Γ: Context} {H}:
  Context.stlc (H::Γ) = H.stlc::Γ.stlc
  := by {
    cases H with
    | mk A k => cases k <;> rfl
  }

def Term.stlc: Term -> Stlc
| var n => Stlc.var n
| const TermKind.nil => Stlc.nil
| abs TermKind.lam A x => Stlc.lam A.stlc_ty x.stlc
| tri TermKind.app P l r => Stlc.app P.stlc_ty l.stlc r.stlc
| bin TermKind.pair l r => Stlc.pair l.stlc r.stlc
| let_bin (TermKind.let_pair type) P e e' => 
  Stlc.let_pair P.stlc_ty e.stlc e'.stlc
| unary (TermKind.inj i) e => Stlc.inj i e.stlc
| cases (TermKind.case type) P d l r => 
  Stlc.case P.stlc_ty d.stlc l.stlc r.stlc
| abs TermKind.lam_pr _ x => Stlc.lam Ty.unit x.stlc
| tri TermKind.app_pr A e _ => Stlc.app A.stlc_ty e.stlc Stlc.nil
| bin TermKind.elem e _ => e.stlc
| let_bin (TermKind.let_set type) P e e' =>
  Stlc.let_pair (Ty.prod P.stlc_ty Ty.unit) 
    (Stlc.pair e.stlc Stlc.nil) e'.stlc
| abs TermKind.lam_irrel _ x => Stlc.lam Ty.unit x.stlc
| tri TermKind.app_irrel A l _ => Stlc.app A.stlc_ty l.stlc Stlc.nil
| bin TermKind.repr _ r => r.stlc
| let_bin (TermKind.let_repr type) P e e' => 
  Stlc.let_pair (Ty.prod Ty.unit P.stlc_ty) 
    (Stlc.pair Stlc.nil e.stlc) e'.stlc
| const TermKind.zero => Stlc.zero
| const TermKind.succ => Stlc.succ
| nr (TermKind.natrec type) K n z s 
  => Stlc.natrec K.stlc_ty n.stlc z.stlc s.stlc
| unary TermKind.abort _ => Stlc.abort
| _ => Stlc.abort

theorem Term.stlc_var: (Term.var v).stlc = Stlc.var v := rfl

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
      | zero =>
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

theorem HasVar.stlc_hyp {Γ A n}: 
  HasVar Γ n k A ->
  Stlc.HasVar Γ.stlc n (Hyp.mk A k).stlc := by {
    revert Γ A;
    induction n generalizing k with
    | zero => 
      intro Γ A Hv;
      cases Hv with
      | zero =>
        cases k <;>
        simp only [Term.wk1, Term.stlc_ty_wk, Hyp.stlc] <;>
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
            cases k <;>
            constructor <;>
            cases k <;>
            simp only [Term.wk1, Term.stlc_ty_wk, Hyp.stlc] <;>
            exact I Hv
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
    | _ =>
      try rename AnnotSort => k;
      (try cases k) <;>
      first
      | exact Stlc.HasType.abort
      | assumption
      | (
        dsimp only [Term.stlc, Term.stlc_ty] at *
        simp only [
          Term.alpha0, Term.subst0, Annot.subst0,
          Annot.stlc_ty_subst, Annot.stlc_ty_wk,
          Term.stlc_ty_wk, wknth, Context.stlc,
          term, proof
        ] at *
        repeat rw [Annot.stlc_ty_subst] at *
        repeat rw [Annot.stlc_ty_wk] at *
        repeat rw [HasType.prop_is_unit (by assumption)] at *
        first 
          | assumption 
          | (constructor <;> first | assumption | constructor)
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
      --TODO: sort this mess out
      try constructor
      try apply HasType.wk_sort 
        <;> first | assumption | repeat constructor
      try assumption
      try apply HasType.wk_sort 
        <;> first | assumption | repeat constructor
      try assumption
  }

-- theorem HasType.stlc_prop_is_none {Γ a A G} (H: Γ ⊢ a: expr prop A)
--   : H.stlc.interp G = none
--   := by {
--     generalize Stlc.HasType.interp _ _ = x;
--     cases x with
--     | some x => cases x
--     | none => rfl
--   }


def Stlc.Context.interp.downgrade 
  {Γ: _root_.Context} (G: Γ.upgrade.stlc.interp)
  : Γ.stlc.interp
  :=
  match Γ, G with
  | [], () => ()
  | (Hyp.mk _ (HypKind.val _))::_, (x, G) => (x, G.downgrade)
  | (Hyp.mk _ HypKind.gst)::_, (_, G) => (none, G.downgrade)