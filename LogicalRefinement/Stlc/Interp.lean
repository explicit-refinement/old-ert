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
| abs TermKind.assume _ A => A.stlc_ty
| abs TermKind.set A _ => A.stlc_ty
| abs TermKind.intersect _ B => B.stlc_ty
| abs TermKind.union _ B => B.stlc_ty
| const TermKind.nats => Ty.nats
| _ => Ty.bot

theorem HasType.prop_is_bot {Γ A}: (Γ ⊢ A: prop) -> A.stlc_ty = Ty.bot
:= by {
  intro H;
  cases H <;> rfl
}

def Annot.stlc_ty: Annot -> Ty
| expr type A => A.stlc_ty
| _ => Ty.bot

theorem Annot.prop_is_bot {Γ A s}: 
  (Γ ⊢ A: prop) -> (expr s A).stlc_ty = Ty.bot
  := by {
    intro H;
    cases s with
    | type => exact H.prop_is_bot
    | prop => rfl
  }

theorem Annot.sort_case {Γ A s} (H: Γ ⊢ A: sort s): 
  (expr s A).stlc_ty = A.stlc_ty
  := by {
    cases s with
    | type => simp only [stlc_ty]
    | prop => rw [Annot.prop_is_bot H, HasType.prop_is_bot H]
  }

def Context.stlc: Context -> Stlc.Context
| [] => []
| (Hyp.mk A (HypKind.val type))::Hs => A.stlc_ty::(stlc Hs)
| _::Hs => stlc Hs

@[simp]
theorem Context.stlc_gst
  : stlc ((Hyp.gst A)::Γ) = stlc Γ
  := rfl

def Context.ghosts: Context -> Stlc.Context
| [] => []
| (Hyp.mk A HypKind.gst)::Hs => A.stlc_ty::(ghosts Hs)
| (Hyp.mk _ _)::Hs => (ghosts Hs)

def Hyp.sparsity (H: Hyp): Bool := H.kind = HypKind.val type

def Context.sparsity: Context -> Sparsity
| [] => []
| H::Hs => H.sparsity::(sparsity Hs)

@[simp]
theorem Context.sparsity_gst
  : sparsity ((Hyp.gst A)::Γ) = false::(sparsity Γ)
  := rfl

@[simp]
theorem Context.sparsity_ty
  : sparsity ((Hyp.val A type)::Γ) = true::(sparsity Γ)
  := rfl
@[simp]
theorem Context.sparsity_prop
  : sparsity ((Hyp.val A prop)::Γ) = false::(sparsity Γ)
  := rfl

def Context.downgrade_sparsity: Context -> Sparsity
| [] => []
| (Hyp.mk _ (HypKind.val type))::Γ => true::(downgrade_sparsity Γ)
| (Hyp.mk _ (HypKind.val prop))::Γ => downgrade_sparsity Γ
| (Hyp.mk _ HypKind.gst)::Γ => false::(downgrade_sparsity Γ)

@[simp]
theorem Context.downgrade_sparsity_downgrade (Γ: Context)
  : Γ.downgrade_sparsity.thin Γ.upgrade.stlc = Γ.stlc
  := by {
    induction Γ with
    | nil => simp [downgrade_sparsity]
    | cons H Γ I => 
      cases H with
      | mk A k =>
        cases k with
        | val s => cases s with 
          | type => 
            simp [Sparsity.thin] at *
            rw [I]
            rfl
          | prop => exact I
        | gst => exact I
  }

def Stlc.Context.interp.downgrade 
  {Γ: _root_.Context} (G: Γ.upgrade.stlc.interp)
  : Γ.stlc.interp
  := by {
    rw [<-Context.downgrade_sparsity_downgrade]
    apply G.thin
  }

@[simp]
theorem Stlc.Context.interp.downgrade_gst
  {A: Term} {Γ: _root_.Context} 
  (x: A.stlc_ty.interp) (G: Γ.upgrade.stlc.interp)
  : @downgrade ((Hyp.gst A)::Γ) (x, G) = G.downgrade
  := rfl

@[simp]
theorem Stlc.Context.interp.downgrade_prop
  {A: Term} {Γ: _root_.Context} (G: Γ.upgrade.stlc.interp)
  : @downgrade ((Hyp.val A prop)::Γ) G = G.downgrade
  := rfl

@[simp]
theorem Stlc.Context.interp.downgrade_ty
  {A: Term} {Γ: _root_.Context} 
  (x: A.stlc_ty.interp) (G: Γ.upgrade.stlc.interp)
  : @downgrade ((Hyp.val A type)::Γ) (x, G) = (x, G.downgrade)
  := by {
    dsimp only [downgrade, Eq.mpr]
    rw [monorecursor]
    dsimp only [thin]
    rw [monorecursor]
    rw [pair_mono_transport]
    rw [Context.downgrade_sparsity_downgrade]
    rfl
    simp only [Sparsity.thin, Context.downgrade_sparsity_downgrade]
    rfl
  }
  
theorem Context.sparsity_true {Γ: Context}
  : H.kind = HypKind.val type -> sparsity (H::Γ) = true::Γ.sparsity
  := by {
    intro H;
    simp [sparsity, Hyp.sparsity, H]
  }

theorem Context.sparsity_false {Γ: Context}
  : H.kind ≠ HypKind.val type -> sparsity (H::Γ) = false::Γ.sparsity
  := by {
    cases H with
    | mk A k =>
      intro H;
      simp [sparsity, Hyp.sparsity]
      cases k with
      | val s => cases s with | type => contradiction | prop => rfl
      | gst => rfl
  }

def Context.stlc_ix (Γ: Context): Nat -> Nat := Γ.sparsity.ix

abbrev Sparsity.stlc (σ: Sparsity) (n: Nat): Stlc
  := if σ.dep n then Stlc.var (σ.ix n) else Stlc.abort

def Term.stlc: Term -> Sparsity -> Stlc
| var n, σ => σ.stlc n
| const TermKind.nil, _ => Stlc.nil
| abs TermKind.lam A x, σ => Stlc.lam A.stlc_ty (x.stlc (true::σ))
| tri TermKind.app P l r, σ => Stlc.app P.stlc_ty (l.stlc σ) (r.stlc σ)
| bin TermKind.pair l r, σ => Stlc.pair (l.stlc σ) (r.stlc σ)
| let_bin TermKind.let_pair P e e', σ => 
  Stlc.let_pair P.stlc_ty (e.stlc σ) (e'.stlc (true::true::σ))
| unary (TermKind.inj i) e, σ => Stlc.inj i (e.stlc σ)
| cases TermKind.case P d l r, σ => 
  Stlc.case P.stlc_ty (d.stlc σ) (l.stlc (true::σ)) (r.stlc (true::σ))
| abs TermKind.lam_pr _ x, σ => x.stlc (false::σ)
| tri TermKind.app_pr _ e _, σ => e.stlc σ
| bin TermKind.elem e _, σ => e.stlc σ
| let_bin TermKind.let_set P e e', σ =>
  Stlc.let_in P.stlc_ty (e.stlc σ) (e'.stlc (false::true::σ))
| abs TermKind.lam_irrel _ x, σ => x.stlc (false::σ)
| tri TermKind.app_irrel _ l _, σ => l.stlc σ
| bin TermKind.repr _ r, σ => r.stlc σ
| let_bin TermKind.let_repr P e e', σ => 
  Stlc.let_in P.stlc_ty (e.stlc σ) (e'.stlc (true::false::σ))
| const TermKind.zero, _ => Stlc.zero
| const TermKind.succ, _ => Stlc.succ
| nr (TermKind.natrec k) K n z s, σ => 
  if k = type then
    Stlc.natrec K.stlc_ty (n.stlc σ) (z.stlc σ) (s.stlc (true::false::σ))
  else
    Stlc.abort
| unary TermKind.abort _, _ => Stlc.abort
| _, _ => Stlc.abort

def Term.stlc_var: (var v).stlc σ = σ.stlc v := rfl

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
  (expr k (A.subst σ)).stlc_ty = (expr k A).stlc_ty := by {
    cases k with
    | type => exact H.stlc_ty_subst
    | prop => rfl
  }

theorem Annot.stlc_ty_wk {A k}: ∀{ρ},
  (expr k (A.wk ρ)).stlc_ty = (expr k A).stlc_ty := by {
    cases k with
    | type => apply Term.stlc_ty_wk
    | prop => intros; rfl
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

theorem HasVar.sigma_get? {Γ A n s}:
  HasVar Γ n (HypKind.val s) A ->
  Γ.sparsity.get? n = some (decide (s = type))
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

theorem HasVar.sigma {Γ A n s}:
  HasVar Γ n (HypKind.val s) A ->
  Γ.sparsity.dep n = decide (s = type)
  := by {
    intro H;
    rw [Sparsity.dep_get? H.sigma_get?];
  }

theorem HasVar.sigma_ty {Γ A n}:
  HasVar Γ n (HypKind.val type) A ->
  Γ.sparsity.dep n = true
  := by {
    intro H;
    rw [H.sigma]
    rfl
  }

theorem HasVar.sigma_prop {Γ A n}:
  HasVar Γ n (HypKind.val prop) A ->
  Γ.sparsity.dep n = false
  := by {
    intro H;
    exact H.sigma
  }

-- But why...
set_option maxHeartbeats 1000000

theorem HasType.stlc {Γ a A}:
  (Γ ⊢ a : A) -> Stlc.HasType Γ.stlc (a.stlc Γ.sparsity) A.stlc_ty := by {
    intro H;
    induction H with
    | var _ Hv => 
      rename AnnotSort => s;
      rw [Term.stlc_var]
      dsimp only [Sparsity.stlc]
      rw [Hv.sigma]
      cases s with
      | type => exact Stlc.HasType.var Hv.stlc
      | prop => exact Stlc.HasType.abort
    | natrec HC _ _ Hs IC Ie Iz Is => 
      rename AnnotSort => k;
      cases k with
      | type =>
        dsimp only [
          Term.stlc, Term.stlc_ty
        ] at *;
        simp only [
          Term.alpha0, Term.subst0, Annot.subst0,
          Annot.stlc_ty_subst, Annot.stlc_ty_wk,
          Term.stlc_ty_wk, wknth,
          term, proof
        ] at *
        repeat rw [Annot.stlc_ty_subst] at *
        repeat rw [Annot.stlc_ty_wk] at *
        constructor <;> assumption
        repeat first
        | assumption
        | (
          apply HasType.wk_sort
          assumption
          repeat constructor
          assumption
        )
      | prop => exact Stlc.HasType.abort
    | _ =>
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

theorem HasType.stlc_prop_is_none {Γ a A G} (H: Γ ⊢ a: expr prop A)
  : H.stlc.interp G = none
  := by {
    generalize Stlc.HasType.interp _ _ = x;
    cases x with
    | some x => cases x
    | none => rfl
  }