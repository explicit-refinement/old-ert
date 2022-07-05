prelude
import LogicalRefinement.Sparsity

import LogicalRefinement.Wk
import LogicalRefinement.Tactics
import LogicalRefinement.Utils

inductive Ty
| bot
| unit
| nats
| arrow (A B: Ty)
| prod (A B: Ty)
| coprod (A B: Ty)

open Ty

def Ty.interp_in (A: Ty) (M: Type -> Type): Type 
  :=
    match A with
    | bot => Empty
    | unit => Unit
    | nats => Nat
    | arrow A B => A.interp_in M -> M (B.interp_in M)
    | prod A B => Prod (A.interp_in M) (B.interp_in M)
    | coprod A B => Sum (A.interp_in M) (B.interp_in M)

abbrev Ty.interp (A: Ty): Type := A.interp_in Option
abbrev Ty.abort (A: Ty): Option A.interp := none

@[simp]
abbrev Ty.interp.app {A B} (l: Option (arrow A B).interp) (r: Option A.interp): Option B.interp 
  := l.bind (λl => r.bind l)

@[simp]
abbrev Ty.interp.pair {A B} (l: Option A.interp) (r: Option B.interp): Option (prod A B).interp 
  := l.bind (λl => r.bind (λr => return (l, r)))

@[simp]
abbrev Ty.interp.let_pair {A B C: Ty} 
  (e: Option (prod A B).interp) 
  (e': B.interp -> A.interp -> Option C.interp)
  : Option C.interp 
  := e.bind (λ(a, b) => e' b a)

@[simp]
def Ty.interp.inl {A B} (e: Option A.interp): Option (coprod A B).interp := 
  e.bind (λe => return Sum.inl e)

@[simp]
def Ty.interp.inr {A B} (e: Option B.interp): Option (coprod A B).interp := 
  e.bind (λe => return Sum.inr e)

@[simp]
def Ty.interp.case_inner {A B C: Ty} 
  (d: (coprod A B).interp) 
  (l: A.interp -> Option C.interp) (r: B.interp -> Option C.interp)
  : Option C.interp
  := match d with
  | Sum.inl a => l a
  | Sum.inr b => r b

@[simp]
abbrev Ty.interp.case {A B C: Ty} 
  (d: Option (coprod A B).interp) 
  (l: A.interp -> Option C.interp) (r: B.interp -> Option C.interp)
  : Option C.interp
  := d.bind (λd => d.case_inner l r)

abbrev Ty.interp.natrec_inner {C: Ty} (n: Nat) 
  (z: Option C.interp) (s: C.interp -> Option C.interp)
  : Option C.interp
  := match n with
  | 0 => z
  | n + 1 => (natrec_inner n z s).bind s

abbrev Ty.interp.natrec_int {C: Ty} (n: Option nats.interp)
  (z: Option C.interp) (s: C.interp -> Option C.interp)
  : Option C.interp
  := n.bind (λn => Ty.interp.natrec_inner n z s)

inductive Stlc
  -- Basic
  | var (n: Nat)
  | lam (A: Ty) (s: Stlc)
  | app (P: Ty) (s t: Stlc)

  -- Sugar
  | let_in (A: Ty) (e: Stlc) (e': Stlc)

  -- Products
  | pair (l r: Stlc)
  | let_pair (P: Ty) (e: Stlc) (e': Stlc)

  -- Coproducts
  | inj (f: Fin 2) (e: Stlc)
  | case (P: Ty) (d l r: Stlc)

  -- Erasure
  | nil

  -- Failure
  | abort

  -- Natural numbers
  | zero
  | succ
  | natrec (A: Ty) (n: Stlc) (z: Stlc) (s: Stlc)

def Stlc.let_prop (e: Stlc): Stlc := Stlc.let_in Ty.unit Stlc.nil e
def Stlc.let_one (e: Stlc) (C: Ty): Stlc := Stlc.let_in C (var 1) e

def Stlc.has_var: Stlc -> Nat -> Prop
| var v, n => v = n
| lam _ s, n => s.has_var (n + 1)
| app _ l r, n => l.has_var n ∨ r.has_var n
| let_in _ e e', n => e.has_var n ∨ e'.has_var (n + 1)
| pair l r, n => l.has_var n ∨ r.has_var n
| let_pair _ e e', n => e.has_var n ∨ e'.has_var (n + 2)
| inj _ e, n => e.has_var n
| case _ d l r, n => d.has_var n ∨ l.has_var (n + 1) ∨ r.has_var (n + 1)
| natrec _ n z s, v => n.has_var v ∨ z.has_var v ∨ s.has_var (v + 1)
| _, _ => False

def Stlc.wk: Stlc -> Wk -> Stlc
| var n, ρ => var (ρ.var n)
| lam A s, ρ => lam A (s.wk ρ.lift)
| app P s t, ρ => app P (s.wk ρ) (t.wk ρ)
| let_in A e e', ρ => let_in A (e.wk ρ) (e'.wk ρ.lift)
| pair l r, ρ => pair (l.wk ρ) (r.wk ρ)
| let_pair P e e', ρ => let_pair P (e.wk ρ) (e'.wk (ρ.liftn 2))
| inj i e, ρ => inj i (e.wk ρ)
| case P d l r, ρ => case P (d.wk ρ) (l.wk ρ.lift) (r.wk ρ.lift)
| natrec A n z s, ρ => natrec A (n.wk ρ) (z.wk ρ) (s.wk (ρ.liftn 2))
| c, _ => c

def Stlc.wk1 (s: Stlc): Stlc := s.wk Wk.wk1
def Stlc.wknth (s: Stlc) (n: Nat): Stlc := s.wk (Wk.wknth n)

def Stlc.Context := List Ty

@[simp]
abbrev Stlc.Context.thin (Γ: Context) (Δ: Sparsity): Context := Δ.thin Γ

def Stlc.Context.interp: Context -> Type
| [] => Unit
| A::As => Prod (Option A.interp) (interp As)

def Stlc.Context.interp.thin: {Γ: Context} -> Γ.interp -> (Δ: Sparsity) -> (Γ.thin Δ).interp
| [], (), S => by {
  simp
  exact ()
}
| Γ, G, [] => by {
  simp
  exact G
}
| _A::_Γ, (x, G), true::Δ => (x, G.thin Δ)
-- TODO: report spurious unused variable warning 
-- when `_` is used as name for `_A`
| _A::_Γ, (_, G), false::Δ => G.thin Δ

inductive Stlc.HasVar: Context -> Nat -> Ty -> Prop
| zero {Γ A}: HasVar (A::Γ) 0 A
| succ {Γ A B n}: HasVar Γ n A -> HasVar (B::Γ) (Nat.succ n) A

theorem Stlc.HasVar.zero_invert {Γ A B} (P: HasVar (A::Γ) 0 B): A = B 
  := by cases P; rfl
theorem Stlc.HasVar.succ_invert {Γ A B} (P: HasVar (A::Γ) (n + 1) B)
  : HasVar Γ n B := by cases P; assumption

inductive Stlc.HasType: Context -> Stlc -> Ty -> Prop
| var {Γ A n}: HasVar Γ n A -> HasType Γ (var n) A
| lam {Γ A B s}: HasType (A::Γ) s B -> HasType Γ (lam A s) (arrow A B)
| app {Γ A B s t}: HasType Γ s (arrow A B) -> HasType Γ t A -> HasType Γ (app (arrow A B) s t) B

| let_in {Γ A B e e'}: HasType Γ e A -> HasType (A::Γ) e' B ->
  HasType Γ (let_in A e e') B

| pair {Γ A B l r}: HasType Γ l A -> HasType Γ r B -> 
  HasType Γ (pair l r) (prod A B)
| let_pair {Γ A B C e e'}: 
  HasType Γ e (prod A B) -> HasType (B::A::Γ) e' C -> 
  HasType Γ (let_pair (prod A B) e e') C

| inj0 {Γ A B e}: HasType Γ e A -> HasType Γ (inj 0 e) (coprod A B)
| inj1 {Γ A B e}: HasType Γ e B -> HasType Γ (inj 1 e) (coprod A B)
| case {Γ A B C d l r}: 
  HasType Γ d (coprod A B) -> HasType (A::Γ) l C -> HasType (B::Γ) r C -> 
  HasType Γ (case (coprod A B) d l r) C

| nil {Γ}: HasType Γ nil unit

| abort {Γ A}: HasType Γ abort A

| zero {Γ}: HasType Γ zero nats
| succ {Γ}: HasType Γ succ (arrow nats nats)
| natrec {Γ C n z s}:
  HasType Γ n nats ->
  HasType Γ z C ->
  HasType (C::Ty.unit::Γ) s C ->
  HasType Γ (natrec C n z s) C

notation Γ "⊧" x ":" A => Stlc.HasType Γ x A

def Stlc.HasType.let_prop: HasType (Ty.unit::Γ) e A -> HasType Γ e.let_prop A
  := by {
    intro H;
    constructor
    constructor
    exact H
  }

def Stlc.HasType.has_var: HasType Γ (Stlc.var n) A -> HasVar Γ n A
  := by {
    intro H;
    cases H;
    assumption
  }

inductive Stlc.WkCtx: Wk -> Context -> Context -> Prop
  | id: WkCtx Wk.id Γ Γ
  | step {A ρ Γ Δ}: WkCtx ρ Γ Δ -> WkCtx ρ.step (A::Γ) Δ 
  | lift {A ρ Γ Δ}: WkCtx ρ Γ Δ -> WkCtx ρ.lift (A::Γ) (A::Δ)

theorem Stlc.WkCtx.lift2 {ρ Γ Δ A B} (R: WkCtx ρ Γ Δ):
  WkCtx (ρ.liftn 2) (A::B::Γ) (A::B::Δ)
  := R.lift.lift

theorem Ty.to_wk {Γ} (B: Ty): Stlc.WkCtx Wk.wk1 (B::Γ) Γ 
  := Stlc.WkCtx.step Stlc.WkCtx.id

theorem Stlc.HasVar.wk {Γ Δ n A} (H: HasVar Δ n A):
  ∀{ρ}, WkCtx ρ Γ Δ -> HasVar Γ (ρ.var n) A := by {
    intro ρ R;
    revert H A n;
    induction R with
    | id => intros; assumption
    | step _ I =>
      intro n A H;
      exact HasVar.succ (I H)
    | lift _ I =>
      intro n A H;
      cases H with
      | zero => exact HasVar.zero
      | succ H => exact HasVar.succ (I H) 
  }

theorem Stlc.HasType.wk {Δ a A} (H: HasType Δ a A): 
  ∀{Γ ρ}, WkCtx ρ Γ Δ -> HasType Γ (a.wk ρ) A := by {
  induction H <;> intro Γ ρ R;
  case var H => exact HasType.var (H.wk R)
  all_goals (
    rename_i' I0 I1 I2;
    constructor <;>
    (first | apply I0 | apply I1 | apply I2) <;>
    (repeat apply WkCtx.lift) <;>
    exact R
  )
}

--TODO: report spurious unused variable warning...
def Stlc.Context.interp.wk {Γ Δ ρ} 
  (G: Γ.interp) 
  (R: WkCtx ρ Γ Δ): Δ.interp := 
  match ρ with
  | Wk.id => by {
      have HΓΔ: Δ = Γ := by cases R; rfl;
      rw [HΓΔ];
      exact G
    }
  | Wk.step ρ => by {
      cases Γ with
      | nil => apply False.elim; cases R
      | cons H Γ =>
        have R': WkCtx ρ Γ Δ := by cases R; assumption;
        cases G with
        | mk x G =>
          exact G.wk R'
    }
  | Wk.lift ρ => by {
      cases Γ with
      | nil => apply False.elim; cases R
      | cons H Γ =>
        cases Δ with
        | nil => apply False.elim; cases R
        | cons H' Δ =>
          have R': WkCtx ρ Γ Δ := by cases R; assumption;
          have HH: H = H' := by cases R; rfl;
          rw [HH] at G;
          cases G with
          | mk x G =>
            exact (x, G.wk R')
    }

def Stlc.Context.interp.wk_id {Γ} {H: WkCtx Wk.id Γ Γ} (G: Γ.interp):
  G.wk H = G
  := by {
    cases H;
    unfold wk
    simp
    rfl
  }

def Stlc.Context.interp.wk_step {Γ Δ ρ} {A: Ty} 
  (G: Γ.interp) 
  (x: Option A.interp) 
  (R: WkCtx ρ Γ Δ):
  @wk (A::Γ) _ _ (x, G) R.step = G.wk R
  := rfl

def Stlc.Context.interp.wk_lift {Γ Δ ρ} {A: Ty} 
  (G: Γ.interp) 
  (x: Option A.interp) 
  (R: WkCtx ρ Γ Δ):
  @wk (A::Γ) (A::Δ) _ (x, G) R.lift = (x, G.wk R)
  := rfl


def Stlc.Context.interp.wk_lift' {Γ Δ ρ} {A: Ty} 
  (G: Γ.interp) 
  (x: Option A.interp) 
  (R: WkCtx ρ Γ Δ)
  (R': WkCtx ρ.lift (A::Γ) (A::Δ)):
  @wk (A::Γ) (A::Δ) _ (x, G) R' = (x, G.wk R)
  := rfl

def Stlc.Context.interp.wk_wk1 {Γ: Context} {A: Ty} 
  (G: Γ.interp) 
  (x: Option A.interp) 
  (R: WkCtx Wk.wk1 (A::Γ) Γ):
  @wk (A::Γ) _ _ (x, G) R = G
  := by {
    cases R;
    rw [Stlc.Context.interp.wk_step]
    rw [Stlc.Context.interp.wk_id]
    assumption
  }

def Stlc.Subst := Nat -> Stlc

def Stlc.to_subst (s: Stlc): Subst
| 0 => s
| n + 1 => var n

def Stlc.Subst.lift (σ: Subst): Subst
| 0 => var 0
| n + 1 => (σ n).wk1

def Stlc.Subst.lift_succ (σ: Subst): σ.lift (Nat.succ n) = (σ n).wk1
:= rfl

def Stlc.Subst.liftn (σ: Subst): Nat -> Subst
| 0 => σ
| n + 1 => (σ.lift).liftn n

def Stlc.subst: Stlc -> Subst -> Stlc
| var n, σ => σ n
| lam A s, σ => lam A (s.subst σ.lift)
| app P s t, σ => app P (s.subst σ) (t.subst σ)
| let_in A e e', σ => let_in A (e.subst σ) (e'.subst σ.lift)
| pair l r, σ => pair (l.subst σ) (r.subst σ)
| let_pair P e e', σ => let_pair P (e.subst σ) (e'.subst (σ.liftn 2))
| inj i e, σ => inj i (e.subst σ)
| case P d l r, σ => case P (d.subst σ) (l.subst σ.lift) (r.subst σ.lift)
| natrec C n z s, σ => natrec C (n.subst σ) (z.subst σ) (s.subst (σ.liftn 2))
| c, _ => c

def Stlc.subst_var: (Stlc.var n).subst σ = σ n := rfl

def Stlc.subst0 (s: Stlc) (e: Stlc): Stlc := s.subst e.to_subst
def Stlc.subst1 (s: Stlc) (e: Stlc): Stlc := s.subst e.to_subst.lift
def Stlc.substn (s: Stlc) (n: Nat) (e: Stlc): Stlc := s.subst (e.to_subst.liftn n)

def Stlc.lower0 (s: Stlc): Stlc := s.subst0 abort
def Stlc.lower1 (s: Stlc): Stlc := s.subst1 abort
def Stlc.lower (s: Stlc) (n: Nat): Stlc := s.substn n abort

def Stlc.SubstCtx (σ: Subst) (Γ Δ: Context): Prop :=  
  ∀{n A}, HasVar Δ n A -> HasType Γ (σ n) A

def Stlc.SubstCtx.pop {σ} {Γ Δ: Context} (S: SubstCtx σ Γ (H::Δ))
  : SubstCtx (λn => σ n.succ) Γ Δ
  := λHv => S Hv.succ

def Stlc.HasType.subst0_ctx {Γ a A} (H: HasType Γ a A)
  : SubstCtx (a.to_subst) Γ (A::Γ)
  := by {
    intro n;
    cases n with
    | zero => intro B H; cases H; assumption
    | succ => intro B H; cases H; constructor; assumption
  }

def Stlc.SubstCtx.lift {σ Γ Δ A} (S: SubstCtx σ Γ Δ)
  : SubstCtx (σ.lift) (A::Γ) (A::Δ)
  := by {
    intro n;
    cases n with
    | zero => intro B H; cases H; repeat constructor
    | succ n => 
      intro B H 
      cases H
      apply HasType.wk; 
      apply S; 
      assumption
      repeat constructor
  }

def Stlc.SubstCtx.lift2 {σ Γ Δ A B} (S: SubstCtx σ Γ Δ)
  : SubstCtx (σ.liftn 2) (A::B::Γ) (A::B::Δ)
  := lift S.lift

theorem Stlc.HasType.subst {Δ a A} (H: HasType Δ a A): 
  ∀{Γ σ}, SubstCtx σ Γ Δ -> HasType Γ (a.subst σ) A := by {
  induction H <;> intro Γ σ S;
  case var H => exact S H
  all_goals (
    rename_i' I0 I1 I2;
    constructor <;>
    (first | apply I0 | apply I1 | apply I2) <;>
    (repeat apply SubstCtx.lift) <;>
    exact S
  )
}

theorem Stlc.HasType.subst0 {Γ a A s B} 
  (H: HasType (B::Γ) a A) 
  (Hs: HasType Γ s B):
  HasType Γ (a.subst0 s) A := H.subst Hs.subst0_ctx

theorem Stlc.HasType.subst1 {Γ a A s B P} 
  (H: HasType (P::B::Γ) a A) 
  (Hs: HasType Γ s B):
  HasType (P::Γ) (a.subst1 s) A := by {
    apply subst H;
    apply SubstCtx.lift;
    exact Hs.subst0_ctx
  }

theorem Stlc.HasType.lower0 {Γ a A B} (H: HasType (B::Γ) a A)
  : HasType Γ a.lower0 A 
  := H.subst0 abort

theorem Stlc.HasType.lower1 {Γ a A B P} (H: HasType (P::B::Γ) a A)
  : HasType (P::Γ) a.lower1 A 
  := H.subst1 abort

def Stlc.Context.deriv (Γ: Context) (A: Ty): Type 
  := Γ.interp -> Option A.interp

def Stlc.Context.deriv.wk {Γ Δ ρ A} (D: Δ.deriv A) (R: WkCtx ρ Γ Δ): Γ.deriv A
  := λG => D (Stlc.Context.interp.wk G R)

def Stlc.Context.deriv.wk_def {Γ Δ ρ A} 
  (D: Δ.deriv A) 
  (R: WkCtx ρ Γ Δ)
  (G: Γ.interp): (D.wk R) G = D (Stlc.Context.interp.wk G R)
  := rfl

def Stlc.Context.deriv.wk_step {Γ Δ ρ A} {B: Ty} 
  (D: Δ.deriv A) (R: WkCtx ρ Γ Δ) (x: Option B.interp) (G: Γ.interp)
  : D.wk R.step (x, G) = D.wk R G
  := rfl

def Stlc.Context.deriv.wk_lift {Γ Δ ρ A} {B: Ty} 
  (D: Context.deriv (B::Δ) A) (R: WkCtx ρ Γ Δ) (x: Option B.interp) (G: Γ.interp)
  : D.wk R.lift (x, G) = Context.deriv.wk (λD' => D (x, D')) R G
  := rfl

--TODO: report spurious unused variable warnings...
def Stlc.HasVar.interp {Γ A n} (H: HasVar Γ n A): Γ.deriv A :=
  λG =>
  match Γ with
  | [] => by {
    apply False.elim;
    cases H
  }
  | B::Γ => 
    let (IA, G) := G; 
    match n with
    | 0 => by rw [H.zero_invert] at IA; exact IA
    | Nat.succ n => H.succ_invert.interp G

--TODO: report spurious unused variable warning...
def Stlc.HasType.interp {Γ a A} (H: HasType Γ a A): Γ.deriv A :=
  λG =>
  match a with
  | Stlc.var n => 
    let v: HasVar Γ n A := by cases H; assumption;
    v.interp G
  | Stlc.lam X s => by cases A with
    | arrow A B =>
      have H: HasType (A::Γ) s B := by cases H; assumption;
      exact some (λx => H.interp (x, G))
    | _ => apply False.elim; cases H
  | Stlc.app P l r => 
    by 
    have Hl: HasType Γ l P := by cases H; assumption;
    cases P with
    | arrow A' B' =>
      have HA: B' = A := by cases H; rfl;
      have Hr: HasType Γ r A' := by cases H; assumption;
      let Il := Hl.interp G;
      let Ir := Hr.interp G;
      let I := Ty.interp.app Il Ir;
      rw [HA] at I;
      exact I
    | _ => apply False.elim; cases H
  | Stlc.let_in A' e e' => by
    have He: HasType Γ e A' :=
      by cases H; assumption;
    have He': HasType (A'::Γ) e' A :=
      by cases H; assumption;
    exact (He.interp G).bind (λv => He'.interp (v, G))
  | Stlc.pair l r => by cases A with
    | prod A B =>
      have Hl: HasType Γ l A := by cases H; assumption;
      have Hr: HasType Γ r B := by cases H; assumption;
      let Il := Hl.interp G;
      let Ir := Hr.interp G;
      exact Ty.interp.pair Il Ir
    | _ => apply False.elim; cases H
  | Stlc.let_pair P e e' => by cases P with
    | prod A' B' =>
      have He: HasType Γ e (prod A' B')
        := by cases H; assumption;
      have He':HasType (B'::A'::Γ) e' A
        := by cases H; assumption;
      let Ie := He.interp G;
      let Ie' := λ b a => He'.interp (return b, return a, G);
      exact Ty.interp.let_pair Ie Ie'
    | _ => apply False.elim; cases H
  | Stlc.inj i e => by cases A with
    | coprod A B => match i with
      | 0 =>
        have He: HasType Γ e A := by cases H; assumption;
        exact Ty.interp.inl (He.interp G)
      | 1 =>
        have He: HasType Γ e B := by cases H; assumption;
        exact Ty.interp.inr (He.interp G)
    | _ => apply False.elim; cases H
  | Stlc.case P d l r => by cases P with
    | coprod A' B' =>
      have Hd: HasType Γ d (coprod A' B') :=
        by cases H; assumption;
      have Hl: HasType (A'::Γ) l A :=
        by cases H; assumption;
      have Hr: HasType (B'::Γ) r A :=
        by cases H; assumption;
      let Id := Hd.interp G;
      let Il := λa => Hl.interp (return a, G);
      let Ir := λb => Hr.interp (return b, G);
      exact Ty.interp.case Id Il Ir
    | _ => apply False.elim; cases H
  | Stlc.nil => by cases A with 
    | unit => exact some () 
    | _ => apply False.elim; cases H 
  | Stlc.abort => A.abort
  | Stlc.zero => by cases A with 
    | nats => exact some Nat.zero 
    | _ => apply False.elim; cases H 
  | Stlc.succ => by cases A with 
    | arrow A B =>
      cases A with
      | nats => cases B with
        | nats => exact some (λn => some n.succ)
        | _ => apply False.elim; cases H 
      | _ => apply False.elim; cases H 
    | _ => apply False.elim; cases H 
  --TODO: report that; if the "by", "exact", and "have" are removed, this breaks, to Zulip/GitHub. Fascinating!
  | Stlc.natrec C n z s =>
    by
      have Hn: HasType Γ n nats
        := by cases H; assumption;
      have Hz: HasType Γ z A
        := by cases H; assumption;
      have Hs: HasType (A::Ty.unit::Γ) s A
        := by cases H; assumption;
      let In := Hn.interp G;
      let Iz := Hz.interp G;
      let Is := λc => Hs.interp (return c, return (), G);
      exact Ty.interp.natrec_int In Iz Is

def Stlc.HasType.interp_var {Γ n A} (H: Stlc.HasType Γ (Stlc.var n) A)
  : H.interp = H.has_var.interp
  := rfl
def Stlc.HasType.interp_var_app {Γ G n A} 
  (H: Stlc.HasType Γ (Stlc.var n) A)
  : H.interp G = H.has_var.interp G
  := rfl

theorem Stlc.HasVar.interp_wk {Γ Δ ρ n A}
  (H: HasVar Δ n A)
  (R: WkCtx ρ Γ Δ)
  :
  (H.wk R).interp = H.interp.wk R
  := by {
    revert n A H;
    induction R with
    | id => 
      intros; 
      funext G;
      simp [Context.deriv.wk, Context.interp.wk_id]
      rfl
    | step R I =>
      intro n A H;
      funext G; cases G;
      conv =>
        congr
        reduce
        skip
        rw [H.interp.wk_step R]
        rw [<-I]
    | lift R I =>
      intro N A H;
      funext G; cases G;
      cases H with
      | zero => rfl
      | succ H =>
        conv =>
          congr
          reduce
          skip
          rw [H.succ.interp.wk_lift R]
          arg 1
          reduce
          ext
        rw [<-I]
        rfl
  }

theorem option_helper {a b: A}: a = b -> some a = some b := by intros; simp [*]
def eq_mp_helper {p: A = A}: Eq.mp p = id := rfl
def eq_mp_helper' {p: A = A}: Eq.mp p x = x := rfl
def bind_helper (p: a = b) (p': c = d)
  : Option.bind a c = Option.bind b d
  := by simp [p, p']
def let_pair_helper (p: a = b) (p': c = d)
  : Ty.interp.let_pair a c = Ty.interp.let_pair b d
  := by simp [p, p']
def case_helper:
  a = a' -> b = b' -> c = c' -> Ty.interp.case a b c = Ty.interp.case a' b' c'
  := by intros; simp [*]
def natrec_helper:
  a = a' -> b = b' -> c = c' -> Ty.interp.natrec_int a b c = Ty.interp.natrec_int a' b' c'
  := by intros; simp [*]

theorem Stlc.HasType.interp_wk {Γ Δ ρ a A}
  (H: HasType Δ a A)
  (R: WkCtx ρ Γ Δ)
  :
  (H.wk R).interp = H.interp.wk R
  := by {
    revert Γ ρ R;

    induction H with
    | var v => intros; apply Stlc.HasVar.interp_wk
    | _ => 
      intro Γ ρ R;
      funext G;
      first | rfl |
      rename_i' I0 I1 I2;
      simp only [interp, eq_mp_helper']
      first
      | apply option_helper
      | apply bind_val_helper
      | apply let_pair_helper
      | apply case_helper
      | apply natrec_helper
      | skip 
      repeat any_goals (
        (first | rw [I0] | rw [I1] | rw [I2])
        <;> (first | exact R | exact R.lift | exact R.lift.lift | skip); 
        try rfl
      )
  }

theorem Stlc.HasType.interp_wk1 {Γ a} {A B: Ty}
  (H: HasType Γ a A)
  (x: Option B.interp)
  (G: Γ.interp)
  :
  (H.wk (B.to_wk)).interp (x, G) = H.interp G
  := by {
    rw [interp_wk H B.to_wk]
    simp only [
      Context.deriv.wk, Context.interp.wk, Context.interp.wk_id
    ]
  }
  
@[simp]
theorem Stlc.HasType.var_interp_wk1 {Γ a b n} {A B: Ty}
  (H: HasType Γ a A)
  (H': HasType (B::Γ) b A)
  (x: Option B.interp)
  (G: Γ.interp)
  (Ha: a = Stlc.var n)
  (Hb: b = Stlc.var (n + 1))
  :
  H'.interp (x, G) = H.interp G
  := by {
    cases Ha;
    cases Hb;
    cases H;
    cases H';
    rfl
  }
  
@[simp]
theorem Stlc.HasType.var_interp_0 {Γ: Context} {a} {A B: Ty}
  (H: HasType (B::Γ) a A)
  (x: Option B.interp)
  (G: Γ.interp)
  (Ha: a = Stlc.var 0)
  (HA)
  :
  H.interp (x, G) = cast HA x
  := by {
    cases Ha;
    rfl
  }

def Stlc.Context.deriv.step {Γ: Context} {A} (D: Γ.deriv A) (B: Ty)
  : Context.deriv (B::Γ) A
  := λ(_, G) => D G

theorem Stlc.HasType.interp_transport
  {A B: Ty}
  {a b: Stlc}
  (HA: HasType Γ a A)
  (HB: HasType Γ b B)
  (Hab: a = b)
  (HAB: A = B)
  : HAB ▸ HA.interp = HB.interp
  := by {
    cases HAB;
    simp only [Eq.rec]
    cases Hab;
    cases HA <;> cases HB <;> rfl 
  }
  
theorem Stlc.HasType.interp_transport_inner
  {A B: Ty}
  {a b: Stlc}
  (HA: HasType Γ a A)
  (HB: HasType Γ b B)
  (Hab: a = b)
  (HAB: A = B)
  (G: Γ.interp)
  : HAB ▸ HA.interp G = HB.interp G
  := by {
    cases HAB;
    simp only [Eq.rec]
    cases Hab;
    cases HA <;> cases HB <;> rfl 
  }

theorem Stlc.HasType.interp_transport_cast
  {Γ}
  {A B: Ty}
  {a b: Stlc}
  (HA: HasType Γ a A)
  (HB: HasType Γ b B)
  (Hab: a = b)
  (HAB: A = B)
  : @cast (Γ.deriv A) (Γ.deriv B) (by rw [HAB]) HA.interp = HB.interp
  := by {
    cases Hab;
    cases HAB;
    rfl
  }

theorem Stlc.HasType.interp_transport_cast'
  {Γ}
  {A B: Ty}
  {a b: Stlc}
  (HA: HasType Γ a A)
  (HB: HasType Γ b B)
  (Hab: a = b)
  (HAB: A = B)
  (G: Γ.interp)
  : @cast (Option A.interp) (Option B.interp) (by rw [HAB]) (HA.interp G) = HB.interp G
  := by {
    cases Hab;
    cases HAB;
    rfl
  }

theorem Stlc.HasType.interp_transport_cast''
  {Γ Δ}
  {A B: Ty}
  {a b: Stlc}
  (HA: HasType Γ a A)
  (HB: HasType Δ b B)
  (Hab: a = b)
  (HAB: A = B)
  (HΓΔ: Γ = Δ)
  (G: Γ.interp)
  (D: Δ.interp)
  (HGD: G = HΓΔ ▸ D)
  : @cast (Option A.interp) (Option B.interp) (by rw [HAB]) (HA.interp G) = HB.interp D
  := by {
    cases HΓΔ;
    cases Hab;
    cases HAB;
    simp only [HGD]
    rfl
  }

theorem Stlc.HasType.interp_irrel
  (H: Γ ⊧ a: A)
  (H': Γ ⊧ a: A)
  : H.interp = H'.interp
  := rfl

theorem interp_eq_collapse
  : 
  @Eq.rec Ty b 
    (λx _ => Option (Ty.interp x)) 
    (@Eq.rec Ty a (λx _ => Option (Ty.interp x)) v b p) a p' 
  = v
  := by {
    cases p;
    rfl
  }

theorem interp_congr
  (H: Γ ⊧ a: A)
  (H': Γ ⊧ b: A)
  (p: a = b)
  : H.interp = H'.interp
  := by {
    cases p;
    rfl
  }
  
theorem Stlc.HasType.interp_wk1' {Γ a a'} {A B: Ty}
  (H: HasType Γ a A)
  (H': HasType (B::Γ) a' A)
  (Ha': a' = a.wk1)
  (x: Option B.interp)
  (G: Γ.interp)
  :
  H'.interp (x, G) = H.interp G
  := by {
    cases Ha';
    rw [<-H.interp_wk1 x G]
    rfl
  }

def Stlc.Subst.wk1 (σ: Subst): Subst :=
  λv => (σ v).wk1

@[simp]
def Wk.to_stlc_subst (ρ: Wk): Stlc.Subst :=
  λv => Stlc.var (ρ.var v)

instance Wk.wk_stlc_subst_coe: Coe Wk Stlc.Subst where
  coe := Wk.to_stlc_subst

def Wk.to_stlc_subst_lift {ρ: Wk}: 
  ρ.to_stlc_subst.lift = ρ.lift.to_stlc_subst := by {
  funext v;
  cases v <;> rfl
}


theorem Stlc.Subst.liftn_lift_commute {σ: Stlc.Subst} {n}
  : σ.lift.liftn n = (σ.liftn n).lift 
  := by {
    induction n generalizing σ with
    | zero => rfl
    | succ n I =>
      simp only [liftn]
      rw [I]
  }

def Wk.to_stlc_subst_liftn {n: Nat} {ρ: Wk}:
  ρ.to_stlc_subst.liftn n = (ρ.liftn n).to_stlc_subst := by {
    induction n generalizing ρ with
    | zero => rfl
    | succ n I =>
      simp only [liftn, Stlc.Subst.liftn]
      rw [<-to_stlc_subst_lift]
      rw [<-I]
      exact Stlc.Subst.liftn_lift_commute
}

theorem Stlc.Subst.subst_wk_compat {u: Stlc} {ρ: Wk}:
  u.subst ρ = u.wk ρ := by { 
  induction u generalizing ρ <;> {
    intros;
    simp only [
      Stlc.subst, 
      Wk.to_stlc_subst_lift, Wk.to_stlc_subst_liftn, 
      *]
    rfl
  }
}

theorem Stlc.HasType.interp_transport_mono
  {A B: Ty}
  {a b: Stlc}
  (HA: HasType Γ a A)
  (HB: HasType Γ b B)
  (Hab: a = b)
  (HAB: A = B)
  (H)
  (G: Γ.interp)
  : @Eq.rec 
    Type 
    (Option A.interp) (λA _ => A) (HA.interp G) 
    (Option B.interp) H = HB.interp G
  := by {
    cases Hab;
    cases HAB;
    cases H;
    cases HA <;> cases HB <;> rfl 
  }

theorem interp_eq_none
  : @Eq.rec Ty a (λx _ => Option (Ty.interp x)) none x p = none := by {
    cases p <;> rfl
  }

theorem interp_eq_none' {n: Option (Ty.interp a)}
  : n = none -> @Eq.rec Ty a (λx _ => Option (Ty.interp x)) n x p = none := by {
    intro H;
    cases H <;>
    cases p <;> rfl
  }

theorem interp_eq_some
  : @Eq.rec Ty a (λx _ => Option (Ty.interp x)) (some v) x p = (some (p ▸ v)) := by {
    cases p <;> rfl
  }


def Stlc.HasType.wk_def {Γ Δ ρ a A} 
  (H: Δ ⊧ a: A) 
  (R: WkCtx ρ Γ Δ)
  (G: Γ.interp): (H.interp.wk R) G = H.interp (Stlc.Context.interp.wk G R)
  := rfl