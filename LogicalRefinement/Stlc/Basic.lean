import LogicalRefinement.Wk
import LogicalRefinement.Tactics

inductive Ty
| bot
| unit
| nats
| arrow (A B: Ty)
| prod (A B: Ty)
| coprod (A B: Ty)

open Ty

def Ty.interp_based_in (A: Ty) (M: Type -> Type): (Type -> Type) -> Type := λU => U (match A with
| bot => Empty
| unit => Unit
| nats => Nat
| arrow A B => A.interp_based_in M id -> B.interp_based_in M M
| prod A B => Prod (A.interp_based_in M id) (B.interp_based_in M id)
| coprod A B => Sum (A.interp_based_in M id) (B.interp_based_in M id))

def Ty.interp_in (A: Ty) (M: Type -> Type) := A.interp_based_in M M
def Ty.interp_val_in (A: Ty) (M: Type -> Type) := A.interp_based_in M id
def Ty.interp_val_char {A: Ty} {M}: A.interp_in M = M (A.interp_val_in M) := by cases A <;> rfl

-- Note: if the λx gets moved into the match, we get a kernel error; maybe post on Zulip about this...
def Ty.eager {A: Ty} {M: Type -> Type} [Monad M]: A.interp_val_in M -> A.interp_in M := 
  λx => by cases A with
    | bot => cases x
    | _ => exact do return x

instance myOptionMonad: Monad Option where
  pure := some
  bind := λx f => match x with | none => none | some x => f x 

def Ty.interp (A: Ty): Type := A.interp_in Option
def Ty.interp_val (A: Ty): Type := A.interp_val_in Option

def Ty.abort (A: Ty): A.interp := by cases A <;> exact none

def Ty.interp.bind_val {A B: Ty} 
  (l: A.interp_val -> B.interp) (r: A.interp): B.interp
  := by cases A <;>
     exact match r with
     | some r => l r
     | none => B.abort
def Ty.interp.app {A B} (l: (arrow A B).interp) (r: A.interp): B.interp :=
  match l with
  | some l => bind_val l r
  | none => B.abort
def Ty.interp.pair {A B} (l: A.interp) (r: B.interp): (prod A B).interp := by
  cases A <;> cases B <;>
  exact match l, r with
  | some l, some r => some (l, r)
  | _, _ => none
def Ty.interp.let_pair {A B C: Ty} 
  (e: (prod A B).interp) 
  (e': B.interp_val -> A.interp_val -> C.interp)
  : C.interp 
  := match e with
  | some (a, b) => e' b a
  | none => C.abort
def Ty.interp.inl {A B} (e: A.interp): (coprod A B).interp := by 
  cases A <;> exact e.map Sum.inl
def Ty.interp.inr {A B} (e: B.interp): (coprod A B).interp := by 
  cases B <;> exact e.map Sum.inr
def Ty.interp.case {A B C: Ty} 
  (d: (coprod A B).interp) 
  (l: A.interp_val -> C.interp) (r: B.interp_val -> C.interp)
  : C.interp
  := match d with
  | some (Sum.inl a) => l a
  | some (Sum.inr b) => r b
  | none => C.abort
def Ty.interp.natrec_inner {C: Ty} (n: Nat) 
  (z: C.interp) (s: C.interp_val -> C.interp)
  : C.interp
  := match n with
  | 0 => z
  | n + 1 => bind_val s (natrec_inner n z s)
def Ty.interp.natrec {C: Ty} (n: nats.interp)
  (z: C.interp) (s: C.interp_val -> C.interp)
  : C.interp
  := match n with
  | some n => natrec_inner n z s
  | none => C.abort

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
  | natrec (n: Stlc) (z: Stlc) (s: Stlc)

def Stlc.wk: Stlc -> Wk -> Stlc
| var n, ρ => var (ρ.var n)
| lam A s, ρ => lam A (s.wk ρ.lift)
| app P s t, ρ => app P (s.wk ρ) (t.wk ρ)
| let_in A e e', ρ => let_in A (e.wk ρ) (e'.wk ρ.lift)
| pair l r, ρ => pair (l.wk ρ) (r.wk ρ)
| let_pair P e e', ρ => let_pair P (e.wk ρ) (e'.wk (ρ.liftn 2))
| inj i e, ρ => inj i (e.wk ρ)
| case P d l r, ρ => case P (d.wk ρ) (l.wk ρ.lift) (r.wk ρ.lift)
| natrec n z s, ρ => natrec (n.wk ρ) (z.wk ρ) (s.wk ρ.lift)
| c, ρ => c

def Stlc.wk1 (σ: Stlc): Stlc := σ.wk Wk.wk1

def Stlc.Context := List Ty

def Stlc.Context.interp: Context -> Type
| [] => Unit
| A::As => Prod A.interp_val (interp As)

def Stlc.Context.interp_effect (Γ: Context): Type
  := Option (Γ.interp)

def Stlc.Context.interp_effect.push_effect {A: Ty} {Γ: Context}
  : A.interp -> Γ.interp_effect -> interp_effect (A::Γ)
  := by {
    intro I Γ;
    match Γ with
    | none => exact none
    | some Γ =>
      cases A <;> 
      match I with
      | none => exact none
      | some I => exact some (I, Γ)
  }

inductive Stlc.HasVar: Context -> Nat -> Ty -> Prop
| zero {Γ A}: HasVar (A::Γ) 0 A
| succ {Γ A B n}: HasVar Γ n A -> HasVar (B::Γ) (Nat.succ n) A

theorem Stlc.HasVar.zero_invert {Γ A B} (P: HasVar (A::Γ) 0 B): A = B 
  := by cases P; rfl
theorem Stlc.HasVar.succ_invert {Γ A B} (P: HasVar (A::Γ) (n + 1) B)
  : HasVar Γ n B := by cases P; assumption

def Stlc.HasVar.interp {Γ A n} (H: HasVar Γ n A) (G: Γ.interp)
  : A.interp_val :=
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
  HasType (C::Γ) s C ->
  HasType Γ (natrec n z s) C

inductive Stlc.WkCtx: Wk -> Context -> Context -> Prop
  | id: WkCtx Wk.id Γ Γ
  | step {ρ Γ Δ A}: WkCtx ρ Γ Δ -> WkCtx ρ.step (A::Γ) Δ 
  | lift {ρ Γ Δ A}: WkCtx ρ Γ Δ -> WkCtx ρ.lift (A::Γ) (A::Δ)

theorem Stlc.HasVar.wk {Γ Δ n A} (H: HasVar Δ n A):
  ∀{ρ}, WkCtx ρ Γ Δ -> HasVar Γ (ρ.var n) A := by {
    intro ρ R;
    revert H A n;
    induction R with
    | id => intros; assumption
    | step R I =>
      intro n A H;
      exact HasVar.succ (I H)
    | lift R I =>
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

def Stlc.Subst := Nat -> Stlc

def Stlc.to_subst (s: Stlc): Subst
| 0 => s
| n + 1 => var n

def Stlc.Subst.lift (σ: Subst): Subst
| 0 => var 0
| n + 1 => (σ n).wk1

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
| natrec n z s, σ => natrec (n.subst σ) (z.subst σ) (s.subst σ.lift)
| c, σ => c

def Stlc.subst0 (s: Stlc) (e: Stlc): Stlc := s.subst e.to_subst
def Stlc.subst1 (s: Stlc) (e: Stlc): Stlc := s.subst e.to_subst.lift

def Stlc.lower0 (s: Stlc): Stlc := s.subst0 abort
def Stlc.lower1 (s: Stlc): Stlc := s.subst1 abort

def Stlc.SubstCtx (σ: Subst) (Γ Δ: Context): Prop :=  
  ∀{n A}, HasVar Δ n A -> HasType Γ (σ n) A

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
  := Γ.interp -> A.interp

def Stlc.Context.deriv.ctx_effect {Γ: Context} {A: Ty} (D: Γ.deriv A)
  : Γ.interp_effect -> A.interp
  | some Γ => D Γ
  | none => A.abort

def Stlc.HasType.interp {Γ a A} (H: HasType Γ a A): Γ.deriv A :=
  λG =>
  match a with
  | Stlc.var n => 
    let v: HasVar Γ n A := by cases H; assumption;
    Ty.eager (v.interp G)
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
      have ⟨HA, Hr⟩: B' = A ∧ HasType Γ r A' 
        := by cases H; exact ⟨by rfl, by assumption⟩;
      let Il := Hl.interp G;
      let Ir := Hr.interp G;
      let I := Il.app Ir;
      rw [HA] at I;
      exact I
    | _ => apply False.elim; cases H
  | Stlc.let_in A' e e' => by
    have ⟨He, He'⟩: HasType Γ e A' ∧ HasType (A'::Γ) e' A :=
      by cases H; apply And.intro <;> assumption;
    exact (He.interp G).bind_val (λv => He'.interp (v, G))
  | Stlc.pair l r => by cases A with
    | prod A B =>
      have ⟨Hl, Hr⟩: HasType Γ l A ∧ HasType Γ r B
        := by cases H; exact ⟨by assumption, by assumption⟩
      let Il := Hl.interp G;
      let Ir := Hr.interp G;
      exact Il.pair Ir
    | _ => apply False.elim; cases H
  | Stlc.let_pair P e e' => by cases P with
    | prod A' B' =>
      have ⟨He, He'⟩: HasType Γ e (prod A' B') ∧ HasType (B'::A'::Γ) e' A
        := by cases H; exact ⟨by assumption, by assumption⟩
      let Ie := He.interp G;
      let Ie' := λ b a => He'.interp (b, (a, G));
      exact Ie.let_pair Ie'
    | _ => apply False.elim; cases H
  | Stlc.inj i e => by cases A with
    | coprod A B => match i with
      | 0 =>
        have He: HasType Γ e A := by cases H; assumption;
        exact (He.interp G).inl
      | 1 =>
        have He: HasType Γ e B := by cases H; assumption;
        exact (He.interp G).inr
    | _ => apply False.elim; cases H
  | Stlc.case P d l r => by cases P with
    | coprod A' B' =>
      have ⟨Hd, Hl, Hr⟩: HasType Γ d (coprod A' B') ∧ HasType (A'::Γ) l A ∧ HasType (B'::Γ) r A :=
        by cases H; exact ⟨by assumption, by assumption, by assumption⟩
      let Id := Hd.interp G;
      let Il := λa => Hl.interp (a, G);
      let Ir := λb => Hr.interp (b, G);
      exact Id.case Il Ir
    | _ => apply False.elim; cases H
  | Stlc.nil => by cases A with 
    | unit => exact some () 
    | _ => apply False.elim; cases H 
  | Stlc.abort => A.abort
  | Stlc.zero => by cases A with 
    | nats => exact some 0 
    | _ => apply False.elim; cases H 
  | Stlc.succ => by cases A with 
    | arrow A B =>
      cases A with
      | nats => cases B with
        | nats => exact some (λn => some n.succ)
        | _ => apply False.elim; cases H 
      | _ => apply False.elim; cases H 
    | _ => apply False.elim; cases H 
  | Stlc.natrec n z s =>
    let ⟨Hn, Hz, Hs⟩: HasType Γ n nats ∧ HasType Γ z A ∧ HasType (A::Γ) s A
      := by cases H; exact ⟨by assumption, by assumption, by assumption⟩
    let In := Hn.interp G;
    let Iz := Hz.interp G;
    let Is := λc => Hs.interp (c, G);
    In.natrec Iz Is