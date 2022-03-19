import LogicalRefinement.Wk

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
def Ty.interp.app {A B} (l: (arrow A B).interp) (r: A.interp): B.interp := by
  cases A <;>
  exact match l, r with
  | some l, some r => l r
  | _, _ => B.abort
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
def Ty.interp.cases {A B C: Ty} 
  (d: (coprod A B).interp) 
  (l: A.interp_val -> C.interp) (r: B.interp_val -> C.interp)
  : C.interp
  := match d with
  | some (Sum.inl a) => l a
  | some (Sum.inr b) => r b
  | none => C.abort
def Ty.interp.natrec_inner {C: Ty} (n: Nat) 
  (z: C.interp) (s: C.interp -> C.interp)
  : C.interp
  := match n with
  | 0 => z
  | n + 1 => s (natrec_inner n z s)
def Ty.interp.natrec {C: Ty} (n: nats.interp)
  (z: C.interp) (s: C.interp -> C.interp)
  : C.interp
  := match n with
  | some n => natrec_inner n z s
  | none => C.abort

inductive Stlc
-- Basic
| var (n: Nat)
| lam (A: Ty) (s: Stlc)
| app (P: Ty) (s t: Stlc)

-- Products and coproducts
| pair (l r: Stlc)
| let_pair (P: Ty) (e: Stlc) (e': Stlc)

| inj (f: Fin 2) (e: Stlc)
| cases (P: Ty) (d l r: Stlc)

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
| pair l r, ρ => pair (l.wk ρ) (r.wk ρ)
| let_pair P e e', ρ => let_pair P (e.wk ρ) (e'.wk (ρ.liftn 2))
| inj i e, ρ => inj i (e.wk ρ)
| cases P d l r, ρ => cases P (d.wk ρ) (l.wk ρ.lift) (r.wk ρ.lift)
| natrec n z s, ρ => natrec (n.wk ρ) (z.wk ρ) (s.wk ρ.lift)
| c, ρ => c

def Stlc.wk1 (σ: Stlc): Stlc := σ.wk Wk.wk1

def Stlc.Context := List Ty

def Stlc.Context.interp: Context -> Type
| [] => Unit
| A::As => Prod A.interp_val (interp As)

inductive Stlc.HasVar: Context -> Ty -> Nat -> Prop
| zero {Γ A}: HasVar (A::Γ) A 0
| succ {Γ A B n}: HasVar Γ A n -> HasVar (B::Γ) A (Nat.succ n)

theorem Stlc.HasVar.zero_invert {Γ A B} (P: HasVar (A::Γ) B 0): A = B := by cases P; rfl
theorem Stlc.HasVar.succ_invert {Γ A B} (P: HasVar (A::Γ) B (n + 1)): HasVar Γ B n := by cases P; assumption

def Stlc.HasVar.interp {Γ A n} (H: HasVar Γ A n) (G: Γ.interp): A.interp_val :=
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
| var {Γ A n}: HasVar Γ A n -> HasType Γ (var n) A
| lam {Γ A B s}: HasType (A::Γ) s B -> HasType Γ (lam A s) (arrow A B)
| app {Γ A B s t}: HasType Γ s (arrow A B) -> HasType Γ t A -> HasType Γ (app (arrow A B) s t) B

| pair {Γ A B l r}: HasType Γ l A -> HasType Γ r B -> HasType Γ (pair l r) (prod A B)
| let_pair {Γ A B C e e'}: 
  HasType Γ e (prod A B) -> HasType (B::A::Γ) e' C -> HasType Γ (let_pair (prod A B) e e') C

| inj0 {Γ A B e}: HasType Γ e A -> HasType Γ (inj 0 e) (coprod A B)
| inj1 {Γ A B e}: HasType Γ e B -> HasType Γ (inj 1 e) (coprod A B)
| cases {Γ A B C d l r}: 
  HasType Γ d (coprod A B) -> HasType (A::Γ) l C -> HasType (B::Γ) r C -> 
  HasType Γ (cases (coprod A B) d l r) C

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

-- theorem Stlc.HasType.wk {Γ Δ ρ a A}: WkCtx ρ Γ Δ -> HasType Δ a A -> HasType Γ (a.wk ρ) A := by {
--   sorry
-- }

def Stlc.Subst := Nat -> Stlc

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
| pair l r, σ => pair (l.subst σ) (r.subst σ)
| let_pair P e e', σ => let_pair P (e.subst σ) (e'.subst (σ.liftn 2))
| inj i e, σ => inj i (e.subst σ)
| cases P d l r, σ => cases P (d.subst σ) (l.subst σ.lift) (r.subst σ.lift)
| natrec n z s, σ => natrec (n.subst σ) (z.subst σ) (s.subst σ.lift)
| c, σ => c

def Stlc.SubstCtx (σ: Subst) (Γ Δ: Context): Prop :=  
  ∀{n A}, HasVar Δ A n -> HasType Γ (σ n) A

-- theorem Stlc.HasType.subst {Γ Δ σ a A}: 
--   SubstCtx σ Γ Δ -> HasType Δ a A -> HasType Γ (a.subst σ) A := by {
--   sorry
-- }

def Stlc.HasType.interp {Γ a A} (H: HasType Γ a A) (G: Γ.interp): A.interp :=
  match a with
  | Stlc.var n => 
    let v: HasVar Γ A n := by cases H; assumption;
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
  | Stlc.cases P d l r => by cases P with
    | coprod A' B' =>
      have ⟨Hd, Hl, Hr⟩: HasType Γ d (coprod A' B') ∧ HasType (A'::Γ) l A ∧ HasType (B'::Γ) r A :=
        by cases H; exact ⟨by assumption, by assumption, by assumption⟩
      let Id := Hd.interp G;
      let Il := λa => Hl.interp (a, G);
      let Ir := λb => Hr.interp (b, G);
      exact Id.cases Il Ir
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
    sorry