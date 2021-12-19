-- Based off https://github.com/mr-ohman/logrel-mltt/blob/master/Definition/Untyped.agda

import Init.Data.Nat
import LogicalRefinement.Wk

inductive UntypedKind: Type where

  -- Types
  | nats
  | pi
  | sigma
  | coprod
  | set
  | assume
  | intersect
  | union

  -- Propositions
  | top
  | bot
  | and
  | or
  | implies
  | forall_
  | exists_
  | eq

  -- Terms
  | nat (n: Nat)
  | lam
  | app
  | pair
  | proj (b: Bool)
  | inj (b: Bool)
  | case
  | mkset
  | letset
  | lam_pr
  | app_pr
  | lam_irrel
  | app_irrel
  | repr
  | let_repr

  -- Proofs
  | nil
  | abort
  | conj
  | comp (b: Bool)
  | disj (b: Bool)
  | case_pr
  | imp
  | mp
  | general
  | inst
  | witness
  | let_wit
  | refl

@[simp] def UntypedKind.arity: UntypedKind -> Nat
  -- Types
  | nats => 0
  | pi => 2
  | sigma => 2
  | coprod => 2
  | set => 2
  | assume => 2
  | intersect => 2
  | union => 2

  -- Propositions
  | top => 0
  | bot => 0
  | and => 2
  | or => 2
  | implies => 2
  | forall_ => 2
  | exists_ => 2
  | eq => 3

  -- Terms
  | nat _ => 0
  | lam => 2
  | app => 2
  | pair => 2
  | proj _ => 1
  | inj _ => 1
  | case => 3
  | mkset => 2
  | letset => 1
  | lam_pr => 2
  | app_pr => 2
  | lam_irrel => 2
  | app_irrel => 2
  | repr => 2
  | let_repr => 1

  -- Proofs
  | nil => 0
  | abort => 1
  | conj => 2
  | comp _ => 1
  | disj _ => 1
  | case_pr => 3
  | imp => 2
  | mp => 2
  | general => 2
  | inst => 2
  | witness => 2
  | let_wit => 1
  | refl => 1

inductive RawUntyped: Type where

  -- Variables
  | var (n: Nat)

  -- Base terms

  -- Types
  | nats
  | pi (A: RawUntyped) (B: RawUntyped)
  | sigma (A: RawUntyped) (B: RawUntyped)
  | coprod (A: RawUntyped) (B: RawUntyped)
  | set (A: RawUntyped) (φ: RawUntyped)
  | assume (φ: RawUntyped) (A: RawUntyped)
  | intersect (A: RawUntyped) (B: RawUntyped)
  | union (A: RawUntyped) (B: RawUntyped)

  -- Propositions
  | top
  | bot
  | and (φ: RawUntyped) (ψ: RawUntyped)
  | or (φ: RawUntyped) (ψ: RawUntyped)
  | implies (φ: RawUntyped) (ψ: RawUntyped)
  | forall_ (A: RawUntyped) (φ: RawUntyped)
  | exists_ (A: RawUntyped) (φ: RawUntyped)
  | eq (A: RawUntyped) (e: RawUntyped) (e': RawUntyped)

  -- Terms
  | nat (n: Nat)
  | lam (A: RawUntyped) (e: RawUntyped)
  | app (l: RawUntyped) (r: RawUntyped)
  | pair (l: RawUntyped) (r: RawUntyped)
  | proj (b: Bool) (e: RawUntyped)
  | inj (b: Bool) (e: RawUntyped)
  | case (e: RawUntyped) (l: RawUntyped) (r: RawUntyped)
  | mkset (e: RawUntyped) (p: RawUntyped)
  | letset (e: RawUntyped)
  | lam_pr (φ: RawUntyped) (e: RawUntyped)
  | app_pr (e: RawUntyped) (p: RawUntyped)
  | lam_irrel (A: RawUntyped) (e: RawUntyped)
  | app_irrel (l: RawUntyped) (r: RawUntyped)
  | repr (l: RawUntyped) (r: RawUntyped)
  | let_repr (e: RawUntyped)

  -- Proofs
  | nil
  | abort (p: RawUntyped)
  | conj (l: RawUntyped) (r: RawUntyped)
  | comp (b: Bool) (p: RawUntyped)
  | disj (b: Bool) (p: RawUntyped)
  | case_pr (p: RawUntyped) (l: RawUntyped) (r: RawUntyped)
  | imp (φ: RawUntyped) (p: RawUntyped)
  | mp (l: RawUntyped) (r: RawUntyped)
  | general (A: RawUntyped) (p: RawUntyped)
  | inst (p: RawUntyped) (e: RawUntyped)
  | witness (e: RawUntyped) (p: RawUntyped)
  | let_wit (p: RawUntyped)
  | refl (e: RawUntyped)


@[simp] def nargs (A B: Type): Nat -> Type
  | 0 => B
  | Nat.succ n => A -> (nargs A B n)

@[simp] def nary (n: Nat) (A: Type): Type := nargs A A n

@[simp] def const_nargs {A B: Type} (b: B): (n: Nat) -> nargs A B n
  | 0 => b
  | Nat.succ n => λ_ => const_nargs b n

@[simp] def UntypedKind.constructorType (k: UntypedKind): Type := nary (arity k) RawUntyped

@[simp] def RawUntyped.mk: (k: UntypedKind) -> UntypedKind.constructorType k
  -- Types
  | UntypedKind.nats => RawUntyped.nats
  | UntypedKind.pi => RawUntyped.pi
  | UntypedKind.sigma => RawUntyped.sigma
  | UntypedKind.coprod => RawUntyped.coprod
  | UntypedKind.set => RawUntyped.set
  | UntypedKind.assume => RawUntyped.assume
  | UntypedKind.intersect => RawUntyped.intersect
  | UntypedKind.union => RawUntyped.union

  -- Propositions
  | UntypedKind.top => RawUntyped.top
  | UntypedKind.bot => RawUntyped.bot
  | UntypedKind.and => RawUntyped.and
  | UntypedKind.or => RawUntyped.or
  | UntypedKind.implies => RawUntyped.implies
  | UntypedKind.forall_ => RawUntyped.forall_
  | UntypedKind.exists_ => RawUntyped.exists_
  | UntypedKind.eq => RawUntyped.eq

  -- Terms
  | UntypedKind.nat n => RawUntyped.nat n
  | UntypedKind.lam => RawUntyped.lam
  | UntypedKind.app => RawUntyped.app
  | UntypedKind.pair => RawUntyped.pair
  | UntypedKind.proj b => RawUntyped.proj b
  | UntypedKind.inj b => RawUntyped.inj b
  | UntypedKind.case => RawUntyped.case
  | UntypedKind.mkset => RawUntyped.mkset
  | UntypedKind.letset => RawUntyped.letset
  | UntypedKind.lam_pr => RawUntyped.lam_pr
  | UntypedKind.app_pr => RawUntyped.app_pr
  | UntypedKind.lam_irrel => RawUntyped.lam_irrel
  | UntypedKind.app_irrel => RawUntyped.app_irrel
  | UntypedKind.repr => RawUntyped.repr
  | UntypedKind.let_repr => RawUntyped.let_repr

  -- Proofs
  | UntypedKind.nil => RawUntyped.nil
  | UntypedKind.abort => RawUntyped.abort
  | UntypedKind.conj => RawUntyped.conj
  | UntypedKind.comp b => RawUntyped.comp b
  | UntypedKind.disj b => RawUntyped.disj b
  | UntypedKind.case_pr => RawUntyped.case_pr
  | UntypedKind.imp => RawUntyped.imp
  | UntypedKind.mp => RawUntyped.mp
  | UntypedKind.general => RawUntyped.general
  | UntypedKind.inst => RawUntyped.inst
  | UntypedKind.witness => RawUntyped.witness
  | UntypedKind.let_wit => RawUntyped.let_wit
  | UntypedKind.refl => RawUntyped.refl

@[simp] def RawUntyped.cons: (k: RawUntyped) -> Option UntypedKind
  | RawUntyped.var _ => Option.none

  -- Types
  | RawUntyped.nats => UntypedKind.nats
  | RawUntyped.pi _ _ => UntypedKind.pi
  | RawUntyped.sigma _ _ => UntypedKind.sigma
  | RawUntyped.coprod _ _ => UntypedKind.coprod
  | RawUntyped.set _ _ => UntypedKind.set
  | RawUntyped.assume _ _ => UntypedKind.assume
  | RawUntyped.intersect _ _ => UntypedKind.intersect
  | RawUntyped.union _ _ => UntypedKind.union

  -- Propositions
  | RawUntyped.top => UntypedKind.top
  | RawUntyped.bot => UntypedKind.bot
  | RawUntyped.and _ _ => UntypedKind.and
  | RawUntyped.or _ _ => UntypedKind.or
  | RawUntyped.implies _ _ => UntypedKind.implies
  | RawUntyped.forall_ _ _ => UntypedKind.forall_
  | RawUntyped.exists_ _ _ => UntypedKind.exists_
  | RawUntyped.eq _ _ _ => UntypedKind.eq

  -- Terms
  | RawUntyped.nat n => UntypedKind.nat n
  | RawUntyped.lam _ _ => UntypedKind.lam
  | RawUntyped.app _ _ => UntypedKind.app
  | RawUntyped.pair _ _ => UntypedKind.pair
  | RawUntyped.proj b _ => UntypedKind.proj b
  | RawUntyped.inj b _ => UntypedKind.inj b
  | RawUntyped.case _ _ _ => UntypedKind.case
  | RawUntyped.mkset _ _ => UntypedKind.mkset
  | RawUntyped.letset _ => UntypedKind.letset
  | RawUntyped.lam_pr _ _ => UntypedKind.lam_pr
  | RawUntyped.app_pr _ _ => UntypedKind.app_pr
  | RawUntyped.lam_irrel _ _ => UntypedKind.lam_irrel
  | RawUntyped.app_irrel _ _ => UntypedKind.app_irrel
  | RawUntyped.repr _ _ => UntypedKind.repr
  | RawUntyped.let_repr _ => UntypedKind.let_repr

  -- Proofs
  | RawUntyped.nil => UntypedKind.nil
  | RawUntyped.abort _ => UntypedKind.abort
  | RawUntyped.conj _ _ => UntypedKind.conj
  | RawUntyped.comp b _ => UntypedKind.comp b
  | RawUntyped.disj b _ => UntypedKind.disj b
  | RawUntyped.case_pr _ _ _ => UntypedKind.case_pr
  | RawUntyped.imp _ _ => UntypedKind.imp
  | RawUntyped.mp _ _ => UntypedKind.mp
  | RawUntyped.general _ _ => UntypedKind.general
  | RawUntyped.inst _ _ => UntypedKind.inst
  | RawUntyped.witness _ _ => UntypedKind.witness
  | RawUntyped.let_wit _ => UntypedKind.let_wit
  | RawUntyped.refl _ => UntypedKind.refl

notation "genRecRawUntyped" u "=>" v_case "," f "," rec_br => match u with
  | RawUntyped.var v => v_case v

  | RawUntyped.nats => rec_br UntypedKind.nats
  | RawUntyped.pi A B => rec_br UntypedKind.pi (f 0 A) (f 1 B)
  | RawUntyped.sigma A B => rec_br UntypedKind.sigma (f 0 A) (f 1 B)
  | RawUntyped.coprod A B => rec_br UntypedKind.coprod (f 0 A) (f 0 B)
  | RawUntyped.set A φ => rec_br UntypedKind.set (f 0 A) (f 1 φ)
  | RawUntyped.assume φ A => rec_br UntypedKind.assume (f 0 φ) (f 0 A)
  | RawUntyped.intersect A B => rec_br UntypedKind.intersect (f 0 A) (f 1 B)
  | RawUntyped.union A B => rec_br UntypedKind.union (f 0 A) (f 1 B)

  | RawUntyped.top => rec_br UntypedKind.top
  | RawUntyped.bot => rec_br UntypedKind.bot
  | RawUntyped.and φ ψ => rec_br UntypedKind.and (f 0 φ) (f 0 ψ)
  | RawUntyped.or φ ψ => rec_br UntypedKind.or (f 0 φ) (f 0 ψ)
  | RawUntyped.implies φ ψ => rec_br UntypedKind.implies (f 0 φ) (f 0 ψ)
  | RawUntyped.forall_ A φ => rec_br UntypedKind.forall_ (f 0 A) (f 1 φ)
  | RawUntyped.exists_ A φ => rec_br UntypedKind.exists_ (f 0 A) (f 1 φ)
  | RawUntyped.eq A e e' => rec_br UntypedKind.eq (f 0 A) (f 0 e) (f 0 e')
  
  | RawUntyped.nat n => rec_br (UntypedKind.nat n)
  | RawUntyped.lam A e => rec_br UntypedKind.lam (f 0 A) (f 1 e)
  | RawUntyped.app s t => rec_br UntypedKind.app (f 0 s) (f 0 t)
  | RawUntyped.pair l r => rec_br UntypedKind.pair (f 0 l) (f 0 r)
  | RawUntyped.proj b e => rec_br (UntypedKind.proj b) (f 0 e)
  | RawUntyped.inj b e => rec_br (UntypedKind.inj b) (f 0 e)
  | RawUntyped.case e l r => rec_br (UntypedKind.case) (f 0 e) (f 0 l) (f 0 r)
  | RawUntyped.mkset e p => rec_br (UntypedKind.mkset) (f 0 e) (f 1 p)
  | RawUntyped.letset e => rec_br (UntypedKind.letset) (f 2 e)
  | RawUntyped.lam_pr φ e => rec_br (UntypedKind.lam_pr) (f 0 φ) (f 1 e)
  | RawUntyped.app_pr e p => rec_br (UntypedKind.app_pr) (f 0 e) (f 0 p)
  | RawUntyped.lam_irrel A e => rec_br (UntypedKind.lam_irrel) (f 0 A) (f 1 e)
  | RawUntyped.app_irrel l r => rec_br (UntypedKind.app_irrel) (f 0 l) (f 0 r)
  | RawUntyped.repr l r => rec_br (UntypedKind.repr) (f 0 l) (f 0 r)
  | RawUntyped.let_repr e => rec_br (UntypedKind.let_repr) (f 2 e)

  | RawUntyped.nil => rec_br UntypedKind.nil
  | RawUntyped.abort p => rec_br UntypedKind.abort (f 0 p)
  | RawUntyped.conj l r => rec_br UntypedKind.conj (f 0 l) (f 0 r)
  | RawUntyped.comp b p => rec_br (UntypedKind.comp b) (f 0 p)
  | RawUntyped.disj b p => rec_br (UntypedKind.disj b) (f 0 p)
  | RawUntyped.case_pr p l r => rec_br (UntypedKind.case_pr) (f 0 p) (f 0 l) (f 0 r)
  | RawUntyped.imp φ p => rec_br UntypedKind.imp (f 0 φ) (f 0 p)
  | RawUntyped.mp l r => rec_br (UntypedKind.mp) (f 0 l) (f 0 r)
  | RawUntyped.general A p => rec_br UntypedKind.general (f 0 A) (f 1 p)
  | RawUntyped.inst p e => rec_br UntypedKind.inst (f 0 p) (f 0 e)
  | RawUntyped.witness e p => rec_br UntypedKind.witness (f 0 e) (f 0 p)
  | RawUntyped.let_wit p => rec_br UntypedKind.let_wit (f 2 p)
  | RawUntyped.refl e => rec_br UntypedKind.refl (f 0 e)

notation "genVarPropRawUntyped" u "=>" v_case "," prop => match u with
  | RawUntyped.var v => v_case

  | RawUntyped.nats => prop
  | RawUntyped.pi A B => prop
  | RawUntyped.sigma A B => prop
  | RawUntyped.coprod A B => prop
  | RawUntyped.set A φ => prop
  | RawUntyped.assume φ A => prop
  | RawUntyped.intersect A B => prop
  | RawUntyped.union A B => prop

  | RawUntyped.top => prop
  | RawUntyped.bot => prop
  | RawUntyped.and φ ψ => prop
  | RawUntyped.or φ ψ => prop
  | RawUntyped.implies φ ψ => prop
  | RawUntyped.forall_ A φ => prop
  | RawUntyped.exists_ A φ => prop
  | RawUntyped.eq A e e' => prop
  
  | RawUntyped.nat n => prop
  | RawUntyped.lam A e => prop
  | RawUntyped.app s t => prop
  | RawUntyped.pair l r => prop
  | RawUntyped.proj b e => prop
  | RawUntyped.inj b e => prop
  | RawUntyped.case e l r => prop
  | RawUntyped.mkset e p => prop
  | RawUntyped.letset e => prop
  | RawUntyped.lam_pr φ e => prop
  | RawUntyped.app_pr e p => prop
  | RawUntyped.lam_irrel A e => prop
  | RawUntyped.app_irrel l r => prop
  | RawUntyped.repr l r => prop
  | RawUntyped.let_repr e => prop

  | RawUntyped.nil => prop
  | RawUntyped.abort p => prop
  | RawUntyped.conj l r => prop
  | RawUntyped.comp b p => prop
  | RawUntyped.disj b p => prop
  | RawUntyped.case_pr p l r => prop
  | RawUntyped.imp φ p => prop
  | RawUntyped.mp l r => prop
  | RawUntyped.general A p => prop
  | RawUntyped.inst p e => prop
  | RawUntyped.witness e p => prop
  | RawUntyped.let_wit p => prop
  | RawUntyped.refl e => prop

notation "genPropRawUntyped" u "=>" prop => genVarPropRawUntyped u => prop, prop

def RawUntyped.wk (ρ: RawWk) (u: RawUntyped): RawUntyped :=
  genRecRawUntyped u => 
    (λ v => RawUntyped.var (RawWk.var ρ v)),
    (λ m t => wk (RawWk.liftn m ρ) t),
    mk

@[simp] def RawUntyped.wk_comp (ρ: RawWk) (σ: RawWk) (u: RawUntyped):
  wk ρ (wk σ u) = wk (RawWk.comp ρ σ) u :=
  genPropRawUntyped u =>
    by { 
      try simp only [wk, RawWk.liftn, RawWk.var, raw_wk_var_comp];
      try simp only [wk_comp, raw_wk_lift_comp]
    }

@[simp] def RawSubst := Nat -> RawUntyped

def RawSubst.lift (σ: RawSubst): RawSubst
  | 0 => RawUntyped.var 0
  | Nat.succ n => RawUntyped.wk RawWk.wk1 (σ n)

@[simp] def RawSubst.liftn: (l: Nat) -> RawSubst -> RawSubst
  | 0, σ => σ
  | Nat.succ n, σ => lift (liftn n σ)

def RawUntyped.subst (σ: RawSubst) (u: RawUntyped): RawUntyped :=
  genRecRawUntyped u =>
    σ,
    (λ m t => subst (RawSubst.liftn m σ) t),
    mk

def RawSubst.wk (ρ: RawWk): RawSubst :=
  λ n => RawUntyped.var (RawWk.var ρ n)

def RawSubst.wk_wk_lift (ρ: RawWk): RawSubst.lift (wk ρ) = wk (RawWk.lift ρ) := by {
  funext n;
  simp only [lift, wk]
  cases n with
  | zero => rfl
  | succ n => {
    simp only [RawUntyped.wk, RawWk.var]
  }
}

private def RawUntyped.wk_is_wk_inner (ρ: RawWk) (u: RawUntyped):
  subst (RawSubst.wk ρ) u = RawUntyped.wk ρ u :=
    genPropRawUntyped u => by { 
      try simp only [subst, RawSubst.liftn];
      try simp only [RawSubst.wk_wk_lift];
      try simp only [wk_is_wk_inner];
      try simp only [wk, mk, RawWk.liftn];
      try simp only [RawSubst.wk, subst];
    }

@[simp] def RawUntyped.wk_is_wk (ρ: RawWk): subst (RawSubst.wk ρ) = wk ρ := by {
  funext u;
  simp [wk_is_wk_inner]
}

@[simp] def maxList: List Nat -> Nat
  | List.nil => 0
  | List.cons x xs => Nat.max x (maxList xs)

macro_rules
  | `(maxVariadic2 $f $x:term*) => `(maxList [$x,*])

@[simp] def RawUntyped.fv_shifted (n: Nat) (u: RawUntyped): Nat :=
  genRecRawUntyped u => 
    (λ v => v - n + 1), 
    (λ  m t => fv_shifted (n + m) t), 
    maxVariadic2

@[simp] def RawUntyped.fv := RawUntyped.fv_shifted 0

def RawUntyped.subst_fv (u: RawUntyped):
  (m n: Nat) ->
  (σ: RawSubst) ->
  ((l: Nat) -> l < n -> fv (σ l) ≤ m) ->
  fv u ≤ n ->
  fv (subst σ u) ≤ m := by {
  induction u with
  | var => {
    intros m n σ H Hu;
    simp only [subst];
    apply H;
    apply Hu
  }
  | nats => {
    intros;
    apply Nat.zero_le;
  }
  | pi => {
    simp;
    sorry
  }
  | _ => sorry
}

structure Untyped (n: Nat) := (val: RawUntyped) (p: RawUntyped.fv val ≤ n)

structure Subst (m n: Nat) := (val: RawSubst) (p: (v: Nat) -> v < n -> RawUntyped.fv (val v) ≤ m)

def Untyped.subst (σ: Subst m n): Untyped n -> Untyped m
  | Untyped.mk u p => Untyped.mk (RawUntyped.subst σ.val u) (
    RawUntyped.subst_fv u m n σ.val σ.p p
  )

def RawUntyped.wk_fv (u: RawUntyped):
  (m n: Nat) ->
  (ρ: RawWk) ->
  ((l: Nat) -> l < n -> RawWk.var ρ l < m) ->
  fv u ≤ n ->
  fv (wk ρ u) ≤ m := sorry

def Untyped.wk (ρ: Wk m n): Untyped n -> Untyped m
  | Untyped.mk u p => Untyped.mk (RawUntyped.wk ρ.val u) (
    RawUntyped.wk_fv u m n ρ.val ρ.p p
  )