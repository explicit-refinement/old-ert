import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
open Untyped

inductive AnnotSort
  | type
  | prop

inductive Annot
  | sort (s: AnnotSort)
  | expr (s: AnnotSort) (A: Untyped)

def Annot.term := expr AnnotSort.type
def Annot.proof := expr AnnotSort.prop

open Annot
open AnnotSort

instance annotSortCoe: Coe AnnotSort Annot where
  coe := sort
  
@[simp]
def Annot.lift1: Annot -> Annot
  | sort s => sort s
  | expr s A => expr s (Untyped.lift1 A)

@[simp]
def Annot.wk: Annot -> Wk -> Annot
  | sort s, _ => sort s
  | expr s A, ρ => expr s (A.wk ρ)

@[simp]
def Annot.wk1 (A: Annot): Annot := A.wk Wk.wk1

def Annot.wk1_expr_def {A}: (expr s A).wk1 = (expr s A.wk1) := rfl

def Annot.wk1_sort_const {s}:
    (sort s).wk1 = sort s := rfl

@[simp]
def Annot.subst: Annot -> Subst -> Annot
  | sort s, _ => sort s
  | expr s A, σ => expr s (A.subst σ)

def Annot.subst_sort_const {s σ}:
    (sort s).subst σ = sort s := rfl

@[simp]
def Annot.wk_composes: {A: Annot} -> (A.wk ρ).wk σ = A.wk (σ.comp ρ)
  | sort _ => rfl
  | expr _ _ => by simp

@[simp]
def Annot.wk_wk1: {A: Annot} -> (A.wk Wk.wk1) = A.wk1
  | sort _ => rfl
  | expr _ _ => rfl

@[simp]
def Annot.wk_id {A: Annot}: A.wk Wk.id = A := by {
  cases A; repeat simp
}

inductive HypKind
  | val (s: AnnotSort) -- Computational/Logical
  | gst -- Refinement

inductive HypKind.is_wk: HypKind -> HypKind -> Prop
  | refl {k}: is_wk k k
  | gst: is_wk gst (val type)

inductive HypKind.regular: HypKind -> AnnotSort -> Prop
  | val {s}: regular (val s) s
  | gst: regular gst type

@[simp]
def HypKind.upgrade: HypKind -> HypKind
  | val s => val s
  | gst => val type

@[simp]
def HypKind.downgrade: HypKind -> HypKind
  | val prop => val prop
  | val type => gst
  | gst => gst

@[simp]
def HypKind.downgrade_wk {k k': HypKind}:
  k.is_wk k'.upgrade -> k.downgrade.is_wk k' := by {
    cases k with
    | val s =>
      cases k' with
      | val s' =>
        intro H;
        cases H;
        cases s <;> constructor
      | gst =>
        intro H;
        cases H;
        constructor
    | gst =>
      cases k' with
      | val s' =>
        intro H;
        cases H;
        constructor
      | gst => intro H; constructor
  }

def HypKind.upgrade_is_wk: {k: HypKind} -> k.is_wk k.upgrade
  | val type => is_wk.refl
  | val prop => is_wk.refl
  | gst => is_wk.gst

@[simp]
def HypKind.annot: HypKind -> AnnotSort
  | val s => s
  | gst => type


@[simp]
def HypKind.annot_downgrade: {k: HypKind} -> k.downgrade.annot = k.annot
  | val type => rfl
  | val prop => rfl
  | gst => rfl

@[simp]
def HypKind.val_annot: (val s).annot = s := rfl

def HypKind.annot_wk_eq {k k': HypKind}: k.is_wk k' -> k.annot = k'.annot
  := by {
    intro H;
    cases H <;> rfl
  }


def HypKind.annot_is_wk {k: HypKind}: k.is_wk (val k.annot)
  := by {
    cases k <;> simp <;> constructor
  }

def HypKind.annot_other_is_wk {k k': HypKind}: 
  k.is_wk k' -> k'.is_wk (val k.annot)
  := by {
    intro H;
    cases H with
    | refl => exact annot_is_wk
    | gst => exact is_wk.refl
  }

@[simp]
theorem HypKind.upgrade_idem: upgrade (upgrade h) = upgrade h := by {
  cases h; repeat rfl
}

theorem HypKind.upgrade_regular {s} {h: HypKind} (p: h.regular s): 
  h.upgrade.regular s := by {
    cases s <;> cases h <;> cases p <;> constructor
  }

structure Hyp := (ty: Untyped) (kind: HypKind)

@[simp]
def Hyp.wk (H: Hyp) (ρ: Wk) := Hyp.mk (H.ty.wk ρ) H.kind

@[simp]
def Hyp.wk_def {A k ρ}: (Hyp.mk A k).wk ρ = Hyp.mk (A.wk ρ) k := rfl

@[simp]
def Hyp.wkn (H: Hyp) (n: Nat) := Hyp.mk (H.ty.wkn n) H.kind

@[simp]
def Hyp.subst (H: Hyp) (σ: Subst) := Hyp.mk (H.ty.subst σ) H.kind

@[simp]
def Hyp.annot (H: Hyp): Annot := Annot.expr H.kind.annot H.ty

theorem Hyp.wk_components:
  Hyp.wk (Hyp.mk A h) ρ = Hyp.mk (A.wk ρ) h := rfl

theorem Hyp.subst_components:
  Hyp.subst (Hyp.mk A h) σ = Hyp.mk (A.subst σ) h := rfl

@[simp]
def Hyp.upgrade (H: Hyp) := Hyp.mk H.ty H.kind.upgrade

@[simp]
theorem Hyp.upgrade_idem: upgrade (upgrade h) = upgrade h := by {
  simp only [upgrade, HypKind.upgrade_idem]
}

@[simp]
theorem Hyp.upgrade_wk_commute {h: Hyp}: 
  upgrade (h.wk ρ) = h.upgrade.wk ρ := by simp

def Hyp.val (A: Untyped) (s: AnnotSort) := Hyp.mk A (HypKind.val s)
def Hyp.gst (A: Untyped) := Hyp.mk A HypKind.gst

def Context := List Hyp

@[simp]
def Context.upgrade: Context -> Context
  | [] => []
  | h::hs => (h.upgrade)::(upgrade hs)

@[simp]
def Context.upgrade_length_is_length {Γ: Context}: Γ.upgrade.length = Γ.length := by {
  induction Γ with
  | nil => rfl
  | cons H Γ I => simp [I] 
}

@[simp]
theorem Context.upgrade_idem: upgrade (upgrade Γ) = upgrade Γ := by {
  induction Γ with
  | nil => rfl
  | cons A Γ I => 
    simp only [upgrade, Hyp.upgrade_idem]; 
    simp [I]
}

open Untyped

def Untyped.arrow (A B: Untyped) := pi A (wk1 B)

def constAnnot: UntypedKind [] -> Annot
  | UntypedKind.nats => type
  | UntypedKind.top => prop
  | UntypedKind.bot => prop
  | UntypedKind.zero => term nats
  | UntypedKind.succ => term (arrow nats nats)
  | UntypedKind.nil => proof top

inductive HasVar: Context -> Untyped -> HypKind -> Nat -> Prop
  | var0 {Γ: Context} {A: Untyped} {k k': HypKind}:
    k'.is_wk k -> HasVar ((Hyp.mk A k)::Γ) A.wk1 k' 0
  | var_succ {Γ: Context} {A: Untyped} {k: HypKind} {H: Hyp} {n: Nat}:
    HasVar Γ A k n -> HasVar (H::Γ) A.wk1 k (n + 1)

theorem HasVar.fv (H: HasVar Γ A s n): n < Γ.length := by {
  induction H with
  | var0 =>
    apply Nat.succ_le_succ
    apply Nat.zero_le
  | var_succ =>
    simp only [List.length]
    apply Nat.succ_le_succ
    assumption
}

-- Notes:
-- - Automation seems to work even when target types are the same, e.g. swapping general for lam_irrel. This bodes well for the shadow-universe strategy
--   This is before regularity, though; since having the RHS of assume be a prop doesn't seem to break things either.
inductive HasType: Context -> Untyped -> Annot -> Prop
  -- Variables
  | var {Γ: Context} {A: Untyped} {s: AnnotSort} {n: Nat}:
    HasType Γ A (sort s) ->
    HasVar Γ A (HypKind.val s) n ->
    HasType Γ (var n) (expr s A)

  -- Constants
  | nats {Γ}: HasType Γ nats type
  | top {Γ}: HasType Γ top prop
  | bot {Γ}: HasType Γ bot prop
  | zero {Γ}: HasType Γ zero (term nats)
  | succ {Γ}: HasType Γ succ (term (arrow nats nats))
  | nil {Γ}: HasType Γ nil (proof top)

  -- Types
  | pi {Γ: Context} {A B: Untyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType Γ (pi A B) type
  | sigma {Γ: Context} {A B: Untyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType Γ (sigma A B) type
  | coprod {Γ: Context} {A B: Untyped}:
    HasType Γ A type -> HasType Γ B type ->
    HasType Γ (coprod A B) type
  | set {Γ: Context} {A B: Untyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B prop ->
    HasType Γ (set A B) type
  | assume {Γ: Context} {φ A: Untyped}:
    HasType Γ φ prop -> 
    HasType ((Hyp.mk φ (HypKind.val prop))::Γ) A type ->
    HasType Γ (assume φ A) type
  | intersect {Γ: Context} {A B: Untyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B prop ->
    HasType Γ (intersect A B) type
  | union {Γ: Context} {A B: Untyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B prop ->
    HasType Γ (union A B) type
  
  -- Propositions
  | and {Γ: Context} {φ ψ: Untyped}:
    HasType Γ φ prop -> HasType Γ ψ prop ->
    HasType Γ (and φ ψ) prop
  | or {Γ: Context} {φ ψ: Untyped}:
    HasType Γ φ prop -> HasType Γ ψ prop ->
    HasType Γ (or φ ψ) prop
  | implies {Γ: Context} {φ ψ: Untyped}:
    HasType Γ φ prop -> 
    HasType ((Hyp.mk φ (HypKind.val prop))::Γ) ψ prop ->
    HasType Γ (implies φ ψ) prop
  | forall_ {Γ: Context} {A φ: Untyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType Γ (forall_ A φ) type
  | exists_ {Γ: Context} {A φ: Untyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType Γ (exists_ A φ) type
  | eq {Γ: Context} {A l r: Untyped}:
    HasType Γ A type -> 
    HasType Γ.upgrade l (term A) -> HasType Γ.upgrade r (term A) ->
    HasType Γ (eq A l r) prop

  -- Basic term formers
  | lam {Γ: Context} {A s B: Untyped}:
    HasType ((Hyp.mk A (HypKind.val type))::Γ) s (term B) ->
    HasType Γ A type ->
    HasType Γ (lam A s) (term (pi A B))
  | app {Γ: Context} {A B l r: Untyped}:
    HasType Γ l (term (pi A B)) -> HasType Γ r (term A) ->
    HasType Γ (app l r) (term (B.subst0 l))
  | pair {Γ: Context} {A B l r: Untyped}:
    HasType Γ l (term A) -> HasType Γ r (term (B.subst0 l)) ->
    HasType Γ (pair l r) (term (sigma A B))
  | let_pair {Γ: Context} {A B C e e': Untyped} {k: AnnotSort}:
    HasType Γ e (term (sigma A B)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType ((Hyp.mk (sigma A B) (HypKind.val type))::Γ) C k ->
    HasType 
    ((Hyp.mk B (HypKind.val type))::(Hyp.mk A (HypKind.val type))::Γ) 
    e' (term ((C.wknth 1).alpha0 (pair (var 1) (var 0)))) ->
    HasType Γ (let_pair e e') (expr k (C.subst0 e))
  | inj_l {Γ: Context} {A B e: Untyped}:
    HasType Γ e (term A) -> HasType Γ B type ->
    HasType Γ (inj false e) (term (coprod A B))
  | inj_r {Γ: Context} {A B e: Untyped}:
    HasType Γ e (term B) -> HasType Γ A type ->
    HasType Γ (inj true e) (term (coprod A B))
  | case {Γ: Context} {A B C e l r: Untyped} {k: AnnotSort}:
    HasType Γ e (term (coprod A B)) ->
    HasType Γ A type ->
    HasType Γ B type ->
    HasType ((Hyp.mk (coprod A B) (HypKind.val type))::Γ) C k ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) l (term (C.alpha0 (inj false (var 0)))) ->
    HasType ((Hyp.mk B (HypKind.val type))::Γ) r (term (C.alpha0 (inj true (var 0)))) ->
    HasType Γ (case C e l r) (expr k (C.subst0 e))
  | elem {Γ: Context} {A φ l r: Untyped}:
    HasType Γ l (term A) -> HasType Γ r (proof (φ.subst0 l)) ->
    HasType Γ (elem l r) (term (set A φ))
  | let_set {Γ: Context} {A φ C e e': Untyped} {k: AnnotSort}:
    HasType Γ e (term (set A φ)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType ((Hyp.mk (set A φ) (HypKind.val type))::Γ) C k ->
    HasType 
    ((Hyp.mk φ (HypKind.val prop))::(Hyp.mk A (HypKind.val type))::Γ) 
    e' (term ((C.wknth 1).alpha0 (pair (var 1) (var 0)))) ->
    HasType Γ (let_set e e') (expr k (C.subst0 e))
  | lam_pr {Γ: Context} {φ s A: Untyped}:
    HasType Γ φ prop ->
    HasType ((Hyp.mk φ (HypKind.val prop))::Γ) s (term A) ->
    HasType Γ (lam_pr φ s) (term (assume φ A))
  | app_pr {Γ: Context} {φ A l r: Untyped}:
    HasType Γ l (term (assume φ A)) -> HasType Γ.upgrade r (proof φ) ->
    HasType Γ (app_pr l r) (term (A.subst0 l))
  | lam_irrel {Γ: Context} {A s B: Untyped}:
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) s (term B) ->
    HasType Γ (lam_irrel A s) (term (intersect A B))
  | app_irrel {Γ: Context} {A B l r: Untyped}:
    HasType Γ l (term (intersect A B)) -> HasType Γ.upgrade r (term A) ->
    HasType Γ (app_irrel l r) (term (B.subst0 l))
  | repr {Γ: Context} {A B l r: Untyped}:
    HasType Γ l (term A) -> HasType Γ r (term (B.subst0 l)) ->
    HasType Γ (repr l r) (term (union A B))
  -- let_repr

  -- Basic proof formers
  | abort {Γ: Context} {A: Annot} {p: Untyped}:
    HasType Γ p (proof bot) ->
    HasType Γ (abort p) A
  | conj {Γ: Context} {A B l r: Untyped}:
    HasType Γ l (proof A) -> HasType Γ r (proof B) ->
    HasType Γ (conj l r) (proof (and A B))
  | comp_l {Γ: Context} {A B e: Untyped}:
    HasType Γ e (proof (and A B)) ->
    HasType Γ (comp false e) (proof A)
  | comp_r {Γ: Context} {A B e: Untyped}:
    HasType Γ e (proof (and A B)) ->
    HasType Γ (comp true e) (proof B)
  | disj_l {Γ: Context} {A B e: Untyped}:
    HasType Γ e (proof A) ->
    HasType Γ B prop ->
    HasType Γ (disj false e) (proof (or A B))
  | disj_r {Γ: Context} {A B e: Untyped}:
    HasType Γ e (proof B) ->
    HasType Γ A prop ->
    HasType Γ (disj true e) (proof (or A B))
  | case_pr {Γ: Context} {A B C e l r: Untyped}:
    HasType Γ e (proof (or A B)) ->
    HasType Γ A prop ->
    HasType Γ B prop ->
    HasType ((Hyp.mk (or A B) (HypKind.val prop))::Γ) C prop ->
    HasType ((Hyp.mk A (HypKind.val prop))::Γ) l (proof (C.alpha0 (disj false (var 0)))) ->
    HasType ((Hyp.mk B (HypKind.val prop))::Γ) r (proof (C.alpha0 (disj true (var 0)))) ->
    HasType Γ (case_pr C e l r) (term (C.subst0 e))
  | imp {Γ: Context} {φ s ψ: Untyped}:
    HasType Γ φ prop ->
    HasType ((Hyp.mk φ (HypKind.val prop))::Γ) s (proof ψ) ->
    HasType Γ (imp φ s) (proof (implies φ ψ))
  | mp {Γ: Context} {φ ψ l r: Untyped}:
    HasType Γ l (term (implies φ ψ)) -> HasType Γ.upgrade r (proof φ) ->
    HasType Γ (mp l r) (proof (ψ.subst0 l))
  | general {Γ: Context} {A s φ: Untyped}:
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) s (proof φ) ->
    HasType Γ (general A s) (proof (forall_ A φ))
  | inst {Γ: Context} {A φ l r: Untyped}:
    HasType Γ l (proof (forall_ A φ)) -> HasType Γ.upgrade r (term A) ->
    HasType Γ (inst l r) (proof (φ.subst0 l))
  | wit {Γ: Context} {A φ l r: Untyped}:
    HasType Γ l (term A) -> HasType Γ.upgrade r (proof (φ.subst0 l)) ->
    HasType Γ (repr l r) (proof (exists_ A φ))
  --TODO: let_wit
  | refl {Γ: Context} {A a: Untyped}:
    HasType Γ a (term A) -> HasType Γ (refl a) (proof (eq A a a))

  -- Value formers
  --TODO: natrec  

notation Γ "⊢" a ":" A => HasType Γ a A
notation Γ "⊢" a "∈" A => HasType Γ a (term A)
notation Γ "⊢" a "∴" A => HasType Γ a (prop A)

theorem HasType.fv {Γ a A} (P: Γ ⊢ a: A): a.fv ≤ Γ.length := by {
  induction P 
  <;> intros 
  <;> try apply Nat.zero_le -- constants, e.g. nats, nil, zero
  case var =>
    apply HasVar.fv
    assumption
  all_goals (
    simp only [
      Untyped.fv, 
      Nat.max_r_le_split, 
      Nat.le_sub_is_le_add
    ];
    simp only [
      Context.upgrade_length_is_length
    ] at *
    repeat first | apply And.intro | assumption
  )
} 

theorem HasVar.upgrade (p: HasVar Γ A k n): 
  HasVar Γ.upgrade A (HypKind.val k.annot) n := by {
  induction p with
  | var0 H => 
    rename_i k k';
    simp only [Context.upgrade, Hyp.upgrade]
    apply var0
    cases H;
    cases k <;> constructor
    constructor
  | var_succ => apply var_succ; assumption
}

theorem HasVar.wk_sort {k k'} (Hk: k.is_wk k') (p: HasVar Γ A k' n): 
  HasVar Γ A k n := by {
  induction p with
  | var0 H => 
    rename_i k k';
    simp only [Context.upgrade, Hyp.upgrade]
    apply var0
    cases H;
    apply Hk
    cases Hk
    constructor
  | var_succ H I => 
    apply var_succ
    apply I
    apply Hk
}

theorem HasVar.downgrade_helper: {Γ Γ': Context} -> Γ' = Γ.upgrade -> 
  ∀ {n A k}, HasVar Γ' A k n -> HasVar Γ A k.downgrade n := by {
  intro Γ;
  induction Γ with
  | nil => 
    intro Γ' HΓ';
    rw [HΓ']
    intro n a K H;
    cases H
  | cons H Γ I =>
    intro Γ' HΓ';
    simp only [Context.upgrade, HΓ']
    intro n a K H;
    cases H with
    | var0 =>
      apply var0
      apply HypKind.downgrade_wk
      assumption
    | var_succ => 
      apply var_succ
      apply I rfl
      assumption
  }

theorem HasVar.downgrade {Γ n A k}: 
  HasVar Γ.upgrade A k n -> HasVar Γ A k.downgrade n :=
  downgrade_helper rfl

theorem HasVar.upgrade_val (p: HasVar Γ A (HypKind.val s) n): 
  HasVar Γ.upgrade A (HypKind.val s) n := HasVar.upgrade p

theorem HasType.upgrade (p: Γ ⊢ a: A): Γ.upgrade ⊢ a: A := by {
  induction p;
  case var => 
    apply var
    assumption
    apply HasVar.upgrade_val
    assumption
  all_goals { constructor; repeat assumption; }
}

--TODO: define context type, coercion to raw context?

inductive IsCtx: Context -> Prop
  | nil: IsCtx []
  | cons_val {Γ A s}: 
    IsCtx Γ -> (Γ ⊢ A: sort s) 
    -> IsCtx ((Hyp.mk A (HypKind.val s))::Γ)
  | cons_gst {Γ A}: 
    IsCtx Γ -> (Γ ⊢ A: type) -> 
    IsCtx ((Hyp.mk A HypKind.gst)::Γ)

-- theorem HasType.ctx_regular (p: Γ ⊢ a: A): IsCtx Γ := by {
--   induction p <;> first
--   | assumption
--   | constructor <;> assumption
-- }

def IsHyp (Γ: Context) (H: Hyp): Prop := Γ ⊢ H.ty: sort H.kind.annot

-- def HasType.wk1
--   (Ha: HasType Γ a A) (H: Hyp) (HH: IsHyp Γ H):
--   HasType (H::Γ) a.wk1 A.wk1 := by { 
--     cases HH <;>
--     apply wk1_inner <;>
--     first | assumption | constructor
--   }

inductive WkCtx: Wk -> Context -> Context -> Type
  | id: WkCtx Wk.id Γ Γ
  | step {ρ Γ Δ H}: WkCtx ρ Γ Δ -> WkCtx ρ.step (H::Γ) Δ 
  | lift {ρ Γ Δ k} {A: Untyped}: WkCtx ρ Γ Δ 
    -> WkCtx ρ.lift ((Hyp.mk (A.wk ρ) k)::Γ) ((Hyp.mk A k)::Δ)

def WkCtx.lift_loose: 
  ρ' = ρ.lift -> A' = A.wk ρ -> WkCtx ρ Γ Δ -> WkCtx ρ' ((Hyp.mk A' k)::Γ) ((Hyp.mk A k)::Δ) := by {
    intro Hρ HA R;
    rw [Hρ, HA];
    exact WkCtx.lift R
  }

def WkCtx.wk1 {Γ H}: WkCtx Wk.wk1 (H::Γ) Γ := WkCtx.step WkCtx.id

theorem WkCtx.upgrade: WkCtx ρ Γ Δ 
  -> WkCtx ρ Γ.upgrade Δ.upgrade := by {
  intro R;
  induction R with
  | id => exact id
  | step R => apply step; assumption
  | lift R =>
    simp only [Context.upgrade, Hyp.upgrade_wk_commute]
    apply lift <;> assumption
}

theorem HasVar.wk:
  (ρ: Wk) -> {Γ Δ: Context} -> (Hs: WkCtx ρ Γ Δ) ->
  {n: Nat} -> {A: Untyped} -> {s: HypKind} ->
  HasVar Δ A s n -> HasVar Γ (A.wk ρ) s (ρ.var n) 
  := by {
    intros ρ;
    induction ρ <;> intro Γ Δ R <;> cases R;
    case id => 
      intros n A s H;
      simp [H] 
    case step ρ I Γ H R =>
      intros n A s HΔ;
      simp only [Untyped.step_wk1]
      exact var_succ (I R HΔ)
    case lift ρ I Γ Δ k A R =>
      intros n A s HΔ;
      cases HΔ with
      | var0 =>
        simp only [
          Wk.lift,
          Untyped.wk_composes,
          Wk.var, Untyped.lift_wk1
        ]
        apply var0
        assumption
      | var_succ =>
        simp only [
          Wk.lift,
          Untyped.wk_composes,
          Wk.var, Nat.add, Untyped.lift_wk1
        ]
        apply var_succ
        apply I
        apply R
        assumption
  } 

theorem HasType.wk {Δ a A} (HΔ: Δ ⊢ a: A):
  {ρ: Wk} -> {Γ: Context} -> WkCtx ρ Γ Δ ->
  (Γ ⊢ (a.wk ρ): (A.wk ρ)) := by {
    induction HΔ;
    case var I =>
      intros
      apply var
      apply I
      assumption
      apply HasVar.wk
      repeat assumption

    all_goals (
      intros ρ Γ R
      simp only [
        Untyped.wk, Annot.wk, term, proof, Untyped.subst0_wk,
        Untyped.wk1
      ] at *
      constructor <;> 
      rename_i' I5 I4 I3 I2 I1 I0 <;> 
      (try rw [Untyped.alpha00_wk_comm (by simp)]) <;>
      (try rw [Untyped.let_bin_ty_alpha_wk]) <;>
      (first | apply I0 | apply I1 | apply I2 | apply I3 | apply I4 | apply I5) <;> 
      simp only [<-Hyp.wk_components] <;> 
      first 
      | exact R
      | (exact R.upgrade)
      | {
        repeat (apply WkCtx.lift_loose rfl; rfl)
        exact R
      }
    )
  }

--TODO: basic weakening helpers

def HasType.wk1 {H} (Ha: Γ ⊢ a: A): (H::Γ) ⊢ a.wk1: A.wk1 
:= wk Ha WkCtx.wk1

def HasType.wk1_sort {H} (Ha: Γ ⊢ a: sort s): (H::Γ) ⊢ a.wk1: sort s 
:= wk Ha WkCtx.wk1

-- def HasType.wk_val (Ha: HasType Γ a A) (HB: HasType Γ B (sort s))
--   : HasType ((Hyp.val B s)::Γ) a.wk1 A.wk1
--   := wk1_inner Ha HB HypKind.regular.val

-- def HasType.wk_gst (Ha: HasType Γ a A) (HB: HasType Γ B type)
--   : HasType ((Hyp.gst B)::Γ) a.wk1 A.wk1
--   := wk1_inner Ha HB HypKind.regular.gst

--TODO: basic examples

-- -- Simple examples

-- def HasType.arrow (HA: Γ ⊢ A: type) (HB: Γ ⊢ B: type)
--   : Γ ⊢ (arrow A B): type 
--   := pi HA (wk_sort HB HA)

-- def HasType.lam_id (HA: Γ ⊢ A: type)
--   : Γ ⊢ (Untyped.lam A (var 0)) ∈ Untyped.arrow A A
--   := lam HA (var0 HA)

-- def HasType.const_lam 
--   (HA: Γ ⊢ A: type) (HB: Γ ⊢ B: type) (Hb: Γ ⊢ b ∈ B)
--   : HasType Γ (Untyped.lam A b.wk1) (term (Untyped.arrow A B))
--   := lam HA (wk_expr Hb HA)

--TODO: substitution lemma

--TODO: fill in with proper definition
def SubstCtx (σ: Subst) (Γ Δ: Context): Prop :=  
  ∀{n A k}, HasVar Δ A k n -> Γ ⊢ σ n: expr k.annot (A.subst σ)

theorem SubstCtx.var {σ: Subst} {Γ Δ: Context} (S: SubstCtx σ Γ Δ):
  ∀{n A}, (Δ ⊢ var n: A) -> (Γ ⊢ σ n: A.subst σ) :=
  λHΔ => match HΔ with
         | HasType.var _ H => S H

theorem SubstCtx.lift_primitive 
  {σ: Subst} {Γ Δ: Context} {A: Untyped} {k: HypKind} {s: AnnotSort}:
  SubstCtx σ Γ Δ ->
  k.is_wk (HypKind.val s) ->
  IsHyp Γ (Hyp.mk (A.subst σ) (HypKind.val s)) ->
  SubstCtx σ.lift ((Hyp.mk (A.subst σ) (HypKind.val s))::Γ) ((Hyp.mk A k)::Δ) := by {
    intro S Hk HH n A k HΔ;
    cases n with
    | zero =>
      simp only [Annot.subst]
      cases HΔ with
      | var0 Hkk' =>
        rename_i k'
        simp only [Subst.lift_wk]
        simp only [Subst.lift]
        apply HasType.var
        case a =>
          apply HasType.wk1_sort
          rw [HypKind.annot_wk_eq Hkk']
          rw [HypKind.annot_wk_eq Hk]
          apply HH
        case a =>
          apply HasVar.var0
          cases Hk <;> 
          cases Hkk' <;>
          (try cases s) <;> 
          exact HypKind.is_wk.refl

    | succ n =>
      simp only [Annot.subst, Hyp.annot]
      cases HΔ;
      rename_i A n H
      simp only [Subst.lift_wk, Nat.add]
      simp only [Subst.lift, Subst.wk1]
      rw [<-Annot.wk1_expr_def]
      exact HasType.wk1 (S H)
  }

theorem SubstCtx.lift_loose
  {σ σ': Subst} {Γ Δ: Context} {A A': Untyped} {k: HypKind} {s: AnnotSort}:
  σ' = σ.lift ->
  A' = A.subst σ ->
  SubstCtx σ Γ Δ ->
  k.is_wk (HypKind.val s) ->
  IsHyp Γ (Hyp.mk A' (HypKind.val s)) ->
  SubstCtx σ' ((Hyp.mk A' (HypKind.val s))::Γ) ((Hyp.mk A k)::Δ) := by {
    intro Hσ HA;
    rw [Hσ, HA];
    apply lift_primitive
  }

theorem SubstCtx.upgrade (S: SubstCtx ρ Γ Δ): SubstCtx ρ Γ.upgrade Δ.upgrade 
:= by {
  intro n A k H;
  apply HasType.upgrade;
  rw [<-HypKind.annot_downgrade]
  apply S;
  exact HasVar.downgrade H
}

theorem eta_helper {σ: Subst}: (λn => σ n) = σ := by simp

theorem HasType.subst {Δ a A} (HΔ: Δ ⊢ a: A):
  {σ: Subst} -> {Γ: Context} -> SubstCtx σ Γ Δ ->
  (Γ ⊢ (a.subst σ): (A.subst σ)) := by {
    induction HΔ;

    case var I =>
      intros σ Γ S
      apply S.var
      apply var <;> assumption

    -- case let_pair =>
    --   intros σ Γ S
    --   simp only [
    --     Untyped.subst, Annot.subst, term, proof, Untyped.subst0_subst
    --   ] at *
    --   constructor <;>
    --   rename_i' I5 I4 I3 I2 I1 I0;
    --   first 
    --     | apply I0 | apply I1 | apply I2 | apply I3 | apply I4 | apply I5
    --     | exact I4 S
    --   apply I3
    --   exact S
    --   apply I2
    --   apply SubstCtx.lift_primitive S (by constructor <;> simp only [HypKind, Hyp.subst])
    --   apply I3
    --   exact S
    --   apply I1
    --   apply SubstCtx.lift_primitive S (by constructor <;> simp only [HypKind, Hyp.subst])
    --   constructor
    --   apply I3
    --   exact S
    --   apply I2
    --   apply SubstCtx.lift_primitive S (by constructor <;> simp only [HypKind, Hyp.subst])
    --   apply I3 
    --   exact S
    --   rw [Untyped.let_bin_ty_alpha]
    --   apply I0
    --   simp only [Subst.liftn]
    --   repeat any_goals (
    --       apply SubstCtx.lift_primitive _ (by constructor <;> simp only [HypKind, Hyp.subst]) <;>
    --       try exact S
    --   )
    --   apply I2
    --   repeat any_goals (
    --       apply SubstCtx.lift_primitive _ (by constructor <;> simp only [HypKind, Hyp.subst]) <;>
    --       try exact S
    --   )
    --   try exact S
    --   apply I3
    --   exact S
    --   apply I3 
    --   exact S

    all_goals (
      intros σ Γ S
      simp only [
        Untyped.subst, Annot.subst, term, proof, Untyped.subst0_subst
      ] at *
      constructor <;>
      rename_i' I5 I4 I3 I2 I1 I0 <;> repeat (
        try constructor
        (try rw [Untyped.alpha00_comm (by simp)])
        (try rw [Untyped.let_bin_ty_alpha])
        first 
        | apply I0 | apply I1 | apply I2 | apply I3 | apply I4 | apply I5
        | exact I4 S
        first
        | exact S
        | exact SubstCtx.upgrade S
        | repeat any_goals (
          apply SubstCtx.lift_primitive _ (by constructor <;> simp only [HypKind, Hyp.subst]) <;>
          try exact S
        )
      )
    )
  }

--TODO: basic substitution helpers, in particular for subst0. See HasType.regular

inductive Annot.regular: Annot -> Context -> Prop
  | sort {Γ s}: regular (sort s) Γ
  | expr {Γ s A}: (Γ ⊢ A: sort s) -> regular (expr s A) Γ

def Annot.regular_expr: regular (expr s A) Γ -> (Γ ⊢ A: sort s)
  | Annot.regular.expr Hr => Hr

-- theorem HasType.regular (p: Γ ⊢ a: A): A.regular Γ := by {
--   induction p;

--   all_goals try exact Annot.regular.sort

--   case lam =>
--     constructor; constructor <;>
--     first | assumption | { apply Annot.regular_expr; assumption }

--   --TODO: general tactic for app requires substitution lemma for subst0

--   repeat sorry
-- }

-- theorem HasType.term_regular (p: HasType Γ a (term A)): HasType Γ A type 
--   := by {
--     let H := regular p;
--     cases H with
--     | expr H => exact H
--   }

-- theorem HasType.proof_regular (p: HasType Γ a (proof A)): HasType Γ A prop 
--   := by {
--     let H := regular p;
--     cases H with
--     | expr H => exact H
--   }