import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
import LogicalRefinement.Typed.Context
open Untyped
open Annot
open AnnotSort


inductive HasVar: Context -> Untyped -> HypKind -> Nat -> Prop
  | var0 {Γ: Context} {A: Untyped} {k k': HypKind}:
    k'.is_sub k -> HasVar ((Hyp.mk A k)::Γ) A.wk1 k' 0
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

theorem HasVar.sub (HΓ: HasVar Γ A s n): Γ.is_sub Δ -> HasVar Δ A s n := by {
  revert Γ n s A Δ;
  intro Γ;
  induction Γ with
  | nil => intro Δ A s n H; cases H
  | cons H Γ I =>
    intro Δ A s n HΓ HΔ;
    cases HΔ with
    | @cons Γ Δ _ H HΓΔ HH =>  
      cases HH;
      cases HΓ with
      | var0 =>
        apply var0
        apply HypKind.is_sub.trans <;> assumption
      | var_succ =>
        apply var_succ
        apply I <;> assumption
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
  -- Change nil to non-list things
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
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType Γ (intersect A B) type
  | union {Γ: Context} {A B: Untyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType Γ (union A B) type
  
  -- Propositions
  | and {Γ: Context} {φ ψ: Untyped}:
    HasType Γ φ prop -> HasType Γ ψ prop ->
    HasType Γ (and φ ψ) prop
  | or {Γ: Context} {φ ψ: Untyped}:
    HasType Γ φ prop -> HasType Γ ψ prop ->
    HasType Γ (or φ ψ) prop
  | dimplies {Γ: Context} {φ ψ: Untyped}:
    HasType Γ φ prop -> 
    HasType ((Hyp.mk φ (HypKind.val prop))::Γ) ψ prop ->
    HasType Γ (dimplies φ ψ) prop
  | forall_ {Γ: Context} {A φ: Untyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType Γ (forall_ A φ) prop
  | exists_ {Γ: Context} {A φ: Untyped}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType Γ (exists_ A φ) prop
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
    e' (expr k ((C.wknth 1).alpha0 (pair (var 1) (var 0)))) ->
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
    e' (expr k ((C.wknth 1).alpha0 (elem (var 1) (var 0)))) ->
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
  | let_repr {Γ: Context} {A B C e e': Untyped} {k: AnnotSort}:
    HasType Γ e (term (union A B)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A HypKind.gst)::Γ) B type ->
    HasType ((Hyp.mk (union A B) (HypKind.val type))::Γ) C k ->
    HasType 
    ((Hyp.mk B (HypKind.val type))::(Hyp.mk A HypKind.gst)::Γ) 
    e' (term ((C.wknth 1).alpha0 (repr (var 1) (var 0)))) ->
    HasType Γ (let_repr e e') (expr k (C.subst0 e))

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
    HasType Γ (imp φ s) (proof (dimplies φ ψ))
  | mp {Γ: Context} {φ ψ l r: Untyped}:
    HasType Γ l (term (dimplies φ ψ)) -> HasType Γ.upgrade r (proof φ) ->
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
  | let_wit {Γ: Context} {A φ C e e': Untyped} {k: AnnotSort}:
    HasType Γ e (term (exists_ A φ)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A HypKind.gst)::Γ) φ prop ->
    HasType ((Hyp.mk (exists_ A φ) (HypKind.val prop))::Γ) C k ->
    HasType 
    ((Hyp.mk φ (HypKind.val prop))::(Hyp.mk A HypKind.gst)::Γ) 
    e' (term ((C.wknth 1).alpha0 (wit (var 1) (var 0)))) ->
    HasType Γ (let_wit e e') (expr k (C.subst0 e))

  -- Theory of equality
  | refl {Γ: Context} {A a: Untyped}:
    HasType Γ a (term A) -> HasType Γ (refl a) (proof (eq A a a))
  | sym {Γ: Context} {A: Untyped}:
    HasType Γ A type 
    -> HasType Γ (sym A) (proof (sym_ty A))
  | trans {Γ: Context} {A: Untyped}:
    HasType Γ A type 
    -> HasType Γ (trans A) (proof (trans_ty A))
  | cong {Γ: Context} {A P p x y: Untyped}:
    HasType ((Hyp.mk A (HypKind.val type))::Γ) P prop -> 
    HasType Γ A type ->
    HasType Γ p (proof (eq A x y)) ->
    HasType Γ (cong p P) (proof (implies (P.subst0 x) (P.subst0 y)))

  -- Natural numbers
  | natrec {Γ: Context} {C e z s: Untyped} {k: AnnotSort}:
    HasType ((Hyp.mk nats HypKind.gst)::Γ) C k ->
    HasType Γ e (term nats) ->
    HasType Γ z (term (C.subst0 zero)) ->
    HasType ((Hyp.mk C (HypKind.val k))::(Hyp.mk nats HypKind.gst)::Γ) s
    --TODO: this is just C.wk1...
    (term ((C.wknth 1).alpha0 (var 1))) ->
    HasType Γ (natrec C e z s) (expr k (C.subst0 e))

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

theorem HasVar.wk_sort {k k'} (Hk: k.is_sub k') (p: HasVar Γ A k' n): 
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

theorem HasVar.upgrade_upgraded:
  k.is_sub k' -> HasVar Γ A k n -> HasVar Γ.upgrade A k' n := by {
  intro Hk HΓ;
  let Hv := upgrade HΓ;
  cases k <;> cases Hk <;> try exact Hv
  exact HasVar.wk_sort HypKind.is_sub.gst Hv
}

theorem HasVar.upgrade_downgraded:
  HasVar Γ A k.downgrade n -> HasVar Γ.upgrade A k n 
  := upgrade_upgraded HypKind.downgrade_is_sub

theorem HasType.sub (p: Γ ⊢ a: A): ∀{Δ}, Γ.is_sub Δ -> Δ ⊢ a: A := by {
  induction p;
  case var I =>
    intro Δ HΓΔ;
    apply var
    apply I
    assumption
    apply HasVar.sub <;> assumption

  all_goals (
    rename_i' I5 I4 I3 I2 I1 I0;
    intro Δ H;
    constructor <;> repeat (
      (first | apply I0 | apply I1 | apply I2 | apply I3 | apply I4 | apply I5) <;>
      repeat first | apply Context.is_sub.upgrade_bin | assumption | constructor
    )
  )
}

theorem HasType.upgrade (p: Γ ⊢ a: A): Γ.upgrade ⊢ a: A 
  := HasType.sub p Context.is_sub.upgrade

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