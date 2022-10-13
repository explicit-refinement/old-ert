import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
import LogicalRefinement.Typed.Context
open Term
open Annot
open AnnotSort


inductive HasVar: Context -> Nat -> HypKind -> Term -> Prop
  | zero {Γ: Context} {A: Term} {k: HypKind}:
    HasVar ((Hyp.mk A k)::Γ) 0 k A.wk1 
  | succ {Γ: Context} {A: Term} {k: HypKind} {H: Hyp} {n: Nat}:
    HasVar Γ n k A -> HasVar (H::Γ) (n + 1) k A.wk1

inductive HasVar': Context -> Nat -> HypKind -> Term -> Prop
  | zero {Γ: Context} {A: Term} {k k': HypKind}:
    k'.is_sub k -> HasVar' ((Hyp.mk A k)::Γ) 0 k' A.wk1 
  | succ {Γ: Context} {A: Term} {k: HypKind} {H: Hyp} {n: Nat}:
    HasVar' Γ n k A -> HasVar' (H::Γ) (n + 1) k A.wk1

theorem HasVar.sub' {k k': HypKind} 
  (H: HasVar Γ n k A) 
  (Hk: k'.is_sub k): HasVar' Γ n k' A := by {
  induction H with
  | zero => 
    constructor
    assumption
  | succ _ I => 
    constructor
    exact I Hk
}

theorem HasVar.v 
  (H: HasVar Γ n k A): HasVar' Γ n k A := 
  H.sub' HypKind.is_sub.refl

theorem HasVar'.v 
  (H: HasVar' Γ n (HypKind.val s) A): HasVar Γ n (HypKind.val s) A := 
  by {
    generalize Hk: HypKind.val s = k;
    rw [Hk] at H;
    induction H with
    | zero Hk' =>
      cases Hk;
      cases Hk';
      constructor
    | succ _ I =>
      constructor;
      exact I Hk;
  }

theorem HasVar.v_eq {Γ n s A}:
  HasVar Γ n (HypKind.val s) A = HasVar' Γ n (HypKind.val s) A := 
  propext (Iff.intro HasVar.v HasVar'.v)


theorem HasVar'.e_eq {Γ n k A}:
  HasVar' Γ n k A = ∃k', k.is_sub k' ∧ HasVar Γ n k' A := 
  by {
    apply propext; apply Iff.intro;
    {
      intro Hv';
      induction Hv' with
      | zero Hk' => exact ⟨_, Hk', HasVar.zero⟩
      | succ _ I =>
        have ⟨k', Hk', I⟩ := I;
        exact ⟨k', Hk', I.succ⟩
    }
    {
      intro ⟨k', Hk', Hv⟩;
      exact Hv.sub' Hk'
    }
  }

theorem HasVar.fv (H: HasVar Γ n s A): n < Γ.length := by {
  induction H with
  | zero =>
    apply Nat.succ_le_succ
    apply Nat.zero_le
  | succ =>
    simp only [List.length]
    apply Nat.succ_le_succ
    assumption
}

theorem HasVar'.fv (H: HasVar' Γ n s A): n < Γ.length := by {
  induction H with
  | zero =>
    apply Nat.succ_le_succ
    apply Nat.zero_le
  | succ =>
    simp only [List.length]
    apply Nat.succ_le_succ
    assumption
}

theorem HasVar'.sub (HΓ: HasVar' Γ A s n): 
  Γ.is_sub Δ -> HasVar' Δ A s n := by {
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
      | zero =>
        apply zero
        apply HypKind.is_sub.trans <;> assumption
      | succ =>
        apply succ
        apply I <;> assumption
}

theorem HasVar.sub (HΓ: HasVar Γ A (HypKind.val s) n) (HΓΔ: Γ.is_sub Δ)
: HasVar Δ A (HypKind.val s) n := by {
  simp only [HasVar.v_eq] at *;
  apply HasVar'.sub <;> assumption
}

-- Notes:
-- - Automation seems to work even when target types are the same, e.g. swapping general for lam_irrel. This bodes well for the shadow-universe strategy
--   This is before regularity, though; since having the RHS of assume be a prop doesn't seem to break things either.
inductive HasType: Context -> Term -> Annot -> Prop
  -- Variables
  | var {Γ: Context} {A: Term} {s: AnnotSort} {n: Nat}:
    HasType Γ A (sort s) ->
    HasVar Γ n (HypKind.val s) A ->
    HasType Γ (var n) (expr s A)

  -- Types
  | unit {Γ: Context}: HasType Γ unit type
  | pi {Γ: Context} {A B: Term}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType Γ (pi A B) type
  | sigma {Γ: Context} {A B: Term}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType Γ (sigma A B) type
  | coprod {Γ: Context} {A B: Term}:
    HasType Γ A type -> HasType Γ B type ->
    HasType Γ (coprod A B) type
  | set {Γ: Context} {A B: Term}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B prop ->
    HasType Γ (set A B) type
  | assume {Γ: Context} {φ A: Term}:
    HasType Γ φ prop -> 
    HasType ((Hyp.mk φ (HypKind.val prop))::Γ) A type ->
    HasType Γ (assume φ A) type
  | intersect {Γ: Context} {A B: Term}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType Γ (intersect A B) type
  | union {Γ: Context} {A B: Term}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType Γ (union A B) type
  
  -- Propositions
  | top {Γ}: HasType Γ top prop
  | bot {Γ}: HasType Γ bot prop
  | dand {Γ: Context} {φ ψ: Term}:
    HasType Γ φ prop -> 
    HasType ((Hyp.mk φ (HypKind.val prop))::Γ) ψ prop ->
    HasType Γ (dand φ ψ) prop
  | or {Γ: Context} {φ ψ: Term}:
    HasType Γ φ prop -> HasType Γ ψ prop ->
    HasType Γ (or φ ψ) prop
  | dimplies {Γ: Context} {φ ψ: Term}:
    HasType Γ φ prop -> 
    HasType ((Hyp.mk φ (HypKind.val prop))::Γ) ψ prop ->
    HasType Γ (dimplies φ ψ) prop
  | forall_ {Γ: Context} {A φ: Term}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType Γ (forall_ A φ) prop
  | exists_ {Γ: Context} {A φ: Term}:
    HasType Γ A type -> 
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType Γ (exists_ A φ) prop
  | eq {Γ: Context} {A l r: Term}:
    HasType Γ A type -> 
    HasType Γ.upgrade l (term A) -> HasType Γ.upgrade r (term A) ->
    HasType Γ (eq A l r) prop

  -- Basic term formers
  | nil {Γ}: HasType Γ nil (term unit)
  | lam {Γ: Context} {A s B: Term}:
    HasType ((Hyp.mk A (HypKind.val type))::Γ) s (term B) ->
    HasType Γ A type ->
    HasType Γ (lam A s) (term (pi A B))
  | app {Γ: Context} {A B l r: Term}:
    HasType Γ (pi A B) type ->
    HasType Γ l (term (pi A B)) -> HasType Γ r (term A) ->
    HasType Γ (app (pi A B) l r) (term (B.subst0 r))
  | pair {Γ: Context} {A B l r: Term}:
    HasType Γ (sigma A B) type ->
    HasType Γ l (term A) -> HasType Γ r (term (B.subst0 l)) ->
    HasType Γ (pair l r) (term (sigma A B))
  | let_pair {Γ: Context} {A B C e e': Term}:
    HasType Γ e (term (sigma A B)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType ((Hyp.mk (sigma A B) (HypKind.val type))::Γ) C type ->
    HasType 
    ((Hyp.mk B (HypKind.val type))::(Hyp.mk A (HypKind.val type))::Γ) 
    e' (expr type ((C.wknth 1).alpha0 (pair (var 1) (var 0)))) ->
    HasType Γ (let_pair type (sigma A B) e e') (expr type (C.subst0 e))
  | inj_l {Γ: Context} {A B e: Term}:
    HasType Γ e (term A) -> HasType Γ B type ->
    HasType Γ (inj 0 e) (term (coprod A B))
  | inj_r {Γ: Context} {A B e: Term}:
    HasType Γ e (term B) -> HasType Γ A type ->
    HasType Γ (inj 1 e) (term (coprod A B))
  | case {Γ: Context} {A B C e l r: Term}:
    HasType Γ e (term (coprod A B)) ->
    HasType Γ A type ->
    HasType Γ B type ->
    HasType ((Hyp.mk (coprod A B) (HypKind.val type))::Γ) C type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) l (expr type (C.alpha0 (inj 0 (var 0)))) ->
    HasType ((Hyp.mk B (HypKind.val type))::Γ) r (expr type (C.alpha0 (inj 1 (var 0)))) ->
    HasType Γ (case type (coprod A B) e l r) (expr type (C.subst0 e))
  | elem {Γ: Context} {A φ l r: Term}:
    HasType Γ (set A φ) type ->
    HasType Γ l (term A) -> HasType Γ r (proof (φ.subst0 l)) ->
    HasType Γ (elem l r) (term (set A φ))
  | let_set {Γ: Context} {A φ C e e': Term}:
    HasType Γ e (term (set A φ)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType ((Hyp.mk (set A φ) (HypKind.val type))::Γ) C type ->
    HasType 
    ((Hyp.mk φ (HypKind.val prop))::(Hyp.mk A (HypKind.val type))::Γ) 
    e' (expr type ((C.wknth 1).alpha0 (elem (var 1) (var 0)))) ->
    HasType Γ (let_set type (set A φ) e e') (expr type (C.subst0 e))
  | lam_pr {Γ: Context} {φ s A: Term}:
    HasType Γ φ prop ->
    HasType ((Hyp.mk φ (HypKind.val prop))::Γ) s (term A) ->
    HasType Γ (lam_pr φ s) (term (assume φ A))
  | app_pr {Γ: Context} {φ A l r: Term}:
    HasType Γ (assume φ A) type ->
    HasType Γ l (term (assume φ A)) -> HasType Γ r (proof φ) ->
    HasType Γ (app_pr (assume φ A) l r) (term (A.subst0 r))
  | lam_irrel {Γ: Context} {A s B: Term}:
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.gst))::Γ) s (term B) ->
    HasType Γ (lam_irrel A s) (term (intersect A B))
  | app_irrel {Γ: Context} {A B l r: Term}:
    HasType Γ (intersect A B) type ->
    HasType Γ l (term (intersect A B)) -> HasType Γ.upgrade r (term A) ->
    HasType Γ (app_irrel (intersect A B) l r) (term (B.subst0 r))
  | repr {Γ: Context} {A B l r: Term}:
    HasType Γ (union A B) type ->
    HasType Γ.upgrade l (term A) -> HasType Γ r (term (B.subst0 l)) ->
    HasType Γ (repr l r) (term (union A B))
  | let_repr {Γ: Context} {A B C e e': Term}:
    HasType Γ e (term (union A B)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A HypKind.gst)::Γ) B type ->
    HasType ((Hyp.mk (union A B) (HypKind.val type))::Γ) C type ->
    HasType 
    ((Hyp.mk B (HypKind.val type))::(Hyp.mk A HypKind.gst)::Γ) 
    e' (expr type ((C.wknth 1).alpha0 (repr (var 1) (var 0)))) ->
    HasType Γ (let_repr type (union A B) e e') (expr type (C.subst0 e))

  -- Basic proof formers
  | triv {Γ}: HasType Γ triv (proof top)
  | abort {Γ: Context} {A: Term} {p: Term} {s: AnnotSort}:
    HasType Γ p (proof bot) ->
    HasType Γ A (sort s) ->
    HasType Γ (abort p) (expr s A)
  | dconj {Γ: Context} {A B l r: Term}:
    HasType Γ (dand A B) prop ->
    HasType Γ l (proof A) -> HasType Γ r (proof (B.subst0 l)) ->
    HasType Γ (dconj l r) (proof (dand A B))
  | let_conj {Γ: Context} {A B C e e': Term}:
    HasType Γ e (proof (dand A B)) ->
    HasType Γ A prop ->
    HasType ((Hyp.mk A (HypKind.val prop))::Γ) B prop ->
    HasType ((Hyp.mk (dand A B) (HypKind.val prop))::Γ) C prop ->
    HasType 
    ((Hyp.mk B (HypKind.val prop))::(Hyp.mk A (HypKind.val prop))::Γ) 
    e' (proof ((C.wknth 1).alpha0 (dconj (var 1) (var 0)))) ->
    HasType Γ (let_conj (dand A B) e e') (proof (C.subst0 e))
  | disj_l {Γ: Context} {A B e: Term}:
    HasType Γ e (proof A) ->
    HasType Γ B prop ->
    HasType Γ (disj 0 e) (proof (or A B))
  | disj_r {Γ: Context} {A B e: Term}:
    HasType Γ e (proof B) ->
    HasType Γ A prop ->
    HasType Γ (disj 1 e) (proof (or A B))
  | case_pr {Γ: Context} {A B C e l r: Term}:
    HasType Γ e (proof (or A B)) ->
    HasType Γ A prop ->
    HasType Γ B prop ->
    HasType ((Hyp.mk (or A B) (HypKind.val prop))::Γ) C prop ->
    HasType ((Hyp.mk A (HypKind.val prop))::Γ) l (proof (C.alpha0 (disj 0 (var 0)))) ->
    HasType ((Hyp.mk B (HypKind.val prop))::Γ) r (proof (C.alpha0 (disj 1 (var 0)))) ->
    HasType Γ (case_pr (or A B) e l r) (proof (C.subst0 e))
  | imp {Γ: Context} {φ s ψ: Term}:
    HasType Γ φ prop ->
    HasType ((Hyp.mk φ (HypKind.val prop))::Γ) s (proof ψ) ->
    HasType Γ (imp φ s) (proof (dimplies φ ψ))
  | mp {Γ: Context} {φ ψ l r: Term}:
    HasType Γ (dimplies φ ψ) prop ->
    HasType Γ l (proof (dimplies φ ψ)) -> HasType Γ r (proof φ) ->
    HasType Γ (mp (dimplies φ ψ) l r) (proof (ψ.subst0 r))
  | general {Γ: Context} {A s φ: Term}:
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) s (proof φ) ->
    HasType Γ (general A s) (proof (forall_ A φ))
  | inst {Γ: Context} {A φ l r: Term}:
    HasType Γ (forall_ A φ) prop ->
    HasType Γ l (proof (forall_ A φ)) -> 
    HasType Γ.upgrade r (term A) ->
    HasType Γ (inst (forall_ A φ) l r) (proof (φ.subst0 r))
  | wit {Γ: Context} {A φ l r: Term}:
    HasType Γ (exists_ A φ) prop ->
    HasType Γ.upgrade l (term A) -> HasType Γ r (proof (φ.subst0 l)) ->
    HasType Γ (wit l r) (proof (exists_ A φ))
  | let_wit {Γ: Context} {A φ C e e': Term}:
    HasType Γ e (proof (exists_ A φ)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A HypKind.gst)::Γ) φ prop ->
    HasType ((Hyp.mk (exists_ A φ) (HypKind.val prop))::Γ) C prop ->
    HasType 
    ((Hyp.mk φ (HypKind.val prop))::(Hyp.mk A (HypKind.val type))::Γ) 
    e' (proof ((C.wknth 1).alpha0 (wit (var 1) (var 0)))) ->
    HasType Γ (let_wit (exists_ A φ) e e') (proof (C.subst0 e))
  | case_prop {Γ: Context} {A B C e l r: Term}:
    HasType Γ.upgrade e (term (coprod A B)) ->
    HasType Γ A type ->
    HasType Γ B type ->
    HasType ((Hyp.mk (coprod A B) (HypKind.val type))::Γ) C prop ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ.upgrade) l (expr prop (C.alpha0 (inj 0 (var 0)))) ->
    HasType ((Hyp.mk B (HypKind.val type))::Γ.upgrade) r (expr prop (C.alpha0 (inj 1 (var 0)))) ->
    HasType Γ (case prop (coprod A B) e l r) (expr prop (C.subst0 e))
  | let_pair_prop {Γ: Context} {A B C e e': Term}:
    HasType Γ.upgrade e (term (sigma A B)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ.upgrade) B type ->
    HasType ((Hyp.mk (sigma A B) (HypKind.val type))::Γ.upgrade) C prop ->
    HasType 
    ((Hyp.mk B (HypKind.val type))::(Hyp.mk A (HypKind.val type))::Γ.upgrade) 
    e' (expr prop ((C.wknth 1).alpha0 (pair (var 1) (var 0)))) ->
    HasType Γ (let_pair prop (sigma A B) e e') (expr prop (C.subst0 e))
  | let_set_prop {Γ: Context} {A φ C e e': Term}:
    HasType Γ.upgrade e (term (set A φ)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType ((Hyp.mk (set A φ) (HypKind.val type))::Γ) C prop ->
    HasType 
    ((Hyp.mk φ (HypKind.val prop))::(Hyp.mk A (HypKind.val type))::Γ.upgrade) 
    e' (expr prop ((C.wknth 1).alpha0 (elem (var 1) (var 0)))) ->
    HasType Γ (let_set prop (set A φ) e e') (expr prop (C.subst0 e))
  | let_repr_prop {Γ: Context} {A B C e e': Term}:
    HasType Γ.upgrade e (term (union A B)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A HypKind.gst)::Γ) B type ->
    HasType ((Hyp.mk (union A B) (HypKind.val type))::Γ) C prop ->
    HasType 
    ((Hyp.mk B (HypKind.val type))::(Hyp.mk A HypKind.gst)::Γ.upgrade) 
    e' (expr prop ((C.wknth 1).alpha0 (repr (var 1) (var 0)))) ->
    HasType Γ (let_repr prop (union A B) e e') (expr prop (C.subst0 e))

  -- Theory of equality
  | refl {Γ: Context} {A a: Term}:
    HasType Γ.upgrade a (term A) -> HasType Γ (refl a) (proof (eq A a a))
  | discr {Γ: Context} {A B a b p: Term}:
    HasType Γ.upgrade a (term A) -> HasType Γ.upgrade b (term B) ->
    HasType Γ p (proof (eq (coprod A B) (inj 0 a) (inj 1 b))) ->
    HasType Γ (discr a b p) (proof bot)
  | unit_unique {Γ: Context} {a: Term}:
    HasType Γ.upgrade a (term unit) ->
    HasType Γ (unit_unique a) (proof (eq unit a nil))
  | cong {Γ: Context} {A P p e x y: Term}:
    HasType ((Hyp.mk A (HypKind.val type))::Γ) P prop -> 
    HasType Γ A type ->
    HasType Γ p (proof (eq A x y)) ->
    HasType Γ e (proof (P.subst0 x)) ->
    HasType Γ (cong p e P) (proof (P.subst0 y))
  -- | trans {Γ: Context} {A B p e x y: Term}:
  --   HasType ((Hyp.mk A (HypKind.val type))::Γ) B type -> 
  --   HasType Γ A type ->
  --   HasType Γ p (proof (eq A x y)) ->
  --   HasType Γ e (term (B.subst0 x)) ->
  --   HasType Γ (trans p e B) (term (B.subst0 y))
  | beta {Γ: Context} {A B s t: Term}:
    HasType ((Hyp.mk A (HypKind.val type))::Γ.upgrade) s (term B) ->
    HasType Γ A type ->
    HasType Γ.upgrade t (term A) ->
    HasType Γ (beta t s) 
    (proof (eq (B.subst0 t) 
    (app (pi A B) (lam A s) t) (s.subst0 t)))
  | beta_pr {Γ: Context} {φ A s p: Term}:
    HasType ((Hyp.mk φ (HypKind.val prop))::Γ.upgrade) s (term A) ->
    HasType Γ φ prop ->
    HasType Γ.upgrade p (proof φ) ->
    HasType Γ (beta_pr p s) 
    (proof (eq (A.subst0 p) 
    (app_pr (assume φ A) (lam_pr φ s) p) (s.subst0 p)))
  | beta_ir {Γ: Context} {A B s t: Term}:
  --TODO: val_type?
    HasType ((Hyp.mk A HypKind.gst)::Γ.upgrade) s (term B) ->
    HasType Γ A type ->
    HasType Γ.upgrade t (term A) ->
    HasType Γ (beta_ir t s) 
    (proof (eq (B.subst0 t) 
    (app_irrel (intersect A B) (lam_irrel A s) t) (s.subst0 t)))
  | eta {Γ: Context} {A B f: Term}:
    HasType Γ.upgrade f (term (pi A B)) ->
    HasType Γ A type ->
    HasType Γ (eta A f) (proof (eq (pi A B) (eta_ex A B f) f))
  | irir {Γ: Context} {A B f x y: Term}:
    HasType Γ.upgrade f (term (const_arrow A B)) ->
    HasType Γ.upgrade x (term A) ->
    HasType Γ.upgrade y (term A) ->
    HasType Γ (irir f x y) 
    (proof (eq B (irir_ex A B f x) (irir_ex A B f y)))
  | prir {Γ: Context} {A P x y: Term}:
    HasType ((Hyp.mk A (HypKind.val prop))::Γ) P prop -> 
    HasType Γ A prop ->
    HasType Γ x (proof A) ->
    HasType Γ y (proof A) ->
    HasType Γ (prir x y P) (proof (implies (P.subst0 x) (P.subst0 y)))
  | beta_left {Γ: Context} {A B C e l r: Term}:
    HasType Γ.upgrade e (term A) ->
    HasType Γ A type ->
    HasType Γ B type ->
    HasType ((Hyp.mk (coprod A B) (HypKind.val type))::Γ) C type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ.upgrade) l (expr type (C.alpha0 (inj 0 (var 0)))) ->
    HasType ((Hyp.mk B (HypKind.val type))::Γ.upgrade) r (expr type (C.alpha0 (inj 1 (var 0)))) ->
    HasType Γ (beta_left (coprod A B) (inj 0 e) l r) 
    (proof 
      (eq 
        (C.subst0 (inj 0 e)) 
        (case type (coprod A B) (inj 0 e) l r) 
        (l.subst0 e)))
  | beta_right {Γ: Context} {A B C e l r: Term}:
    HasType Γ.upgrade e (term B) ->
    HasType Γ A type ->
    HasType Γ B type ->
    HasType ((Hyp.mk (coprod A B) (HypKind.val type))::Γ) C type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ.upgrade) l (expr type (C.alpha0 (inj 0 (var 0)))) ->
    HasType ((Hyp.mk B (HypKind.val type))::Γ.upgrade) r (expr type (C.alpha0 (inj 1 (var 0)))) ->
    HasType Γ (beta_right (coprod A B) (inj 1 e) l r) 
    (proof 
      (eq 
        (C.subst0 (inj 1 e)) 
        (case type (coprod A B) (inj 1 e) l r) 
        (r.subst0 e)))
  | beta_pair {Γ: Context} {A B C l r e: Term}:
    HasType Γ.upgrade l (term A) ->
    HasType Γ.upgrade r (term (B.subst0 l)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) B type ->
    HasType ((Hyp.mk (sigma A B) (HypKind.val type))::Γ) C type ->
    HasType 
    ((Hyp.mk B (HypKind.val type))::(Hyp.mk A (HypKind.val type))::Γ.upgrade) 
    e (expr type ((C.wknth 1).alpha0 (pair (var 1) (var 0)))) ->
    HasType Γ 
      (beta_pair (sigma A B) l r e)
      (expr prop (eq (C.subst0 (pair l r)) (let_pair type (sigma A B) (pair l r) e) (e.subst01 r l)))
  | beta_set {Γ: Context} {A φ C l r e: Term}:
    HasType Γ.upgrade l (term A) ->
    HasType Γ r (proof (φ.subst0 l)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A (HypKind.val type))::Γ) φ prop ->
    HasType ((Hyp.mk (set A φ) (HypKind.val type))::Γ) C type ->
    HasType 
    ((Hyp.mk φ (HypKind.val prop))::(Hyp.mk A (HypKind.val type))::Γ.upgrade) 
    e (expr type ((C.wknth 1).alpha0 (elem (var 1) (var 0)))) ->
    HasType Γ 
      (beta_set (set A φ) l r e)
      (expr prop (eq (C.subst0 (elem l r)) (let_set type (set A φ) (elem l r) e) (e.subst01 r l)))
  | beta_repr {Γ: Context} {A B C l r e: Term}:
    HasType Γ.upgrade l (term A) ->
    HasType Γ.upgrade r (term (B.subst0 l)) ->
    HasType Γ A type ->
    HasType ((Hyp.mk A HypKind.gst)::Γ) B type ->
    HasType ((Hyp.mk (union A B) (HypKind.val type))::Γ) C type ->
    HasType 
    ((Hyp.mk B (HypKind.val type))::(Hyp.mk A HypKind.gst)::Γ.upgrade) 
    e (expr type ((C.wknth 1).alpha0 (repr (var 1) (var 0)))) ->
    HasType Γ 
      (beta_repr (union A B) l r e)
      (expr prop (eq (C.subst0 (repr l r)) (let_repr type (union A B) (repr l r) e) (e.subst01 r l)))
  --TODO: trans?
  --TODO: beta_trans?

  -- Natural numbers
  | nats {Γ}: HasType Γ nats type
  | zero {Γ}: HasType Γ zero (term nats)
  | succ {Γ}: HasType Γ succ (term (arrow nats nats))
  | natrec {Γ: Context} {C e z s: Term}:
    HasType ((Hyp.mk nats HypKind.gst)::Γ) C type ->
    HasType Γ e (term nats) ->
    HasType Γ z (term (C.subst0 zero)) ->
    HasType ((Hyp.mk C (HypKind.val type))::(Hyp.mk nats HypKind.gst)::Γ) s
    (term ((C.wknth 1).alpha0 (app (arrow nats nats) succ (var 1)))) ->
    HasType Γ (natrec type C e z s) (expr type (C.subst0 e))
  | natrec_prop {Γ: Context} {C e z s: Term}:
    HasType ((Hyp.mk nats HypKind.gst)::Γ) C prop ->
    HasType Γ.upgrade e (term nats) ->
    HasType Γ.upgrade z (term (C.subst0 zero)) ->
    HasType 
      ((Hyp.mk C (HypKind.val prop))::(Hyp.mk nats HypKind.gst)::Γ.upgrade) s
    (term ((C.wknth 1).alpha0 (app (arrow nats nats) succ (var 1)))) ->
    HasType Γ (natrec prop C e z s) (expr prop (C.subst0 e))
  | beta_zero {Γ: Context} {C z s: Term}:
    HasType ((Hyp.mk nats HypKind.gst)::Γ) C type ->
    HasType Γ.upgrade z (term (C.subst0 zero)) ->
    HasType 
    ((Hyp.mk C (HypKind.val type))::(Hyp.mk nats HypKind.gst)::Γ.upgrade) s
    (term ((C.wknth 1).alpha0 (app (arrow nats nats) succ (var 1)))) ->
    HasType Γ 
      (beta_zero C z s) 
      (expr prop (eq (C.subst0 zero) (natrec type C zero z s) z))
  | beta_succ {Γ: Context} {C e z s: Term}:
    HasType ((Hyp.mk nats HypKind.gst)::Γ) C type ->
    HasType Γ.upgrade e (term nats) ->
    HasType Γ.upgrade z (term (C.subst0 zero)) ->
    HasType 
      ((Hyp.mk C (HypKind.val type))::(Hyp.mk nats HypKind.gst)::Γ.upgrade) s
    (term ((C.wknth 1).alpha0 (app (arrow nats nats) succ (var 1)))) ->
    HasType Γ 
      (beta_succ C e z s)
      --ENHANCE: make succ a builtin operator instead?
      (expr prop (eq
        (C.subst0 (app (arrow nats nats) succ e))
        (natrec type C 
          (app (arrow nats nats) succ e) z s)
        (s.subst01 (natrec type C e z s) e)
      ))

notation Γ "⊢" a ":" A => HasType Γ a A
notation Γ "⊢" a "∈" A => HasType Γ a (term A)
notation Γ "⊢" a "∴" A => HasType Γ a (prop A)

theorem HasType.succ_nat {Γ n} (H: Γ ⊢ n: term Term.nats)
  : Γ ⊢ Term.app (Term.arrow Term.nats Term.nats) Term.succ n: term Term.nats
  := by repeat first | assumption | constructor

theorem HasType.fv {Γ a A} (P: Γ ⊢ a: A): a.fv ≤ Γ.length := by {
  induction P 
  <;> intros 
  <;> try apply Nat.zero_le -- constants, e.g. nats, nil, zero
  case var =>
    apply HasVar.fv
    assumption

  all_goals (
    simp only [
      Term.fv, 
      Nat.max_r_le_split, 
      Nat.le_sub_is_le_add
    ] at *;
    simp only [
      Context.upgrade_length_is_length,
      List.length
    ] at *
    repeat first 
    | assumption
    | apply And.intro
  )
}

theorem HasVar'.upgrade (p: HasVar' Γ A k n): 
  HasVar' Γ.upgrade A (HypKind.val k.annot) n := by {
  induction p with
  | zero H => 
    rename_i k k';
    simp only [Context.upgrade, Hyp.upgrade]
    apply zero
    cases H;
    cases k <;> constructor
    constructor
  | succ => apply succ; assumption
}

theorem HasVar'.wk_sort {k k'} (Hk: k.is_sub k') (p: HasVar' Γ A k' n): 
  HasVar' Γ A k n := by {
  induction p with
  | zero H => 
    rename_i k k';
    simp only [Context.upgrade, Hyp.upgrade]
    apply zero
    cases H;
    apply Hk
    cases Hk
    constructor
  | succ _ I => 
    apply succ
    apply I
    apply Hk
}

theorem HasVar'.upgrade_weak (p: HasVar' Γ A k n): 
  HasVar' Γ.upgrade A k n := by {
  induction p with
  | zero H => 
    rename_i k k';
    simp only [Context.upgrade, Hyp.upgrade]
    apply zero
    cases H;
    cases k <;> constructor
    constructor
  | succ => apply succ; assumption
}

theorem HasVar'.downgrade_helper: {Γ Γ': Context} -> Γ' = Γ.upgrade -> 
  ∀ {n A k}, HasVar' Γ' A k n -> HasVar' Γ A k.downgrade n := by {
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
    | zero =>
      apply zero
      apply HypKind.downgrade_wk
      assumption
    | succ => 
      apply succ
      apply I rfl
      assumption
  }

theorem HasVar'.downgrade {Γ n A k}: 
  HasVar' Γ.upgrade A k n -> HasVar' Γ A k.downgrade n :=
  downgrade_helper rfl

theorem HasVar.downgrade {Γ n A k}: 
  HasVar Γ.upgrade A k n -> 
    ∃k', k.downgrade.is_sub k' ∧ HasVar Γ A k' n :=
  by {
    intro Hv;
    have Hv' := Hv.v.downgrade;
    rw [HasVar'.e_eq] at Hv';
    exact Hv';
  }

theorem HasVar'.upgrade_val (p: HasVar' Γ n (HypKind.val s) A): 
  HasVar' Γ.upgrade n (HypKind.val s) A := HasVar'.upgrade p

theorem HasVar.upgrade_val (p: HasVar Γ n (HypKind.val s) A): 
  HasVar Γ.upgrade n (HypKind.val s) A := 
  HasVar.v_eq ▸ HasVar'.upgrade (HasVar.v_eq ▸ p)

theorem HasVar'.upgrade_upgraded:
  k.is_sub k' -> HasVar' Γ n k A -> HasVar' Γ.upgrade n k' A := by {
  intro Hk HΓ;
  have Hv := upgrade HΓ;
  cases k <;> cases Hk <;> try exact Hv
  exact HasVar'.wk_sort HypKind.is_sub.gst Hv
}

theorem HasVar'.upgrade_downgraded:
  HasVar' Γ n k.downgrade A -> HasVar' Γ.upgrade n k A 
  := upgrade_upgraded HypKind.downgrade_is_sub

theorem HasVar.ghost_up:
  HasVar Γ n HypKind.gst A -> HasVar Γ.upgrade n (HypKind.val type) A 
  := by {
    intro Hv;
    generalize Hk': HypKind.gst = k';
    rw [Hk'] at Hv;
    induction Hv with
    | zero => cases Hk'; constructor
    | succ _ I => constructor; exact I Hk'
  }

theorem HasVar.uniq {Γ: Context} {n k k' A A'}
  (H: HasVar Γ n k A)
  (H': HasVar Γ n k' A')
  : k = k' ∧ A = A'
  := by {
    induction H generalizing k' A' with
    | zero => cases H'; exact ⟨rfl, rfl⟩
    | succ _ I => 
      cases H' with
      | succ H' =>
        have ⟨Hk, HA⟩ := I H';
        constructor;
        exact Hk;
        rw [HA]
  }

theorem HasVar.no_ghosts {Γ: Context} {A n}:
  ¬HasVar Γ.upgrade A HypKind.gst n
  := by {
    generalize HΓ: Γ.upgrade = Γ';
    generalize Hk: HypKind.gst = k;
    intro H;
    induction H generalizing Γ with
    | zero =>
      cases Γ with
      | nil => cases HΓ
      | cons H Γ =>
        cases HΓ;
        cases H with
        | mk A k =>
          cases k <;> cases Hk
    | succ _ I => 
      cases Γ with
      | nil => cases HΓ
      | cons H Γ =>
        cases HΓ;
        exact I rfl Hk
  }

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

inductive IsCtx: Context -> Prop
  | nil: IsCtx []
  | cons_val {Γ A s}: 
    IsCtx Γ -> (Γ ⊢ A: sort s) 
    -> IsCtx ((Hyp.mk A (HypKind.val s))::Γ)
  | cons_gst {Γ A}: 
    IsCtx Γ -> (Γ ⊢ A: type) -> 
    IsCtx ((Hyp.mk A HypKind.gst)::Γ)

theorem IsCtx.upgrade {Γ} (H: IsCtx Γ): IsCtx Γ.upgrade
  := by {
    induction H <;>
    constructor <;>
    first | assumption | (apply HasType.upgrade; assumption)
  }

def IsHyp (Γ: Context) (H: Hyp): Prop := Γ ⊢ H.ty: sort H.kind.annot

theorem HasType.to_var {s A n} (H: Γ ⊢ Term.var n: expr s A):
  HasVar Γ n (HypKind.val s) A := by cases H <;> assumption

--TODO: ask about weird goal hints here...

syntax "upgrade_ctx_helper" tactic: tactic


macro_rules
  | `(tactic| upgrade_ctx_helper $t) => `(tactic| $t)


macro_rules
  | `(tactic| upgrade_ctx_helper $_) => `(tactic|
      first 
        | apply Context.is_sub.refl 
        | apply Context.is_sub.upgrade 
        | apply Context.is_sub.cons
        | apply Hyp.is_sub.refl
        | apply Hyp.is_sub.upgrade
        | apply Hyp.is_sub.refl_ty
        | apply HypKind.is_sub.refl
        | apply HypKind.is_sub.gst
        | rw [Context.upgrade_idem]
  )

syntax "upgrade_ctx" tactic: tactic

macro_rules
  | `(tactic| upgrade_ctx $t) => `(tactic|
      simp only [Context.upgrade_idem];
      apply HasType.sub <;>
      repeat upgrade_ctx_helper $t
  )