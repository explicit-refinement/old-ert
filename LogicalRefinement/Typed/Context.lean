import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
open Untyped

--TODO: flip sub, suffer

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

inductive HypKind.is_sub: HypKind -> HypKind -> Prop
  | refl {k}: is_sub k k
  | gst: is_sub gst (val type)

theorem HypKind.is_sub.trans {a b c: HypKind}: a.is_sub b -> b.is_sub c -> a.is_sub c := by {
  cases a <;> cases b <;> cases c <;> intro H1 H2 <;> cases H1 <;> cases H2 <;> constructor
}

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
  k.is_sub k'.upgrade -> k.downgrade.is_sub k' := by {
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

def HypKind.downgrade_is_sub {k: HypKind}: k.downgrade.is_sub k := by {
  cases k with
  | val s => cases s <;> constructor
  | gst => constructor
}

theorem HypKind.is_sub.upgrade: {k: HypKind} -> k.is_sub k.upgrade
  | val type => is_sub.refl
  | val prop => is_sub.refl
  | HypKind.gst => is_sub.gst

theorem HypKind.is_sub.upgrade_bin {k k': HypKind}: k.is_sub k' -> k.upgrade.is_sub k'.upgrade := by {
  intro H;
  cases H <;>
  constructor
}

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

def HypKind.annot_wk_eq {k k': HypKind}: k.is_sub k' -> k.annot = k'.annot
  := by {
    intro H;
    cases H <;> rfl
  }


def HypKind.annot_is_sub {k: HypKind}: k.is_sub (val k.annot)
  := by {
    cases k <;> simp <;> constructor
  }

def HypKind.annot_other_is_sub {k k': HypKind}: 
  k.is_sub k' -> k'.is_sub (val k.annot)
  := by {
    intro H;
    cases H with
    | refl => exact annot_is_sub
    | gst => exact is_sub.refl
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

inductive Hyp.is_sub: Hyp -> Hyp -> Prop
  | refl_ty {A k k'}: HypKind.is_sub k k' -> is_sub (Hyp.mk A k) (Hyp.mk A k') 

theorem Hyp.is_sub.refl {H: Hyp}: H.is_sub H := by {
  constructor;
  cases H;
  constructor
}

theorem Hyp.is_sub.upgrade {H: Hyp}: H.is_sub H.upgrade := by {
  constructor;
  cases H;
  exact HypKind.is_sub.upgrade
}

theorem Hyp.is_sub.upgrade_bin {H H': Hyp}: H.is_sub H' -> H.upgrade.is_sub H'.upgrade := by {
  intro HH;
  cases HH with
  | refl_ty Hk =>
    cases Hk with
    | refl => constructor; apply HypKind.is_sub.upgrade_bin; constructor
    | gst => constructor; constructor
}

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

inductive Context.is_sub: Context -> Context -> Prop
  | nil: is_sub [] []
  | cons {Γ Δ H H'}: is_sub Γ Δ -> Hyp.is_sub H H' -> is_sub (H::Γ) (H'::Δ)

theorem Context.is_sub.step {Γ Δ: Context} {H: Hyp} (p: Γ.is_sub Δ): Context.is_sub (H::Γ) (H::Δ) 
  := cons p Hyp.is_sub.refl

theorem Context.is_sub.refl {Γ: Context}: Γ.is_sub Γ := by {
  induction Γ with
  | nil => exact nil
  | cons => exact cons (by assumption) Hyp.is_sub.refl
}

theorem Context.is_sub.upgrade {Γ: Context}: Γ.is_sub Γ.upgrade := by {
  induction Γ with
  | nil => exact nil
  | cons => exact cons (by assumption) Hyp.is_sub.upgrade
}

theorem Context.is_sub.upgrade_bin: {Γ Δ: Context} -> Γ.is_sub Δ -> Γ.upgrade.is_sub Δ.upgrade := by {
  intro Γ;
  induction Γ with
  | nil => intro Δ H; cases H; exact nil
  | cons H Γ I =>
    intro Δ H;
    cases H;
    constructor
    apply I
    assumption
    apply Hyp.is_sub.upgrade_bin
    assumption
}

--TODO: move to Untyped.Basic?
def Untyped.arrow (A B: Untyped) := pi A (wk1 B)

def Untyped.implies (φ ψ: Untyped) := dimplies φ ψ.wk1

def constAnnot: UntypedKind [] -> Annot
  | UntypedKind.nats => type
  | UntypedKind.top => prop
  | UntypedKind.bot => prop
  | UntypedKind.zero => term nats
  | UntypedKind.succ => term (arrow nats nats)
  | UntypedKind.nil => proof top

def Untyped.sym_ty_tmp: Untyped :=
  forall_ (var 0) (
    forall_ (var 1) (
      implies (eq (var 2) (var 1) (var 0)) (eq (var 2) (var 0) (var 1))
    )
  )

def Untyped.trans_ty_tmp: Untyped :=
  forall_ (var 0) (
    forall_ (var 1) (
      forall_ (var 2) (
        implies (eq (var 3) (var 2) (var 1)) (
          implies (eq (var 3) (var 1) (var 0)) (eq (var 3) (var 2) (var 0))
        )
      )
    )
  )

def Untyped.sym_ty_tmp_fv: sym_ty_tmp.fv = 1 := rfl
def Untyped.trans_ty_tmp_fv: trans_ty_tmp.fv = 1 := rfl

def Untyped.sym_ty (A: Untyped): Untyped := sym_ty_tmp.subst0 A
def Untyped.trans_ty (A: Untyped): Untyped := trans_ty_tmp.subst0 A