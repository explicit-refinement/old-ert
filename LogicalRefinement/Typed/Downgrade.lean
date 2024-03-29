import LogicalRefinement.Untyped
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Wk
open Term
open Annot
open AnnotSort

set_option maxHeartbeats 10000000

theorem HasType.downgrade_helper {Δ Γ: Context} {a A s}
  : (Δ ⊢ a: A) -> (Γ.is_sub Δ) -> (A = sort s) -> Γ ⊢ a: sort s
  := by {
    intro H;
    induction H generalizing s Γ;
    case eq _ Hl Hr IA _ _ => 
      intro HΓΔ Hs;
      rw [<-Hs]
      rw [<-HΓΔ.upgrade_eq] at Hl
      rw [<-HΓΔ.upgrade_eq] at Hr
      exact HasType.eq (IA HΓΔ rfl) Hl Hr
    
    all_goals (
      intro HΓΔ Hs; 
      first | contradiction | (
        rw [<-Hs]
        rename_i' HA HB IA IB;
        constructor <;> (
          first 
          | exact IA HΓΔ rfl
          | (
            apply IB
            repeat constructor
            try assumption
            repeat constructor
            try rfl
          )
        )
      )
    )
  }

theorem HasType.downgrade {Γ: Context} {A s} (H: Γ.upgrade ⊢ A: sort s): Γ ⊢ A: sort s
  := H.downgrade_helper Context.is_sub.upgrade rfl

theorem HasType.repr01 
  (HA: Γ ⊢ A: sort type)
  (HB: ((Hyp.mk A (HypKind.val type))::Γ) ⊢ B: sort type):
  ({ ty := B, kind := HypKind.val type }::{ ty := A, kind := HypKind.gst }::Γ)
  ⊢ Term.repr (Term.var 1) (Term.var 0): term (Term.union A B).wk1.wk1
  := HasType.repr (HasType.union HA HB).wk1.wk1 
      (HasType.var HA.upgrade.wk1_sort.wk1_sort (by repeat constructor)) 
      (by {
        simp only [Term.wk_composes, Wk.comp]
        have Hwk: Wk.wk1.step = Wk.wkn 2 := rfl;
        rw [Hwk]
        rw [Term.lift_wkn2_subst0_var1]
        constructor;
        apply HasType.wk1_sort;
        apply HasType.downgrade;
        rw [Context.upgrade]
        upgrade_ctx assumption;
        constructor
      })

theorem HasType.repr01'
  (HA: Γ ⊢ A: sort type)
  (HB: ((Hyp.mk A (HypKind.val type))::Γ) ⊢ B: sort type):
  ({ ty := B, kind := HypKind.val type }::{ ty := A, kind := HypKind.val type }::Γ)
  ⊢ Term.repr (Term.var 1) (Term.var 0): term (Term.union A B).wk1.wk1
  := HasType.repr (HasType.union HA HB).wk1.wk1 
      (HasType.var HA.upgrade.wk1_sort.wk1_sort (by repeat constructor)) 
      (by {
        simp only [Term.wk_composes, Wk.comp]
        have Hwk: Wk.wk1.step = Wk.wkn 2 := rfl;
        rw [Hwk]
        rw [Term.lift_wkn2_subst0_var1]
        constructor;
        apply HasType.wk1_sort;
        apply HasType.downgrade;
        rw [Context.upgrade]
        upgrade_ctx assumption;
        constructor
      })

theorem HasType.repr01''
  (HA: Γ ⊢ A: sort type)
  (HB: ((Hyp.mk A HypKind.gst)::Γ) ⊢ B: sort type):
  ({ ty := B, kind := HypKind.val type }::{ ty := A, kind := HypKind.val type }::Γ)
  ⊢ Term.repr (Term.var 1) (Term.var 0): term (Term.union A B).wk1.wk1
  := HasType.repr (HasType.union HA (by upgrade_ctx exact HB)).wk1.wk1 
      (HasType.var HA.upgrade.wk1_sort.wk1_sort (by repeat constructor)) 
      (by {
        simp only [Term.wk_composes, Wk.comp]
        have Hwk: Wk.wk1.step = Wk.wkn 2 := rfl;
        rw [Hwk]
        rw [Term.lift_wkn2_subst0_var1]
        constructor;
        apply HasType.wk1_sort;
        apply HasType.downgrade;
        rw [Context.upgrade]
        upgrade_ctx assumption;
        constructor
      })

theorem HasType.dconj01 
  (HA: Γ ⊢ A: sort prop)
  (HB: ((Hyp.mk A (HypKind.val prop))::Γ) ⊢ B: sort prop):
  ({ ty := B, kind := HypKind.val prop }::{ ty := A, kind := HypKind.val prop }::Γ)
  ⊢ Term.dconj (Term.var 1) (Term.var 0): proof (Term.dand A B).wk1.wk1
  := HasType.dconj (HasType.dand HA HB).wk1.wk1 
      (HasType.var HA.wk1_sort.wk1_sort (by repeat constructor)) 
      (by {
        simp only [Term.wk_composes, Wk.comp]
        have Hwk: Wk.wk1.step = Wk.wkn 2 := rfl;
        rw [Hwk]
        rw [Term.lift_wkn2_subst0_var1]
        constructor;
        apply HasType.wk1_sort;
        apply HasType.downgrade;
        rw [Context.upgrade]
        upgrade_ctx assumption;
        constructor
      })

theorem HasType.wit01
  (HA: Γ ⊢ A: sort type)
  (HB: ((Hyp.mk A (HypKind.val type))::Γ) ⊢ B: sort prop):
  ({ ty := B, kind := HypKind.val prop }::{ ty := A, kind := HypKind.gst }::Γ)
  ⊢ Term.wit (Term.var 1) (Term.var 0): proof (Term.exists_ A B).wk1.wk1
  := HasType.wit (HasType.exists_ HA HB).wk1.wk1 
      (HasType.var HA.upgrade.wk1_sort.wk1_sort (by repeat constructor)) 
      (by {
        simp only [Term.wk_composes, Wk.comp]
        have Hwk: Wk.wk1.step = Wk.wkn 2 := rfl;
        rw [Hwk]
        rw [Term.lift_wkn2_subst0_var1]
        constructor;
        apply HasType.wk1_sort;
        apply HasType.downgrade;
        rw [Context.upgrade]
        upgrade_ctx assumption;
        constructor
      })

theorem HasType.wit01'
  (HA: Γ ⊢ A: sort type)
  (HB: ((Hyp.mk A (HypKind.val type))::Γ) ⊢ B: sort prop):
  ({ ty := B, kind := HypKind.val prop }::{ ty := A, kind := HypKind.val type }::Γ)
  ⊢ Term.wit (Term.var 1) (Term.var 0): proof (Term.exists_ A B).wk1.wk1
  := HasType.wit (HasType.exists_ HA HB).wk1.wk1 
      (HasType.var HA.upgrade.wk1_sort.wk1_sort (by repeat constructor)) 
      (by {
        simp only [Term.wk_composes, Wk.comp]
        have Hwk: Wk.wk1.step = Wk.wkn 2 := rfl;
        rw [Hwk]
        rw [Term.lift_wkn2_subst0_var1]
        constructor;
        apply HasType.wk1_sort;
        apply HasType.downgrade;
        rw [Context.upgrade]
        upgrade_ctx assumption;
        constructor
      })