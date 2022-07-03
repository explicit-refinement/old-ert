import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.Irrel
import LogicalRefinement.Utils
open Annot
open AnnotSort

def Context.is_irrel (Γ: Context) (n: Nat): Prop
  := ∃A, ∃k, k ≠ HypKind.val type ∧ HasVar Γ n k A

def Context.is_rel (Γ: Context) (n: Nat): Prop
  := ∃A, HasVar Γ n (HypKind.val type) A

@[simp] def Stlc.Context.interp.eq_mod_lrt 
  {Γ: Stlc.Context} (G G': Γ.interp) (Γ: _root_.Context): Prop
  := ∀n: Nat, Γ.is_rel n -> eq_at G G' n

theorem HasType.interp_irrel_dep {Γ a A} (H: Γ ⊢ a: expr type A) (n: Nat):
  a.stlc.has_dep n -> Γ.is_rel n := by {
    generalize HA': expr type A = A';
    rw [HA'] at H;
    induction H with
    | var HA Hv _IA =>
      intro H;
      cases H; 
      cases HA';
      exists A
    | _ => cases HA' <;> sorry
  }