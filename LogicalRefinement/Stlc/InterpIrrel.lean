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

theorem Stlc.Context.interp.eq_mod_lrt.extend
    {Δ: Stlc.Context} 
    {H: Hyp} {x: Option H.ty.stlc_ty.interp} 
    {G G': Δ.interp} {Γ: _root_.Context}:
  G.eq_mod_lrt G' Γ -> @eq_mod_lrt (_::Δ) (x, G) (x, G') (H::Γ)
  := by {
    intro HGG' n Hn;
    cases n with
    | zero => rfl
    | succ n => 
      apply HGG' n;
      have ⟨A, HAn⟩ := Hn;
      cases HAn;
      constructor
      assumption
  }

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

theorem HasType.interp_irrel_eq {Γ a A} {G G': Γ.stlc.interp} 
  (H: Γ ⊢ a: expr type A) 
  (HGG': G.eq_mod_lrt G' Γ)
  : G.eq_mod G' a.stlc 
  := λ_ Hn => HGG' _ (H.interp_irrel_dep _ Hn)

theorem HasType.interp_irrel {Γ a A} {G G': Γ.stlc.interp} 
  (H: Γ ⊢ a: expr type A)
  (HGG': G.eq_mod_lrt G' Γ)
  : H.stlc.interp G = H.stlc.interp G'
  := H.stlc.eq_mod (H.interp_irrel_eq HGG')