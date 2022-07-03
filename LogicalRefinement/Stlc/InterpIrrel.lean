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
  {Γ' Δ': Stlc.Context} (G: Γ'.interp) (D: Δ'.interp) 
  (Γ Δ: _root_.Context): Prop
  := ∀n: Nat, Γ.is_rel n ∧ Δ.is_rel n -> eq_at G D n

theorem Stlc.Context.interp.eq_mod_lrt.extend
    {Γ' Δ': Stlc.Context} 
    {H: Hyp} {x: Option H.ty.stlc_ty.interp} 
    {G: Γ'.interp} {D: Δ'.interp} {Γ Δ: _root_.Context}:
  G.eq_mod_lrt D Γ Δ -> 
  @eq_mod_lrt (_::Γ') (_::Δ') (x, G) (x, D) (H::Γ) (H::Δ)
  := by {
    intro HGG' n Hn;
    cases n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n => 
      apply HGG' n;
      have ⟨⟨A, HAn⟩, ⟨A', HAn'⟩⟩ := Hn;
      cases HAn;
      cases HAn';
      constructor
      constructor
      assumption
      constructor
      assumption
  }

theorem HasType.interp_irrel_dep {Γ a A} 
  (H: Γ ⊢ a: expr type A) (n: Nat):
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

theorem HasType.interp_irrel_eq {Γ Δ a A} 
  {G: Γ.stlc.interp} {D: Δ.stlc.interp} 
  (HΓ: Γ ⊢ a: expr type A)
  (HΔ: Δ ⊢ a: expr type A)
  (HGD: G.eq_mod_lrt D Γ Δ)
  : G.eq_mod D a.stlc 
  := λ_ Hn => 
    HGD _ ⟨(HΓ.interp_irrel_dep _ Hn), (HΔ.interp_irrel_dep _ Hn)⟩

theorem HasType.interp_irrel {Γ Δ a A} 
  {G: Γ.stlc.interp} {D: Δ.stlc.interp} 
  (HΓ: Γ ⊢ a: expr type A)
  (HΔ: Δ ⊢ a: expr type A)
  (HGD: G.eq_mod_lrt D Γ Δ)
  : HΓ.stlc.interp G = HΔ.stlc.interp D
  := HΓ.stlc.eq_mod HΔ.stlc (HΓ.interp_irrel_eq HΔ HGD)