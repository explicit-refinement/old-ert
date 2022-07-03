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

theorem Stlc.Context.interp.eq_mod_lrt.extend_prop
    {Γ' Δ': Stlc.Context} 
    {A: Term} {x y: Option A.stlc_ty.interp} 
    {G: Γ'.interp} {D: Δ'.interp} {Γ Δ: _root_.Context}:
  G.eq_mod_lrt D Γ Δ -> 
  @eq_mod_lrt (_::Γ') (_::Δ') (x, G) (y, D) ((Hyp.mk A (HypKind.val prop))::Γ) ((Hyp.mk A (HypKind.val prop))::Δ)
  := by {
    intro HGG' n Hn;
    cases n with
    | zero =>
      have ⟨⟨_, HA⟩, _⟩ := Hn;
      cases HA with
      | zero Hk => cases Hk
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
  
theorem Stlc.Context.interp.eq_mod_lrt.extend_gst
    {Γ' Δ': Stlc.Context} 
    {A: Term} {x y: Option A.stlc_ty.interp} 
    {G: Γ'.interp} {D: Δ'.interp} {Γ Δ: _root_.Context}:
  G.eq_mod_lrt D Γ Δ -> 
  @eq_mod_lrt (_::Γ') (_::Δ') (x, G) (y, D) ((Hyp.mk A HypKind.gst)::Γ) ((Hyp.mk A HypKind.gst)::Δ)
  := by {
    intro HGG' n Hn;
    cases n with
    | zero =>
      have ⟨⟨_, HA⟩, _⟩ := Hn;
      cases HA with
      | zero Hk => cases Hk
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


theorem Stlc.Context.interp.eq_mod_lrt_refl
    {Γ': Stlc.Context} (G: Γ'.interp) (Γ Δ: _root_.Context):
    G.eq_mod_lrt G Γ Δ
  := λn _ => G.eq_at_refl n 

theorem Stlc.Context.interp.eq_mod_lrt_downgrade
    {Γ: _root_.Context} (G: Γ.upgrade.stlc.interp) (Δ) :
    G.downgrade.eq_mod_lrt G Γ Δ
  := by {
    induction Γ generalizing Δ with
    | nil => intro _ ⟨⟨_, HΓ⟩, _⟩; cases HΓ
    | cons H Γ I =>
      intro n ⟨⟨A, HΓ⟩, ⟨B, HΔ⟩⟩;
      cases n with
      | zero => 
        cases H with
        | mk A k =>
          cases k with
          | val s =>
            cases s with
            | type => exact ⟨rfl, rfl⟩
            --TODO: make a tactic for this?
            | prop => cases HΓ with | zero Hk => cases Hk 
          | gst => cases HΓ with | zero Hk => cases Hk
      | succ n =>
        cases H with
        | mk A k =>
          cases k <;> (
            cases G;
            unfold eq_at;
            simp only [
              Context.upgrade, Context.stlc, Hyp.upgrade,
              downgrade
            ]
            cases HΓ;
            cases HΔ;
            apply I;
            constructor
            constructor
            assumption
            constructor
            assumption
          )
  } 

theorem HasType.interp_irrel_dep {Γ a A} 
  (H: Γ ⊢ a: expr type A) (n: Nat)
  (Ha: a.stlc.has_dep n): Γ.is_rel n := by {
    generalize HA': expr type A = A';
    rw [HA'] at H;
    induction H generalizing A n with
    | var HA Hv _IA =>
      cases Ha; 
      cases HA';
      exact ⟨_, Hv⟩
    | lam _ _ Is _ => 
      cases Is (n + 1) Ha rfl with
      | intro A Hv => 
        cases Hv;
        exact ⟨_, by assumption⟩
    | app _ _ _ _ Il Ir => 
      cases Ha with
      | inl Ha => exact Il n Ha rfl
      | inr Ha => exact Ir n Ha rfl
    | pair _ _ _ _ Il Ir => 
      cases Ha with
      | inl Ha => exact Il n Ha rfl
      | inr Ha => exact Ir n Ha rfl
    | let_pair _ _ _ _ _ Ie _ _ _ Ie' => 
      cases HA';
      cases Ha with
      | inl Ha => exact Ie n Ha rfl
      | inr Ha => 
        cases Ie' (n + 2) Ha rfl with
        | intro A Hv =>
          cases Hv with
          | succ Hv => 
            cases Hv;
            exact ⟨_, by assumption⟩
    | inj_l _ _ Ie _ => exact Ie n Ha rfl
    | inj_r _ _ Ie _ => exact Ie n Ha rfl
    | case _ _ _ _ _ _ Id _ _ _ Il Ir => 
      cases HA';
      cases Ha with
      | inl Ha => exact Id n Ha rfl
      | inr Ha =>
        cases Ha with
        | inl Ha => 
          cases Il (n + 1) Ha rfl with
          | intro A Hv => 
            cases Hv;
            exact ⟨_, by assumption⟩
        | inr Ha => 
          cases Ir (n + 1) Ha rfl with
          | intro A Hv => 
            cases Hv;
            exact ⟨_, by assumption⟩
    | elem _ _ _ _ Il _ => exact Il n Ha rfl
    | let_set _ _ _ _ _ Ie _ _ _ Ie' =>  
      cases HA';
      cases Ha with
      | inl Ha => 
        cases Ha with
        | inl Ha => exact Ie n Ha rfl
        | inr Ha => cases Ha
      | inr Ha => 
        cases Ie' (n + 2) Ha rfl with
        | intro A Hv =>
          cases Hv with
          | succ Hv => 
            cases Hv;
            exact ⟨_, by assumption⟩
    | lam_pr _ _ _ Is => 
      cases Is (n + 1) Ha rfl with
      | intro A Hv => 
        cases Hv;
        exact ⟨_, by assumption⟩
    | app_pr _ _ _ _ Il _ => 
      cases Ha with
      | inl Ha => exact Il n Ha rfl
      | inr Ha => cases Ha
    --TODO: Hmm... the fact that the order is swapped for lam is... interesting...
    | lam_irrel _ _ _ Is => 
      cases Is (n + 1) Ha rfl with
      | intro A Hv => 
        cases Hv;
        exact ⟨_, by assumption⟩
    | app_irrel _ _ _ _ Il _ => 
      cases Ha with
      | inl Ha => exact Il n Ha rfl
      | inr Ha => cases Ha
    | repr _ _ _ _ _ Ir => exact Ir n Ha rfl
    | let_repr _ _ _ _ _ Ie _ _ _ Ie' =>  
      cases HA';
      cases Ha with
      | inl Ha => 
        cases Ha with
        | inl Ha => cases Ha
        | inr Ha => exact Ie n Ha rfl
      | inr Ha => 
        cases Ie' (n + 2) Ha rfl with
        | intro A Hv =>
          cases Hv with
          | succ Hv => 
            cases Hv;
            exact ⟨_, by assumption⟩
    | natrec _ _ _ _ _ Ie Iz Is => 
      rename AnnotSort => k;
      cases HA';
      cases Ha with
      | inl Ha => exact Ie n Ha rfl
      | inr Ha =>
        cases Ha with
        | inl Ha => exact Iz n Ha rfl
        | inr Ha => 
          cases Is (n + 2) Ha rfl with
          | intro A Hv =>
            cases Hv with
            | succ Hv => 
              cases Hv;
              exact ⟨_, by assumption⟩
    | _ => cases HA' <;> cases Ha
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

theorem HasType.interp_upgrade {Γ a A} 
  {G: Γ.upgrade.stlc.interp}
  (HΓ: Γ ⊢ a: expr type A)
  (HΔ: Γ.upgrade ⊢ a: expr type A)
  : HΓ.stlc.interp G.downgrade = HΔ.stlc.interp G
  := HΓ.stlc.eq_mod HΔ.stlc 
    (HΓ.interp_irrel_eq HΔ (G.eq_mod_lrt_downgrade _))

theorem HasType.interp_upgrade' {Γ a A} 
  {G: Γ.upgrade.stlc.interp}
  (HΓ: Γ ⊢ a: expr type A)
  : HΓ.stlc.interp G.downgrade = HΓ.upgrade.stlc.interp G
  := HΓ.stlc.eq_mod HΓ.upgrade.stlc 
    (HΓ.interp_irrel_eq HΓ.upgrade (G.eq_mod_lrt_downgrade _))