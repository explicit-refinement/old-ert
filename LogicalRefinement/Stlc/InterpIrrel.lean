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

def Context.is_val (Γ: Context) (n: Nat): Prop
  := ∃A s, HasVar Γ n (HypKind.val s) A

@[simp] def Stlc.Context.interp.eq_mod_lrt 
  {Γ' Δ': Stlc.Context} (G: Γ'.interp) (D: Δ'.interp) 
  (Γ Δ: _root_.Context): Prop
  := ∀n: Nat, Γ.is_rel n ∧ Δ.is_rel n -> eq_at G D n

@[simp] def Stlc.Context.interp.eq_mod_lrt_val 
  {Γ' Δ': Stlc.Context} (G: Γ'.interp) (D: Δ'.interp) 
  (Γ Δ: _root_.Context): Prop
  := ∀n: Nat, Γ.is_val n ∧ Δ.is_val n -> eq_at G D n

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

theorem Stlc.Context.interp.eq_mod_lrt_val.extend
    {Γ' Δ': Stlc.Context} 
    {H: Hyp} {x: Option H.ty.stlc_ty.interp} 
    {G: Γ'.interp} {D: Δ'.interp} {Γ Δ: _root_.Context}:
  G.eq_mod_lrt_val D Γ Δ -> 
  @eq_mod_lrt_val (_::Γ') (_::Δ') (x, G) (x, D) (H::Γ) (H::Δ)
  := by {
    intro HGG' n Hn;
    cases n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n => 
      apply HGG' n;
      have ⟨⟨A, s, HAn⟩, ⟨A', s', HAn'⟩⟩ := Hn;
      cases HAn;
      cases HAn';
      constructor
      constructor
      constructor
      assumption
      constructor
      constructor
      assumption
  }

theorem Stlc.Context.interp.eq_mod_lrt.extend_prop
    {Γ' Δ': Stlc.Context} 
    {A: Term} {X Y: Ty} {x: Option X.interp} {y: Option Y.interp} 
    {G: Γ'.interp} {D: Δ'.interp} {Γ Δ: _root_.Context}:
  G.eq_mod_lrt D Γ Δ -> 
  @eq_mod_lrt (_::Γ') (_::Δ') (x, G) (y, D) ((Hyp.mk A (HypKind.val prop))::Γ) ((Hyp.mk A (HypKind.val prop))::Δ)
  := by {
    intro HGG' n Hn;
    cases n with
    | zero =>
      have ⟨⟨_, HA⟩, _⟩ := Hn;
      cases HA
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
    {A: Term} {L R} {x y} 
    {G: Γ'.interp} {D: Δ'.interp} {Γ Δ: _root_.Context}:
  G.eq_mod_lrt D Γ Δ -> 
  @eq_mod_lrt (L::Γ') (R::Δ') (x, G) (y, D) 
    ((Hyp.mk A HypKind.gst)::Γ) 
    ((Hyp.mk A HypKind.gst)::Δ)
  := by {
    intro HGG' n Hn;
    cases n with
    | zero =>
      have ⟨⟨_, HA⟩, _⟩ := Hn;
      cases HA
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

theorem Stlc.Context.interp.eq_mod_lrt.extend_gst_left
    {Γ' Δ': Stlc.Context} {H}
    {A: Term} {L R} {x y} 
    {G: Γ'.interp} {D: Δ'.interp} {Γ Δ: _root_.Context}:
  G.eq_mod_lrt D Γ Δ -> 
  @eq_mod_lrt (L::Γ') (R::Δ') (x, G) (y, D) 
    ((Hyp.mk A HypKind.gst)::Γ) 
    (H::Δ)
  := by {
    intro HGG' n Hn;
    cases n with
    | zero =>
      have ⟨⟨_, HA⟩, _⟩ := Hn;
      cases HA
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

  theorem Stlc.Context.interp.eq_mod_lrt.extend_gst_right
    {Γ' Δ': Stlc.Context}  {H}
    {A: Term} {L R} {x y} 
    {G: Γ'.interp} {D: Δ'.interp} {Γ Δ: _root_.Context}:
  G.eq_mod_lrt D Γ Δ -> 
  @eq_mod_lrt (L::Γ') (R::Δ') (x, G) (y, D) 
    (H::Γ) 
    ((Hyp.mk A HypKind.gst)::Δ)
  := by {
    intro HGG' n Hn;
    cases n with
    | zero =>
      have ⟨_, ⟨_, HA⟩⟩ := Hn;
      cases HA
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

theorem Stlc.Context.interp.eq_mod_lrt_refl'
    {Γ': Stlc.Context} (G D: Γ'.interp) (Γ Δ: _root_.Context) (H: G = D):
    G.eq_mod_lrt D Γ Δ
  := by {
    cases H;
    apply eq_mod_lrt_refl <;> assumption
  }

theorem Stlc.Context.interp.eq_mod_lrt_val_refl
    {Γ': Stlc.Context} (G: Γ'.interp) (Γ Δ: _root_.Context):
    G.eq_mod_lrt_val G Γ Δ
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
            | prop => cases HΓ
          | gst => cases HΓ
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

theorem Stlc.Context.interp.eq_mod_lrt_val_downgrade
    {Γ: _root_.Context} (G: Γ.upgrade.stlc.interp) (Δ) :
    G.downgrade.eq_mod_lrt_val G Γ Δ
  := by {
    induction Γ generalizing Δ with
    | nil => intro _ ⟨⟨_, _, HΓ⟩, _⟩; cases HΓ
    | cons H Γ I =>
      intro n ⟨⟨A, _, HΓ⟩, ⟨B, _, HΔ⟩⟩;
      cases n with
      | zero => 
        cases H with
        | mk A k =>
          cases k with
          | val s => exact ⟨rfl, rfl⟩
          | gst => cases HΓ
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
            constructor
            assumption
            constructor
            constructor
            assumption
          )
  } 

theorem HasType.interp_irrel_dep_cast {Γ a A n}
  (H: Γ ⊢ a: expr type A) (Ha: a = Term.var n ∨ Γ.is_rel n): Γ.is_rel n
  := by {
    cases Ha with
    | inl Ha => rw [Ha] at H; cases H; exact ⟨_, by assumption⟩
    | inr Ha => exact Ha
  }

theorem HasType.interp_irrel_dep {Γ a s A} 
  (H: Γ ⊢ a: expr s A) (n: Nat)
  (Ha: a.stlc.has_dep n): a = Term.var n ∨ Γ.is_rel n := by {
    generalize HA': expr s A = A';
    rw [HA'] at H;
    induction H generalizing A s n with
    | var => cases Ha; exact Or.inl rfl
    | lam Hs _ Is _ => 
      apply Or.inr
      cases Hs.interp_irrel_dep_cast (Is (n + 1) Ha rfl) with
      | intro A Hv => 
        cases Hv;
        exact ⟨_, by assumption⟩
    | app _ Hl Hr _ Il Ir => 
      apply Or.inr
      cases Ha with
      | inl Ha => exact Hl.interp_irrel_dep_cast (Il n Ha rfl)
      | inr Ha => exact Hr.interp_irrel_dep_cast (Ir n Ha rfl)
    | pair _ Hl Hr _ Il Ir => 
      apply Or.inr
      cases Ha with
      | inl Ha => exact Hl.interp_irrel_dep_cast (Il n Ha rfl)
      | inr Ha => exact Hr.interp_irrel_dep_cast (Ir n Ha rfl)
    | let_pair He _ _ _ He' Ie _ _ _ Ie' => 
      apply Or.inr
      cases HA';
      cases Ha with
      | inl Ha => exact He.interp_irrel_dep_cast (Ie n Ha rfl)
      | inr Ha => 
        cases He'.interp_irrel_dep_cast (Ie' (n + 2) Ha rfl) with
        | intro A Hv =>
          cases Hv with
          | succ Hv => 
            cases Hv;
            exact ⟨_, by assumption⟩
    | inj_l He _ Ie _ => exact Or.inr (He.interp_irrel_dep_cast (Ie n Ha rfl))
    | inj_r He _ Ie _ => exact Or.inr (He.interp_irrel_dep_cast (Ie n Ha rfl))
    | case Hd _ _ _ Hl Hr Id _ _ _ Il Ir =>  
      apply Or.inr
      cases HA';
      cases Ha with
      | inl Ha => exact Hd.interp_irrel_dep_cast (Id n Ha rfl)
      | inr Ha =>
        cases Ha with
        | inl Ha => 
          cases Hl.interp_irrel_dep_cast (Il (n + 1) Ha rfl) with
          | intro A Hv => 
            cases Hv;
            exact ⟨_, by assumption⟩
        | inr Ha => 
          cases Hr.interp_irrel_dep_cast (Ir (n + 1) Ha rfl) with
          | intro A Hv => 
            cases Hv;
            exact ⟨_, by assumption⟩
    | elem _ Hl _ _ Il _ => exact Or.inr (Hl.interp_irrel_dep_cast (Il n Ha rfl))
    | let_set He _ _ _ He' Ie _ _ _ Ie' =>  
      apply Or.inr
      cases HA';
      cases Ha with
      | inl Ha => 
        cases Ha with
        | inl Ha => exact He.interp_irrel_dep_cast (Ie n Ha rfl)
        | inr Ha => cases Ha
      | inr Ha => 
        cases He'.interp_irrel_dep_cast (Ie' (n + 2) Ha rfl) with
        | intro A Hv =>
          cases Hv with
          | succ Hv => 
            cases Hv;
            exact ⟨_, by assumption⟩
    | lam_pr _ Hs _ Is => 
      cases Hs.interp_irrel_dep_cast (Is (n + 1) Ha rfl) with
      | intro A Hv => 
        cases Hv;
        exact Or.inr ⟨_, by assumption⟩
    | app_pr _ Hl _ _ Il _ => 
      cases Ha with
      | inl Ha => exact Or.inr (Hl.interp_irrel_dep_cast (Il n Ha rfl))
      | inr Ha => cases Ha
    --TODO: Hmm... the fact that the order is swapped for lam is... interesting...
    | lam_irrel _ Hs _ Is => 
      cases Hs.interp_irrel_dep_cast (Is (n + 1) Ha rfl) with
      | intro A Hv => 
        cases Hv;
        exact Or.inr ⟨_, by assumption⟩
    | app_irrel _ Hl _ _ Il _ => 
      cases Ha with
      | inl Ha => exact Or.inr (Hl.interp_irrel_dep_cast (Il n Ha rfl))
      | inr Ha => cases Ha
    | repr _ _ Hr _ _ Ir => exact Or.inr (Hr.interp_irrel_dep_cast (Ir n Ha rfl))
    | let_repr He _ _ _ He' Ie _ _ _ Ie' =>  
      apply Or.inr
      cases HA';
      cases Ha with
      | inl Ha => 
        cases Ha with
        | inl Ha => cases Ha
        | inr Ha => exact He.interp_irrel_dep_cast (Ie n Ha rfl)
      | inr Ha => 
        cases He'.interp_irrel_dep_cast (Ie' (n + 2) Ha rfl) with
        | intro A Hv =>
          cases Hv with
          | succ Hv => 
            cases Hv;
            exact ⟨_, by assumption⟩
    | natrec _ He Hz Hs _ Ie Iz Is => 
      apply Or.inr
      rename AnnotSort => k;
      cases HA';
      cases Ha with
      | inl Ha => exact He.interp_irrel_dep_cast (Ie n Ha rfl)
      | inr Ha =>
        cases Ha with
        | inl Ha => exact Hz.interp_irrel_dep_cast (Iz n Ha rfl)
        | inr Ha => 
          cases Hs.interp_irrel_dep_cast (Is (n + 2) Ha rfl) with
          | intro A Hv =>
            cases Hv with
            | succ Hv => 
              cases Hv;
              exact ⟨_, by assumption⟩
    | _ => cases HA' <;> cases Ha
  }


theorem HasType.interp_irrel_dep_ty {Γ a A} 
  (H: Γ ⊢ a: expr type A) (n: Nat)
  (Ha: a.stlc.has_dep n): Γ.is_rel n 
  := H.interp_irrel_dep_cast (H.interp_irrel_dep n Ha)

theorem HasType.interp_irrel_val {Γ a s A} 
  (H: Γ ⊢ a: expr s A) (n: Nat)
  (Ha: a.stlc.has_dep n): Γ.is_val n 
  := match H.interp_irrel_dep n Ha with
  | Or.inl Ha => by cases Ha; cases H; exact ⟨_, s, by assumption⟩
  | Or.inr H => by cases H; exact ⟨_, type, by assumption⟩

theorem HasType.interp_irrel_eq_ty {Γ' Δ': Stlc.Context} {Γ Δ a A} 
  {G: Γ'.interp} {D: Δ'.interp} 
  (HΓ: Γ ⊢ a: expr type A)
  (HΔ: Δ ⊢ a: expr type A)
  (HGD: G.eq_mod_lrt D Γ Δ)
  : G.eq_mod D a.stlc 
  := λ_ Hn => 
    HGD _ ⟨(HΓ.interp_irrel_dep_ty _ Hn), (HΔ.interp_irrel_dep_ty _ Hn)⟩

theorem HasType.interp_irrel_eq {Γ' Δ': Stlc.Context} {Γ Δ a s A} 
  {G: Γ'.interp} {D: Δ'.interp} 
  (HΓ: Γ ⊢ a: expr s A)
  (HΔ: Δ ⊢ a: expr s A)
  (HGD: G.eq_mod_lrt_val D Γ Δ)
  : G.eq_mod D a.stlc 
  := λ_ Hn => 
    HGD _ ⟨(HΓ.interp_irrel_val _ Hn), (HΔ.interp_irrel_val _ Hn)⟩

theorem HasType.interp_irrel_ty {Γ Δ a A} 
  {G: Γ.stlc.interp} {D: Δ.stlc.interp} 
  (HΓ: Γ ⊢ a: expr type A)
  (HΔ: Δ ⊢ a: expr type A)
  (HGD: G.eq_mod_lrt D Γ Δ)
  : HΓ.stlc.interp G = HΔ.stlc.interp D
  := HΓ.stlc.eq_mod HΔ.stlc (HΓ.interp_irrel_eq_ty HΔ HGD)

theorem HasType.interp_irrel_ty' {Γ Δ a A b B} 
  {G: Γ.stlc.interp} {D: Δ.stlc.interp} 
  (HΓ: Γ ⊢ a: expr type A)
  (HΔ: Δ ⊢ a: expr type A)
  (HΓ': Γ.stlc ⊧ b: B)
  (HΔ': Δ.stlc ⊧ b: B)
  (Hb: b = a.stlc)
  (HB: B = A.stlc_ty)
  (HGD: G.eq_mod_lrt D Γ Δ)
  : HΓ'.interp G = HΔ'.interp D
  := by {
    cases Hb; cases HB;
    exact HΓ.stlc.eq_mod HΔ.stlc (HΓ.interp_irrel_eq_ty HΔ HGD)
  }

theorem HasType.interp_upgrade' {Γ a s A} 
  {G: Γ.upgrade.stlc.interp}
  (HΓ: Γ ⊢ a: expr s A)
  (HΔ: Γ.upgrade ⊢ a: expr s A)
  : HΓ.stlc.interp G.downgrade = HΔ.stlc.interp G
  := HΓ.stlc.eq_mod HΔ.stlc (HΓ.interp_irrel_eq HΔ (G.eq_mod_lrt_val_downgrade _))

theorem HasType.interp_upgrade {Γ a s A} 
  {G: Γ.upgrade.stlc.interp}
  (HΓ: Γ ⊢ a: expr s A)
  : HΓ.stlc.interp G.downgrade = HΓ.upgrade.stlc.interp G
  := HΓ.interp_upgrade' HΓ.upgrade

theorem HasType.interp_prop_ty {Γ: Context} {a A ϕ: Term} 
  {G: Γ.stlc.interp}
  {x y: Option ϕ.stlc_ty.interp}
  (HΓ: ((Hyp.mk ϕ (HypKind.val prop))::Γ) ⊢ a: expr type A)
  : HΓ.stlc.interp (x, G) = HΓ.stlc.interp (y, G)
  := HΓ.stlc.eq_mod HΓ.stlc 
    (HΓ.interp_irrel_eq_ty HΓ (G.eq_mod_lrt_refl Γ Γ).extend_prop)

theorem HasType.interp_prop_none_ty {Γ: Context} {a A ϕ: Term} 
  {G: Γ.stlc.interp}
  {x: Option ϕ.stlc_ty.interp}
  (HΓ: ((Hyp.mk ϕ (HypKind.val prop))::Γ) ⊢ a: expr type A)
  : HΓ.stlc.interp (x, G) = HΓ.stlc.interp (none, G)
  := HΓ.stlc.eq_mod HΓ.stlc 
    (HΓ.interp_irrel_eq_ty HΓ (G.eq_mod_lrt_refl Γ Γ).extend_prop)

theorem HasType.interp_prop_ty' {Γ: Context} {a A ϕ: Term} 
  {G: Γ.stlc.interp}
  {X Y: Ty} {x: Option X.interp} {y: Option Y.interp}
  (Ha: ((Hyp.mk ϕ (HypKind.val prop))::Γ) ⊢ a: expr type A)
  (HΓ: (X::Γ.stlc) ⊧ a.stlc: A.stlc_ty)
  (HΔ: (Y::Γ.stlc) ⊧ a.stlc: A.stlc_ty)
  : HΓ.interp (x, G) = HΔ.interp (y, G)
  := HΓ.eq_mod HΔ
    (Ha.interp_irrel_eq_ty Ha (G.eq_mod_lrt_refl Γ Γ).extend_prop)

theorem HasType.interp_prop_none_ty' {Γ: Context} {a A ϕ: Term} 
  {G: Γ.stlc.interp}
  {X Y: Ty} {x: Option X.interp}
  (Ha: ((Hyp.mk ϕ (HypKind.val prop))::Γ) ⊢ a: expr type A)
  (HΓ: (X::Γ.stlc) ⊧ a.stlc: A.stlc_ty)
  (HΔ: (Y::Γ.stlc) ⊧ a.stlc: A.stlc_ty)
  : HΓ.interp (x, G) = HΔ.interp (none, G)
  := HΓ.eq_mod HΔ
    (Ha.interp_irrel_eq_ty Ha (G.eq_mod_lrt_refl Γ Γ).extend_prop)

theorem HasType.interp_gst_ty {Γ: Context} {s A B: Term} 
  {G: Γ.stlc.interp}
  {x y: Option Ty.unit.interp}
  (HΓ: ((Hyp.mk A HypKind.gst)::Γ) ⊢ s: expr type B)
  : HΓ.stlc.interp (x, G) = HΓ.stlc.interp (y, G)
  := HΓ.stlc.eq_mod HΓ.stlc 
    (HΓ.interp_irrel_eq_ty HΓ (G.eq_mod_lrt_refl Γ Γ).extend_gst)

theorem HasType.interp_gst_none_ty {Γ: Context} {s A B: Term} 
  {G: Γ.stlc.interp}
  {x: Option Ty.unit.interp}
  (HΓ: ((Hyp.mk A HypKind.gst)::Γ) ⊢ s: expr type B)
  : HΓ.stlc.interp (x, G) = HΓ.stlc.interp (none, G)
  := HΓ.stlc.eq_mod HΓ.stlc 
    (HΓ.interp_irrel_eq_ty HΓ (G.eq_mod_lrt_refl Γ Γ).extend_gst)