import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc
import LogicalRefinement.Denot.Basic

open AnnotSort
open Annot

theorem HasType.eq_lrt_ty_denot
  {Γ Δ: Context} {A a s} 
  {G: Γ.upgrade.stlc.interp}
  {D: Δ.upgrade.stlc.interp}
  (HΓ: Γ ⊢ A: sort s)
  (HΔ: Δ ⊢ A: sort s)
  (HGD: G.eq_mod_lrt D Γ.upgrade Δ.upgrade)
  : A.denote_ty G a = A.denote_ty D a
  := by {
    generalize HS: sort s = S;
    rw [HS] at HΓ;
    induction HΓ generalizing Δ s with
    | pi _ _ IA IB =>
      cases HΔ; 
      cases a with
      | none => rfl
      | some a => 
        dsimp only [Term.denote_ty]
        apply forall_helper;
        intro x;
        apply arrow_equivalence;
        apply IA;
        assumption
        exact HGD;
        rfl
        apply @IB 
          ((Hyp.mk _ (HypKind.val type))::Δ) 
          (x.bind a) _ (x, G) (x, D);
        assumption
        exact HGD.extend
        rfl
    | sigma _ _ IA IB => 
      cases HΔ; 
      cases a with
      | none => rfl
      | some a => 
        cases a with
        | mk a b =>
          dsimp only [Term.denote_ty]
          simp only [pure]
          apply congr (congr rfl _) _;
          apply IA <;> assumption
          apply @IB
            ((Hyp.mk _ (HypKind.val type))::Δ) 
            (some b) _ (some a, G) (some a, D);
          assumption
          exact HGD.extend
          rfl
    | coprod _ _ IA IB => 
      cases HΔ; 
      cases a with
      | none => rfl
      | some a => 
        cases a with
        | inl a => exact IA (by assumption) HGD rfl
        | inr a => exact IB (by assumption) HGD rfl
    | assume _ _ IA IB => 
      cases HΔ; 
      cases a with
      | none => rfl
      | some a => 
        dsimp only [Term.denote_ty]
        apply arrow_equivalence;
        apply IA;
        assumption
        exact HGD;
        rfl
        apply @IB 
          ((Hyp.mk _ (HypKind.val prop))::Δ) 
          (a ()) _ (none, G) (none, D);
        assumption
        exact HGD.extend
        rfl
    | set _ _ IA IB => 
      cases HΔ; 
      dsimp only [Term.denote_ty]
      dsimp only [Term.stlc_ty] at a;
      apply congr (congr rfl _) _;
      apply IA <;> assumption
      apply @IB
        ((Hyp.mk _ (HypKind.val type))::Δ) 
        none _ (a, G) (a, D);
      assumption
      exact HGD.extend
      rfl
    | intersect _ _ IA IB => 
      cases HΔ; 
      cases a with
      | none => rfl
      | some a => 
        dsimp only [Term.denote_ty]
        apply forall_helper;
        intro x;
        apply arrow_equivalence;
        apply IA;
        assumption
        exact HGD;
        rfl
        apply @IB 
          ((Hyp.mk _ (HypKind.val type))::Δ) 
          (a ()) _ (x, G) (x, D);
        assumption
        exact HGD.extend
        rfl
    | union _ _ IA IB =>  
      cases HΔ;
      dsimp only [Term.denote_ty]
      simp only [pure]
      apply congr rfl _;
      funext x;
      apply congr (congr rfl _) _;
      apply IA;
      assumption
      exact HGD
      rfl
      apply @IB 
        ((Hyp.mk _ (HypKind.val type))::Δ) 
        a _ (x, G) (x, D);
      assumption
      exact HGD.extend
      rfl
    | dimplies _ _ IA IB => 
      cases HΔ;
      dsimp only [Term.denote_ty]
      apply arrow_equivalence;
      apply IA;
      assumption
      exact HGD;
      rfl
      apply @IB 
        ((Hyp.mk _ (HypKind.val prop))::Δ) 
        none _ (none, G) (none, D);
      assumption
      exact HGD.extend
      rfl
    | dand _ _ IA IB =>  
      cases HΔ;
      dsimp only [Term.denote_ty]
      simp only [pure]
      apply congr (congr rfl _) _;
      apply IA;
      assumption
      exact HGD
      rfl
      apply @IB 
        ((Hyp.mk _ (HypKind.val prop))::Δ) 
        none _ (none, G) (none, D);
      assumption
      exact HGD.extend
      rfl
    | or _ _ IA IB => 
      cases HΔ;
      dsimp only [Term.denote_ty]
      exact congr 
        (congr rfl (IA (by assumption) HGD rfl)) 
        (IB (by assumption) HGD rfl);
    | forall_ _ _ IA IB =>  
      cases HΔ; 
      dsimp only [Term.denote_ty]
      apply forall_helper;
      intro x;
      apply arrow_equivalence;
      apply IA;
      assumption
      exact HGD;
      rfl
      apply @IB 
        ((Hyp.mk _ (HypKind.val type))::Δ) 
        none _ (x, G) (x, D);
      assumption
      exact HGD.extend
      rfl
    | exists_ _ _ IA IB => 
      cases HΔ;
      dsimp only [Term.denote_ty]
      simp only [pure]
      apply congr rfl _;
      funext x;
      apply congr (congr rfl _) _;
      apply IA;
      assumption
      exact HGD
      rfl
      apply @IB 
        ((Hyp.mk _ (HypKind.val type))::Δ) 
        none _ (x, G) (x, D);
      assumption
      exact HGD.extend
      rfl
    | eq _ Hl Hr =>
      cases HΔ with
      | eq HA' Hl' Hr' =>
        dsimp only [Term.denote_ty]
        apply propext;
        apply Iff.intro;
        {
          intro ⟨_, _, HG⟩;
          exists Hl'.stlc, Hr'.stlc;
          rw [<-Hl.interp_irrel_ty Hl' HGD]
          rw [<-Hr.interp_irrel_ty Hr' HGD]
          exact HG
        }
        {
          intro ⟨_, _, HG⟩;
          exists Hl.stlc, Hr.stlc;
          rw [Hl.interp_irrel_ty Hl' HGD]
          rw [Hr.interp_irrel_ty Hr' HGD]
          exact HG
        }
    | _ => cases HS <;> rfl
  }

theorem HasType.eq_lrt_ty_denot'
  {Γ: Context} {A a s} 
  {G D: Γ.upgrade.stlc.interp}
  (HΓ: Γ ⊢ A: sort s)
  (HGD: G.eq_mod_lrt D Γ.upgrade Γ.upgrade)
  : A.denote_ty G a = A.denote_ty D a
  := HΓ.eq_lrt_ty_denot HΓ HGD