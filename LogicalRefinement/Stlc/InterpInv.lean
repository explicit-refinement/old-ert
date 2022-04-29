import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.InterpWk
import LogicalRefinement.Stlc.Subst
open AnnotSort

theorem Stlc.HasVar.interp_inv {Γ n A} 
  (Hv: Stlc.HasVar Γ.stlc n A) (HΓ: IsCtx Γ)
  : ∃A', 
    (_root_.HasVar Γ (Γ.sparsity.ix_inv n) (HypKind.val type) A') 
    ∧ ((Annot.expr AnnotSort.type A').stlc_ty = A) 
    ∧ (Γ ⊢ A': AnnotSort.type)
  := by {
    induction Γ generalizing n A with
    | nil => cases Hv
    | cons H Γ I =>
      cases H with
      | mk H k => 
        have ⟨HH, HΓ'⟩: (Γ ⊢ H: k.annot) ∧ (IsCtx Γ) := 
          by cases HΓ <;> apply And.intro <;> assumption;
        have HH': ((Hyp.mk H k)::Γ) ⊢ H.wk1: k.annot := HH.wk1_sort;
        cases k with
        | val s =>
          cases s with
          | type => 
            rw [Context.sparsity_true]
            {
              cases Hv with
              | zero => 
                exact ⟨
                  H.wk1, 
                  by repeat constructor, 
                  by apply Term.stlc_ty_wk1, 
                  HH'
                  ⟩
              | succ Hv => 
                have ⟨A', Hv', HA', HΓA'⟩ := I Hv HΓ';
                exact ⟨
                  A'.wk1, 
                  Hv'.succ, 
                  by 
                    dsimp only [Annot.stlc_ty]; rw [Term.stlc_ty_wk1]; 
                    exact HA', 
                  HΓA'.wk1_sort
                  ⟩
            }
            rfl
          | prop => 
            rw [Context.sparsity_false]
            dsimp only [Sparsity.ix_inv]
            {
              have ⟨A', Hv', HA', HΓA'⟩ := I Hv HΓ';
              exact ⟨
                A'.wk1, 
                Hv'.succ, 
                by dsimp only [Annot.stlc_ty]; rw [Term.stlc_ty_wk1]; exact HA', 
                HΓA'.wk1_sort
                ⟩
            }
            simp only [Hyp.kind]
        | gst => 
          rw [Context.sparsity_false]
          dsimp only [Sparsity.ix_inv]
          {
              have ⟨A', Hv', HA', HΓA'⟩ := I Hv HΓ';
              exact ⟨
                A'.wk1, 
                Hv'.succ, 
                by dsimp only [Annot.stlc_ty]; rw [Term.stlc_ty_wk1]; exact HA', 
                HΓA'.wk1_sort
                ⟩
          }
          simp only [Hyp.kind]
  }