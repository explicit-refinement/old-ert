import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.InterpSubst
import LogicalRefinement.Stlc.InterpWk
import LogicalRefinement.Stlc.Subst

open Annot
open AnnotSort

theorem HasVar.stlc_var {Γ n A} (_: HasVar Γ n (HypKind.val type) A)
  : (Term.var n).stlc = Stlc.var n
  := rfl

theorem HasType.stlc_var_term {Γ n A} (H: Γ ⊢ Term.var n: term A)
  : (Term.var n).stlc = Stlc.var n
  := HasVar.stlc_var (by cases H; assumption)

theorem HasType.stlc_interp_var {Γ n A} (H: Γ ⊢ Term.var n: term A):
  H.stlc.interp = H.to_var.stlc.interp
  := by {
    funext G;
    rw [<-
      Stlc.HasType.interp_transport_inner (Stlc.HasType.var H.to_var.stlc)
      _ H.stlc_var_term.symm rfl
    ]
    rfl
  }

  theorem Stlc.Context.interp.downgrade_cast
  {Γ: _root_.Context} (G: Γ.upgrade.stlc.interp)
  (p: Γ.upgrade.stlc.interp = Γ.upgrade.upgrade.stlc.interp)
  : (cast p G).downgrade = G
  := by {
    induction Γ with
    | nil => rfl
    | cons H Γ I =>
      cases H with
      | mk A k =>
        cases k <;>
        cases G with
        | mk x G =>
          simp only [downgrade]
          rw [rec_to_cast']
          rw [cast_pair']
          rw [I]
          rfl
          rw [Context.upgrade_idem]
          rfl
  }
