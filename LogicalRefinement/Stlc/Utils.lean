import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.InterpInv
import LogicalRefinement.Stlc.InterpSubst
import LogicalRefinement.Stlc.InterpWk
import LogicalRefinement.Stlc.Subst

open Annot

set_option pp.explicit true

theorem HasVar.stlc_var {Γ n A} (H: HasVar Γ n (HypKind.val type) A)
  : (Term.var n).stlc Γ.sparsity = Stlc.var (Γ.sparsity.ix n)
  := by {
    dsimp only [Term.stlc, Sparsity.stlc]
    rw [if_pos]
    rw [H.sigma]
    sorry
  }

theorem HasType.stlc_var_term {Γ n A} (H: Γ ⊢ Term.var n: term A)
  : (Term.var n).stlc Γ.sparsity = Stlc.var (Γ.sparsity.ix n)
  := by {
    sorry
  }

theorem HasType.stlc_interp_var {Γ n A} (H: Γ ⊢ Term.var n: term A):
  H.stlc.interp = H.to_var.stlc.interp
  := by {
    sorry
  }