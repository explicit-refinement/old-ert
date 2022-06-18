import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.InterpInv
import LogicalRefinement.Stlc.InterpSubst
import LogicalRefinement.Stlc.InterpWk
import LogicalRefinement.Stlc.Subst

open Annot
open AnnotSort

theorem HasVar.stlc_var {Γ n A} (H: HasVar Γ n (HypKind.val type) A)
  : (Term.var n).stlc Γ.sparsity = Stlc.var (Γ.sparsity.ix n)
  := by {
    dsimp only [Term.stlc, Sparsity.stlc]
    rw [if_pos]
    rw [H.sigma]
    rfl
  }

theorem HasType.stlc_var_term {Γ n A} (H: Γ ⊢ Term.var n: term A)
  : (Term.var n).stlc Γ.sparsity = Stlc.var (Γ.sparsity.ix n)
  := HasVar.stlc_var (by cases H <;> assumption)

theorem HasType.stlc_interp_var {Γ n A} (H: Γ ⊢ Term.var n: term A):
  H.stlc.interp = H.to_var.stlc.interp
  := by {
    dsimp only [Context.stlc_ix]
    funext G;
    rw [<-
      Stlc.HasType.interp_transport_inner (Stlc.HasType.var H.to_var.stlc) 
      _ H.stlc_var_term.symm rfl
    ]
    rfl
  }

theorem Stlc.Context.thin_upgrade {Γ: _root_.Context}:
    Γ.upgrade.stlc.thin Γ.upgrade.downgrade_sparsity =
    Γ.upgrade.stlc
    := by {
      induction Γ with
      | nil => rfl
      | cons H Γ I =>
        cases H with
        | mk A k =>
          cases k with
          | val s => 
            cases s with
            | type => exact congr rfl I
            | prop => exact I
          | gst => exact congr rfl I
    }
  
theorem Stlc.Context.thin_double_upgrade_helper {Γ: _root_.Context}:
    Γ.upgrade.upgrade.stlc.thin Γ.upgrade.downgrade_sparsity =
    Γ.upgrade.upgrade.stlc
    := by {
      rw [Context.upgrade_idem]
      exact thin_upgrade
    }

theorem Stlc.Context.thin_upgrade_cast
  {Γ: _root_.Context} (G: Γ.upgrade.upgrade.stlc.interp)
  : G.thin Γ.upgrade.downgrade_sparsity
  = cast (by rw [thin_double_upgrade_helper]) G
  := by {
    induction Γ with
    | nil => rfl
    | cons H Γ I => 
      cases H with
      | mk A k => 
        cases k with
        | val s =>
          cases s with
          | type =>
            cases G with
            | mk x G => 
              simp only [interp.thin, Context.downgrade_sparsity]
              rw [cast_pair']
              apply congr rfl;
              exact I G
              rfl
          | prop => 
              simp only [interp.thin, Context.downgrade_sparsity]
              exact I G
        | gst => 
          cases G with
          | mk x G => 
            simp only [interp.thin, Context.downgrade_sparsity]
            rw [cast_pair']
            apply congr rfl;
            exact I G
            rfl
  }

theorem Stlc.Context.interp.downgrade_cast
  {Γ: _root_.Context} (G: Γ.upgrade.stlc.interp)
  (p: Γ.upgrade.stlc.interp = Γ.upgrade.upgrade.stlc.interp)
  : (cast p G).downgrade = G
  := by {
    unfold downgrade
    unfold Eq.mpr
    rw [rec_to_cast']
    rw [thin_upgrade_cast]
    rw [cast_merge]
    rw [cast_merge]
    rfl
  }