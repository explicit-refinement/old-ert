import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp
import LogicalRefinement.Stlc.Subst

set_option maxHeartbeats 1000000

theorem Term.stlc_wknth_false {t: Term} {Γ: Sparsity} {n: Nat}
: (t.wknth n).stlc (Γ.wknth n false) = t.stlc Γ
:= by {
  revert Γ n;
  induction t with
  | var v => 
    intro Γ n;
    simp only [wknth, wk]
    repeat rw [stlc_var]
    simp only [Sparsity.stlc, Sparsity.wknth_ix_false, Sparsity.wknth_dep]
  | _ => 
    intro Γ n;
    simp only [wknth, wk]
    repeat rw [Wk.lift_wknth_merge]
    repeat rw [Wk.liftn_wknth_merge]
    repeat rw [<-wknth_def] 
    try (rename TermKind _ => k; cases k);
    try (rename AnnotSort => s; cases s);
    all_goals try rfl;    
    all_goals (
      simp only [stlc] 
      simp only [Sparsity.wknth_merge]
      simp only [*]
      repeat rw [Term.stlc_ty_wknth]
      try rfl
    )
}

theorem Term.stlc_wknth_true {t: Term} {Γ: Sparsity} {n: Nat}
: (t.wknth n).stlc (Γ.wknth n true) = (t.stlc Γ).wknth (Γ.ix n)
:= by {
  revert Γ n;
  induction t with
  | var v => 
    intro Γ n;
    simp only [wknth, wk]
    repeat rw [stlc_var]
    simp only [Sparsity.stlc]
    split
    . have H: Γ.dep v = true := by
        rw [<-Sparsity.wknth_dep]
        assumption
      rw [Sparsity.wknth_ix_true' H]
      rw [if_pos H]
      simp only [Stlc.wknth, Stlc.wk, Wk.wknth_var]
    . rw [if_neg]
      rfl
      simp only [Sparsity.wknth_dep] at *
      assumption
  | _ => 
    intro Γ n;
    simp only [wknth, wk]
    repeat rw [Wk.lift_wknth_merge]
    repeat rw [Wk.liftn_wknth_merge]
    repeat rw [<-wknth_def] 
    try (rename TermKind _ => k; cases k);
    try (rename AnnotSort => s; cases s);
    all_goals try rfl;    
    all_goals (
      simp only [stlc] 
      simp only [Sparsity.wknth_merge]
      simp only [*]
      repeat rw [Term.stlc_ty_wknth]
      try rfl
    )
}