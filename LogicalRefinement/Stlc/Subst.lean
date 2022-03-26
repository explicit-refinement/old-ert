import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp

def Stlc.InterpSubst (Γ Δ: Context): Type := 
  ∀{n A}, Stlc.HasVar Δ n A -> Γ.deriv A

def Stlc.InterpSubst.pop {H Γ Δ} (S: InterpSubst Γ (H::Δ))
  : InterpSubst Γ Δ
  := λHv => S Hv.succ

def Stlc.SubstCtx.interp {σ Γ Δ} (S: SubstCtx σ Γ Δ)
  : Stlc.InterpSubst Γ Δ
  := λHv => (S Hv).interp
  
def Stlc.SubstCtx.pop_interp {σ Γ Δ H} (S: SubstCtx σ Γ (H::Δ))
  : @Stlc.InterpSubst.pop H Γ Δ (Stlc.SubstCtx.interp S)
  = @Stlc.SubstCtx.interp (λn => σ n.succ) Γ Δ (Stlc.SubstCtx.pop S)
  := sorry

def Stlc.InterpSubst.transport_ctx {Γ Δ: Context} (S: InterpSubst Γ Δ) 
  (G: Γ.interp)
  : Δ.interp
  := match Δ with
     | [] => ()
     | A::Δ => (S HasVar.zero G, transport_ctx S.pop G)

def Stlc.Context.deriv.subst {Γ Δ: Context} {A} (D: Δ.deriv A) (S: InterpSubst Γ Δ)
  : Γ.deriv A
  := λG => D (S.transport_ctx G)

def Stlc.HasType.subst_var {Γ Δ σ A n}
  (H: Stlc.HasType Δ (Stlc.var n) A)
  (S: SubstCtx σ Γ Δ)
  : H.subst S = S H.has_var
  := rfl

def Stlc.HasVar.subst_interp_dist {Γ Δ σ A n}
  (Hv: HasVar Δ n A)
  (S: SubstCtx σ Γ Δ)
  (H: HasType Γ (σ n) A)
  (G: Γ.interp)
  : H.interp G = Hv.interp (Stlc.InterpSubst.transport_ctx S.interp G)
  := by {
    revert Γ Δ σ A Hv S H G;
    induction n with
    | zero =>
      intro Γ Δ σ A Hv S H G;
      cases Δ <;> cases Hv <;> rfl
    | succ n I =>
      intro Γ Δ σ A Hv S H G;
      cases Δ with
      | nil => cases Hv
      | cons B Δ =>
        cases Hv with
        | succ Hv =>
          simp only [HasVar.interp, InterpSubst.transport_ctx]
          rw [S.pop_interp]
          apply I Hv S.pop
  }

def Stlc.HasType.subst_interp_dist {Γ Δ σ A a} 
  (H: HasType Δ a A) 
  (S: SubstCtx σ Γ Δ)
  : (H.subst S).interp = H.interp.subst S.interp
  := by {
    revert σ Γ S;
    induction H <;> intro Γ σ S <;> funext G;

    case var Hv =>
     rw [Stlc.HasType.subst_var (var Hv) S]
     simp only [Context.deriv.subst]
     simp only [HasType.interp]
     rw [Stlc.HasVar.subst_interp_dist]

    case app =>
      simp only [
        HasType.interp
      ]
      sorry

    all_goals sorry
  }