import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp

def Stlc.InterpSubst (Γ Δ: Context): Type := 
  ∀{n A}, Stlc.HasVar Δ n A -> Γ.deriv A

def Stlc.InterpSubst.pop {Γ Δ: Context} (S: InterpSubst Γ (H::Δ)): InterpSubst Γ Δ
  := λHv => S Hv.succ

def Stlc.SubstCtx.interp
  {σ: Subst} 
  {Γ Δ: Context} 
  (S: SubstCtx σ Γ Δ)
  : Stlc.InterpSubst Γ Δ
  := λHv => (S Hv).interp
  
def Stlc.InterpSubst.transport_ctx {Γ Δ: Context} (S: InterpSubst Γ Δ) 
  (G: Γ.interp_effect)
  : Δ.interp_effect
  := match Δ with
     | [] => some ()
     | A::Δ => (transport_ctx S.pop G).push_effect ((S HasVar.zero).ctx_effect G)

def Stlc.Context.deriv.subst {Γ Δ: Context} {A} (D: Δ.deriv A) (S: InterpSubst Γ Δ)
  : Γ.deriv A
  := λG => D.ctx_effect (S.transport_ctx (some G))

def Stlc.HasType.subst_interp_dist {Γ Δ σ A a} (H: HasType Δ a A) (S: SubstCtx σ Γ Δ)
  : (H.subst S).interp = H.interp.subst S.interp
  := by {
    revert σ Γ S;
    induction H <;> intro Γ σ S <;> funext D;

    case var v =>
      simp only [
        HasType.interp,
        Stlc.subst
      ]
      sorry

    case app =>
      simp only [
        HasType.interp
      ]
      sorry

    all_goals sorry
  }