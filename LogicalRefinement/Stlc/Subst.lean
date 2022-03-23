import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp

def Stlc.InterpSubst (Γ Δ: Context): Type := 
  ∀{n A}, Stlc.HasVar Δ n A -> Γ.deriv A

def Stlc.InterpSubst.pop {Γ Δ: Context} (S: InterpSubst Γ (H::Δ)): InterpSubst Γ Δ
  := λHv => S Hv.succ

def Stlc.SubstCtx.interp {σ: Subst} {Γ Δ: Context} (S: SubstCtx σ Γ Δ)
  : InterpSubst Γ Δ
  := λHv => (S Hv).interp
  
def Stlc.InterpSubst.transport_ctx {Γ Δ: Context} (S: InterpSubst Γ Δ) 
  (G: Γ.interp_effect)
  : Δ.interp_effect
  := match Δ with
     | [] => some ()
     | A::Δ => (transport_ctx S.pop G).push_effect ((S HasVar.zero).ctx_effect G)

def Stlc.InterpSubst.subst {Γ Δ: Context} (S: InterpSubst Γ Δ):
  ∀{A}, Δ.deriv A -> Γ.deriv A
  := λD G => D.ctx_effect (S.transport_ctx (some G))