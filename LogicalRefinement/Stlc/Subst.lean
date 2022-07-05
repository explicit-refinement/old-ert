import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Stlc.Interp

def Stlc.InterpSubst (Γ Δ: Context): Type := 
  ∀n A, Stlc.HasVar Δ n A -> Γ.deriv A

def Stlc.InterpSubst.id {Γ}: InterpSubst Γ Γ
  := λ_ _ Hv => Hv.interp

def Stlc.InterpSubst.pop {H Γ Δ} (S: InterpSubst Γ (H::Δ))
  : InterpSubst Γ Δ
  := λ_ _ Hv => S _ _ Hv.succ

--TODO: report spurious unused variable warning...
def Stlc.InterpSubst.lift {H Γ Δ} (S: InterpSubst Γ Δ)
  : InterpSubst (H::Γ) (H::Δ)
  := λ n A Hv G =>
    match n with
    | 0 => 
      have P: A = H := by cases Hv; rfl;
      P ▸ HasVar.zero.interp G
    | n + 1 =>
      let (_, G) := G;
      S _ _ (by cases Hv; assumption) G

def Stlc.InterpSubst.lift2 {A B Γ Δ} (S: InterpSubst Γ Δ)
  : InterpSubst (A::B::Γ) (A::B::Δ)
  := lift S.lift

def Stlc.InterpSubst.step {H Γ Δ} (S: InterpSubst Γ Δ)
  : InterpSubst (H::Γ) Δ
  := λ_ _ Hv => (S _ _ Hv).step H

theorem Stlc.InterpSubst.lift_id {H Γ}:
  (@id Γ).lift = @id (H::Γ)
  := by {
    funext n A Hv;
    cases Hv <;> rfl 
  }

theorem Stlc.InterpSubst.pop_lift_step {H Γ Δ} (S: InterpSubst Γ Δ)
  : @pop H (H::Γ) Δ (@lift H Γ Δ S) = @step H Γ Δ S
  := by {
    funext n A Hv G;
    cases G;
    rfl
  }

theorem Stlc.InterpSubst.pop_step_commute {A B Γ Δ} 
  (S: InterpSubst Γ (A::Δ))
  : @step B Γ Δ (@pop A Γ Δ S) = @pop A (B::Γ) Δ (@step B Γ (A::Δ) S)
  := by {
    funext n A Hv G;
    cases G;
    rfl
  }

def Stlc.SubstCtx.interp {σ Γ Δ} (S: SubstCtx σ Γ Δ)
  : Stlc.InterpSubst Γ Δ
  := λ_ _ Hv => (S Hv).interp
  
theorem Stlc.SubstCtx.pop_interp {σ Γ Δ H} (S: SubstCtx σ Γ (H::Δ))
  : @Stlc.InterpSubst.pop H Γ Δ S.interp
  = @Stlc.SubstCtx.interp (λn => σ n.succ) Γ Δ S.pop
  := by {
    funext n;
    cases n <;>
    funext _ _ <;>
    simp only [InterpSubst.pop, SubstCtx.interp]
  }

theorem Stlc.SubstCtx.lift_interp {σ Γ Δ H} (S: SubstCtx σ Γ Δ)
  : @Stlc.SubstCtx.interp σ.lift (H::Γ) (H::Δ) S.lift
  = @Stlc.InterpSubst.lift H Γ Δ S.interp
  := by {
    funext n;
    cases n with
    | zero => 
      funext _ Hv _;
      cases Hv;
      rfl
    | succ n => 
      funext _ _ G;
      cases G with
      | mk x G =>
        simp only [InterpSubst.lift]
        apply Stlc.HasType.interp_wk1
  }
  
theorem Stlc.SubstCtx.lift2_interp {σ Γ Δ A B} (S: SubstCtx σ Γ Δ)
  : @Stlc.SubstCtx.interp (σ.liftn 2) (A::B::Γ) (A::B::Δ) S.lift2
  = @Stlc.InterpSubst.lift2 A B Γ Δ S.interp
  := by {
    simp only [InterpSubst.lift2]
    rw [<-lift_interp]
    rw [<-lift_interp]
    rfl
  }

--TODO: report spurious unused variable warning
def Stlc.InterpSubst.transport_ctx {Γ Δ: Context} (S: InterpSubst Γ Δ) 
  (G: Γ.interp)
  : Δ.interp
  := match Δ with
     | [] => ()
     | _::_ => (S 0 _ HasVar.zero G, transport_ctx S.pop G)

theorem Stlc.InterpSubst.transport_cast {Γ Δ Γ': Context} 
  (S: InterpSubst Γ' Δ)
  (HΓ: Γ' = Γ)
  (G: Γ.interp)
  : (@cast _ (InterpSubst Γ Δ) (by rw [HΓ]) S).transport_ctx G
  = S.transport_ctx (cast (by rw [HΓ]) G)
  := by {
    cases HΓ; rfl
  }

def second_helper {a a': A} {f: A -> B}: a = a' -> f a = f a' := by intros; simp [*]
def pair_helper: a = a' -> b = b' -> (a, b) = (a', b') := by intros; simp [*]
theorem Stlc.InterpSubst.transport_helper {Γ Δ: Context} {H: Ty} 
  (S: InterpSubst Γ (H::Δ))
  (G: Γ.interp)
  : S.transport_ctx G = (S 0 _ HasVar.zero G, transport_ctx S.pop G)
  := by rfl

def Stlc.InterpSubst.transport_step {Γ Δ: Context} {H: Ty} (S: InterpSubst Γ Δ)
  (G: Γ.interp) (x: Option H.interp)
  : transport_ctx (@InterpSubst.step H Γ Δ S) (x, G)
  = S.transport_ctx G
  := by {
    revert Γ H;
    induction Δ with
    | nil => intros; rfl
    | cons B Δ I =>
      intro Γ H S G x;
      simp only [transport_ctx]
      apply pair_helper rfl;
      rw [<-pop_step_commute]
      apply I
  }
  
theorem Stlc.Context.interp.transport_id {Γ: Stlc.Context}
  (G: Γ.interp):
  Stlc.InterpSubst.id.transport_ctx G = G
  := by {
    induction Γ with
    | nil => rfl
    | cons H Γ I =>
      cases G with
      | mk x G =>
        simp only [InterpSubst.transport_ctx]
        apply congr rfl _;
        rw [<-Stlc.InterpSubst.lift_id]
        rw [Stlc.InterpSubst.pop_lift_step]
        rw [Stlc.InterpSubst.transport_step]
        exact I G
  }

def Stlc.InterpSubst.transport_pop_lift {Γ Δ: Context} {H: Ty} (S: InterpSubst Γ Δ)
  (G: Γ.interp) (x: Option H.interp)
  : transport_ctx (@InterpSubst.lift H Γ Δ S).pop (x, G) 
  = S.transport_ctx G
  := by {
    rw [pop_lift_step]
    apply transport_step
  }

theorem Stlc.InterpSubst.pop_cast {Γ Δ Γ' Δ': Context}
  (H H': Ty)
  (S: InterpSubst Γ' (H'::Δ'))
  (HΓ: Γ = Γ')
  (HΔ: Δ = Δ')
  (HH: H = H')
  : InterpSubst.pop 
    (@cast (InterpSubst Γ' (H'::Δ')) (InterpSubst Γ (H::Δ)) (by rw [HΓ, HΔ, HH]) S) 
  = @cast (InterpSubst Γ' Δ') (InterpSubst Γ Δ) (by rw [HΓ, HΔ]) (S.pop)
  := by {
    cases HΓ; cases HΔ; cases HH;
    rfl
  }
  
  theorem Stlc.InterpSubst.pop_cast' {Γ Δ Γ' Δ': Context}
  (H H': Ty)
  (S: InterpSubst Γ' (H'::Δ'))
  (HΓ: Γ = Γ')
  (HΔ: Δ = Δ')
  (HH: H = H')
  (P)
  (P')
  : InterpSubst.pop 
    (@cast (InterpSubst Γ' (H'::Δ')) (InterpSubst Γ (H::Δ)) P S) 
  = @cast (InterpSubst Γ' Δ') (InterpSubst Γ Δ) P' (S.pop)
  := by {
    rw [pop_cast] <;> assumption
  }

theorem Stlc.InterpSubst.transport_lift {Γ Δ: Context} {H: Ty} (S: InterpSubst Γ Δ)
  (G: Γ.interp) (x: Option H.interp)
  : transport_ctx (Stlc.InterpSubst.lift S) (x, G) = (x, S.transport_ctx G)
  := by {
    simp only [transport_ctx]
    apply pair_helper rfl;
    apply transport_pop_lift
  }
  
theorem Stlc.InterpSubst.transport_lift2 {Γ Δ: Context} {A B: Ty} (S: InterpSubst Γ Δ)
  (G: Γ.interp) (a: Option A.interp) (b: Option B.interp)
  : transport_ctx (Stlc.InterpSubst.lift2 S) (a, b, G) = (a, b, S.transport_ctx G)
  := by {
    simp only [transport_ctx]
    apply pair_helper rfl;
    apply pair_helper rfl;
    simp only [lift2]
    rw [pop_lift_step]
    rw [<-pop_step_commute]
    rw [transport_step]
    rw [transport_pop_lift]
  }

def Stlc.Context.deriv.subst {Γ Δ: Context} {A} (D: Δ.deriv A) (S: InterpSubst Γ Δ)
  : Γ.deriv A
  := λG => D (S.transport_ctx G)

theorem Stlc.Context.deriv.subst_lift {Γ Δ: Context} {A B} 
  (D: Context.deriv (B::Δ) A) 
  (S: InterpSubst Γ Δ)
  (x: Option B.interp)
  (G: Γ.interp)
  : D.subst S.lift (x, G) = D (x, S.transport_ctx G)
  := by {
    simp only [subst]
    rw [Stlc.InterpSubst.transport_lift]
  }
  
theorem Stlc.Context.deriv.subst_lift2 {Γ Δ: Context} {A B C} 
  (D: Context.deriv (B::C::Δ) A) 
  (S: InterpSubst Γ Δ)
  (b: Option B.interp)
  (c: Option C.interp)
  (G: Γ.interp)
  : D.subst S.lift2 (b, c, G) = D (b, c, S.transport_ctx G)
  := by {
    simp only [subst]
    rw [Stlc.InterpSubst.transport_lift2]
  }

theorem Stlc.HasType.subst_var {Γ Δ σ A n}
  (H: Stlc.HasType Δ (Stlc.var n) A)
  (S: SubstCtx σ Γ Δ)
  : H.subst S = S H.has_var
  := rfl

theorem Stlc.HasVar.subst_interp_dist {Γ Δ σ A n}
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

theorem Stlc.HasType.subst_interp_dist {Γ Δ σ A a} 
  (H: HasType Δ a A) 
  (S: SubstCtx σ Γ Δ)
  : (H.subst S).interp = H.interp.subst S.interp
  := by {
    revert σ Γ S;
    induction H <;> intro Γ σ S <;> funext G
    <;> try rfl;

    case var Hv =>
     rw [Stlc.HasType.subst_var (var Hv) S]
     simp only [Context.deriv.subst, HasType.interp]
     rw [Stlc.HasVar.subst_interp_dist]

    case lam Is =>
      simp only [interp, Context.deriv.subst]
      apply option_helper
      funext x;
      conv =>
        lhs
        rw [Is S.lift]
        rw [Stlc.SubstCtx.lift_interp S]
        rw [Stlc.Context.deriv.subst_lift]

    case app Il Ir =>
      simp only [interp, eq_mp_helper']
      rw [Il S, Ir S]
      rfl

    case let_in Ie Ie' => 
      simp only [interp, Context.deriv.subst]
      apply bind_helper;
      rw [Ie S]
      rfl
      funext x
      conv =>
        lhs
        rw [Ie' S.lift]
        rw [Stlc.SubstCtx.lift_interp S]
        rw [Stlc.Context.deriv.subst_lift]

    case pair Il Ir =>
      simp only [interp]
      rw [Il S, Ir S]
      rfl

    case let_pair Ie Ie' => 
      simp only [interp, Context.deriv.subst]
      apply let_pair_helper
      rw [Ie S]
      rfl
      funext a b
      conv =>
        lhs
        rw [Ie' S.lift2]
        rw [Stlc.SubstCtx.lift2_interp S]
        rw [Stlc.Context.deriv.subst_lift2]

    case inj0 Ie =>
      simp only [interp]
      rw [Ie S]
      rfl

    case inj1 Ie =>
      simp only [interp]
      rw [Ie S]
      rfl

    case case Id Il Ir => 
      simp only [interp, Context.deriv.subst]
      apply case_helper
      rw [Id S]
      rfl
      funext x
      conv =>
        lhs
        rw [Il S.lift]
        rw [Stlc.SubstCtx.lift_interp S]
        rw [Stlc.Context.deriv.subst_lift]
      funext x
      conv =>
        lhs
        rw [Ir S.lift]
        rw [Stlc.SubstCtx.lift_interp S]
        rw [Stlc.Context.deriv.subst_lift]

    case natrec In Iz Is => 
      simp only [interp, Context.deriv.subst]
      apply natrec_helper
      rw [In S]
      rfl
      rw [Iz S]
      rfl
      funext x
      conv =>
        lhs
        rw [Is S.lift2]
        rw [Stlc.SubstCtx.lift2_interp S]
        rw [Stlc.Context.deriv.subst_lift2]
  }

theorem Stlc.HasType.wk_interp_dist {Γ Δ ρ A a} 
  (H: HasType Δ a A) 
  (R: WkCtx ρ Γ Δ)
  : (H.wk R).interp = H.interp.wk R
  := sorry