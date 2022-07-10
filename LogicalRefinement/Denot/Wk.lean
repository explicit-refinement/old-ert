import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc
import LogicalRefinement.Denot.Basic

open AnnotSort
open Annot

theorem HasType.wk_eq
  {Γ Δ: Context} {ρ} {A: Term} {a s} 
  {G: Γ.upgrade.stlc.interp}
  (HΓ: Δ ⊢ A: sort s)
  (R: WkCtx ρ Γ.upgrade Δ.upgrade)
  : (A.wk ρ).denote_ty G a = A.denote_ty (G.wk R.stlc) (A.stlc_ty_wk ρ ▸ a)
  := by {
    generalize HS: sort s = S;
    rw [HS] at HΓ;
    induction HΓ generalizing ρ Γ s with
    | @pi Δ' A B _ _ IA IB =>
      cases a with
      | none => rw [interp_eq_none] rfl
      | some a => 
        rw [interp_eq_some]
        dsimp only [Term.denote_ty]
        apply forall_helper_dep (by rw [Term.stlc_ty_wk]);
        {
          intro x;
          apply arrow_equivalence;
          {
            rw [IA R rfl]
            rw [rec_to_cast']
            rw [rec_to_cast']
          }
          {
            rw[
              @IB 
              ((Hyp.mk _ (HypKind.val type))::Γ)
              _ _ _ (x, G) R.lift rfl
            ];            
            apply congr (congr rfl _) _;
            {
              rw [<-Stlc.Context.interp.wk_lift]
              let Δ'' := Term.stlc_ty A :: Context.stlc (Context.upgrade Δ');
              let f: 
                (Γ: Stlc.Context) -> Γ.interp 
                -> Stlc.WkCtx ρ.lift Γ Δ'' -> (Stlc.Context.interp Δ'')
                := λΓ => @Stlc.Context.interp.wk Γ Δ'' ρ.lift;
              have Hf: ∀Γ, @Stlc.Context.interp.wk Γ Δ'' ρ.lift = f Γ 
                := by intros; rfl;
              rw [Hf]
              rw [Hf]
              apply cast_app_dep_two f;
              rfl
              {
                simp only [
                  Context.upgrade, Hyp.upgrade, A.stlc_ty_wk, Context.stlc
                ]
              }
              {
                rw [cast_pair']
                {
                  {
                    apply congr (congr rfl _) rfl;
                    rw [A.stlc_ty_wk]
                    rw [rec_to_cast']
                    rw [cast_merge]
                    rfl
                  }
                }
                rfl
              }
            }
            {
              rw [rec_to_cast']
              rw [rec_to_cast']
              rw [rec_to_cast']
              rw [cast_bind]
              rw [Term.stlc_ty_wk]
              rw [Term.stlc_ty_wk]
            }
          }
        }
    | @sigma Δ' A B _ _ IA IB =>
      cases a with
      | none => rw [interp_eq_none] rfl
      | some a => 
        rw [interp_eq_some]
        cases a with
        | mk a b =>
          rw [rec_to_cast']
          rw [cast_pair' (by rw [Term.stlc_ty_wk]) (by rw [Term.stlc_ty_wk])]
          dsimp only [Term.denote_ty, pure]
          apply congr (congr rfl _) _;
          {
            rw [IA R rfl]
            rw [interp_eq_some]
            rw [rec_to_cast']
          }
          {
            rw [@IB
              ((Hyp.mk _ (HypKind.val type))::Γ)
              _ _ _ 
              (some a, G) R.lift rfl];
            apply congr (congr rfl _) _;
            {
              rw [<-Stlc.Context.interp.wk_lift]
              let Δ'' := Term.stlc_ty A :: Context.stlc (Context.upgrade Δ');
              let f: 
                (Γ: Stlc.Context) -> Γ.interp 
                -> Stlc.WkCtx ρ.lift Γ Δ'' -> (Stlc.Context.interp Δ'')
                := λΓ => @Stlc.Context.interp.wk Γ Δ'' ρ.lift;
              have Hf: ∀Γ, @Stlc.Context.interp.wk Γ Δ'' ρ.lift = f Γ 
                := by intros; rfl;
              rw [Hf]
              rw [Hf]
              apply cast_app_dep_two f;
              rfl
              {
                simp only [
                  Context.upgrade, Hyp.upgrade, A.stlc_ty_wk, Context.stlc
                ]
              }
              {
                rw [cast_pair']
                {
                  {
                    apply congr (congr rfl _) rfl;
                    rw [A.stlc_ty_wk]
                    rw [cast_some]
                    apply congr rfl;
                    rw [cast_merge]
                    rfl
                    rw [A.stlc_ty_wk]
                  }
                }
                rfl
              }
            }
            {
              rw [interp_eq_some]
              rw [rec_to_cast']
            }
          }
    | coprod _ _ IA IB => 
      cases a with
      | none => rw [interp_eq_none] rfl
      | some a => 
        cases a with
        | inl a => 
          dsimp only [Term.denote_ty];
          rw [IA R rfl]; 
          rw [interp_eq_some]
          rw [rec_to_cast']
          rw [rec_to_cast']
          rw [cast_inl']
          simp only []
          apply congr rfl;
          simp only [pure]
          rw [cast_some]
          rw [Term.stlc_ty_wk]
          rw [Term.stlc_ty_wk]
        | inr a => 
          dsimp only [Term.denote_ty]; 
          rw [IB R rfl]; 
          rw [interp_eq_some]
          rw [rec_to_cast']
          rw [rec_to_cast']
          rw [cast_inr']
          simp only []
          apply congr rfl;
          simp only [pure]
          rw [cast_some]
          rw [Term.stlc_ty_wk]
          rw [Term.stlc_ty_wk]
    | @assume Δ' A B _ _ IA IB => 
      cases a with
      | none => rw [interp_eq_none] rfl
      | some a => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_some]
        apply arrow_equivalence;
        {
          rw [IA R rfl];
          rw [interp_eq_none]
        }
        {
          rw [@IB 
            ((Hyp.mk _ (HypKind.val prop))::Γ) 
            _ _ _ (none, G) R.lift rfl];
          apply congr (congr rfl _) _;
          {
            rw [<-Stlc.Context.interp.wk_lift]
            let Δ'' := Term.stlc_ty A :: Context.stlc (Context.upgrade Δ');
            let f: 
              (Γ: Stlc.Context) -> Γ.interp 
              -> Stlc.WkCtx ρ.lift Γ Δ'' -> (Stlc.Context.interp Δ'')
              := λΓ => @Stlc.Context.interp.wk Γ Δ'' ρ.lift;              
              have Hf: ∀Γ, @Stlc.Context.interp.wk Γ Δ'' ρ.lift = f Γ 
                := by intros; rfl;              
              rw [Hf]
              rw [Hf]
              apply cast_app_dep_two f;
              rfl
              {
                simp only [
                  Context.upgrade, Hyp.upgrade, A.stlc_ty_wk, Context.stlc
                ]
              }
              {
                rw [cast_pair']
                apply congr (congr rfl _) rfl;
                rw [A.stlc_ty_wk]
                rw [cast_none]
                rw [A.stlc_ty_wk]
                rfl
              }
          }
          {
            rw [rec_to_cast']
            rw [rec_to_cast']
            rw [cast_app_pull_in]
          }
        }
    | @set Δ' A B _ _ IA IB => 
      dsimp only [Term.denote_ty]
      dsimp only [Term.stlc_ty] at a;
      apply congr (congr rfl _) _;
      . apply IA <;> assumption
      {
        rw [@IB
          ((Hyp.mk _ (HypKind.val type))::Γ) 
          _ _ _ (_, G) R.lift rfl]
        apply congr (congr rfl _) _;
        {
          rw [<-Stlc.Context.interp.wk_lift]
          let Δ'' := Term.stlc_ty A :: Context.stlc (Context.upgrade Δ');
          let f: 
            (Γ: Stlc.Context) -> Γ.interp 
            -> Stlc.WkCtx ρ.lift Γ Δ'' -> (Stlc.Context.interp Δ'')
            := λΓ => @Stlc.Context.interp.wk Γ Δ'' ρ.lift;              
            have Hf: ∀Γ, @Stlc.Context.interp.wk Γ Δ'' ρ.lift = f Γ 
              := by intros; rfl;              
            rw [Hf]
            rw [Hf]
            apply cast_app_dep_two f;
            rfl
            {
              simp only [
                Context.upgrade, Hyp.upgrade, A.stlc_ty_wk, Context.stlc
              ]
              rfl
            }
            {
              rw [cast_pair']
              apply congr (congr rfl _) rfl;
              rw [A.stlc_ty_wk]
              rfl
              rw [rec_to_cast']
              rw [cast_merge]
              rfl
              rfl
            }
        }
        rw [interp_eq_none]
      }
    | @intersect Δ' A B _ _ IA IB =>
      cases a with
      | none => rw [interp_eq_none] rfl
      | some a => 
        rw [interp_eq_some]
        dsimp only [Term.denote_ty]
        apply forall_helper_dep (by rw [Term.stlc_ty_wk]);
        intro x;
        apply arrow_equivalence;
        {
          rw [IA R rfl]
          rw [rec_to_cast']
          rw [rec_to_cast']
        }
        {
          rw [@IB 
            ((Hyp.mk _ (HypKind.val type))::Γ) 
            _ _ _ (x, G) R.lift rfl];            
          apply congr (congr rfl _) _;
          {
            rw [<-Stlc.Context.interp.wk_lift]
            let Δ'' := Term.stlc_ty A :: Context.stlc (Context.upgrade Δ');
            let f: 
              (Γ: Stlc.Context) -> Γ.interp 
              -> Stlc.WkCtx ρ.lift Γ Δ'' -> (Stlc.Context.interp Δ'')
              := λΓ => @Stlc.Context.interp.wk Γ Δ'' ρ.lift;
            have Hf: ∀Γ, @Stlc.Context.interp.wk Γ Δ'' ρ.lift = f Γ 
              := by intros; rfl;
            rw [Hf]
            rw [Hf]
            apply cast_app_dep_two f;
            rfl
            {
              simp only [
                Context.upgrade, Hyp.upgrade, A.stlc_ty_wk, Context.stlc
              ]
            }
            {
              rw [cast_pair']
              {
                {
                  apply congr (congr rfl _) rfl;
                  rw [A.stlc_ty_wk]
                  rw [rec_to_cast']
                  rw [cast_merge]
                  rfl
                }
              }
              rfl
            }
          }
          {
            rw [rec_to_cast']
            rw [rec_to_cast']
            rw [cast_app_pull_in]
          }
        }
    | @union Δ' A B _ _ IA IB =>
      dsimp only [Term.denote_ty]
      simp only [pure]
      apply congr (congr rfl _) _;
      {
        --TODO: clean this mess up...
        simp only [Ne]
        apply arrow_equivalence _ rfl;
        apply propext; apply Iff.intro;
        {
          intro Ha; rw [Ha]; exact interp_eq_none
        }
        {
          intro Ha;
          cases a with
          | none => rfl
          | some a => rw [interp_eq_some] at Ha; contradiction
        }
      }
      {
        apply existential_forall_helper_dep (by rw [Term.stlc_ty_wk]);
        intro x;
        apply congr (congr rfl _) _;
        {
          rw [IA R rfl]
          rw [rec_to_cast']
          rw [rec_to_cast']
        }
        {
          rw [@IB 
            ((Hyp.mk _ (HypKind.val type))::Γ) 
            _ _ _ (x, G) R.lift rfl];            
          apply congr (congr rfl _) rfl;
          rw [<-Stlc.Context.interp.wk_lift]
          let Δ'' := Term.stlc_ty A :: Context.stlc (Context.upgrade Δ');
          let f: 
            (Γ: Stlc.Context) -> Γ.interp 
            -> Stlc.WkCtx ρ.lift Γ Δ'' -> (Stlc.Context.interp Δ'')
            := λΓ => @Stlc.Context.interp.wk Γ Δ'' ρ.lift;
          have Hf: ∀Γ, @Stlc.Context.interp.wk Γ Δ'' ρ.lift = f Γ 
            := by intros; rfl;
          rw [Hf]
          rw [Hf]
          apply cast_app_dep_two f;
          rfl
          {
            simp only [
              Context.upgrade, Hyp.upgrade, A.stlc_ty_wk, Context.stlc
            ]
          }
          {
            rw [cast_pair']
            {
              {
                apply congr (congr rfl _) rfl;
                rw [A.stlc_ty_wk]
                rw [rec_to_cast']
                rw [cast_merge]
                rfl
              }
            }
            rfl
          }
        }
      }
    | @dimplies Δ' A B _ _ IA IB => 
      dsimp only [Term.denote_ty]
      apply arrow_equivalence;
      {
        rw [IA R rfl]
        rw [interp_eq_none]
      }
      {
        rw [@IB 
          ((Hyp.mk _ (HypKind.val prop))::Γ) 
          _ _ _ (none, G) R.lift rfl];
        apply congr (congr rfl _) _;
        {
          rw [<-Stlc.Context.interp.wk_lift]
          let Δ'' := Term.stlc_ty A :: Context.stlc (Context.upgrade Δ');
          let f: 
            (Γ: Stlc.Context) -> Γ.interp 
            -> Stlc.WkCtx ρ.lift Γ Δ'' -> (Stlc.Context.interp Δ'')
            := λΓ => @Stlc.Context.interp.wk Γ Δ'' ρ.lift;
          have Hf: ∀Γ, @Stlc.Context.interp.wk Γ Δ'' ρ.lift = f Γ 
            := by intros; rfl;
          rw [Hf]
          rw [Hf]
          apply cast_app_dep_two f;
          rfl
          {
            simp only [
              Context.upgrade, Hyp.upgrade, A.stlc_ty_wk, Context.stlc
            ]
          }
          {
            rw [cast_pair']
            {
              {
                apply congr (congr rfl _) rfl;
                rw [A.stlc_ty_wk]
                rw [cast_none]
                rw [A.stlc_ty_wk]
              }
            }
            rfl
          }
        }
        rw [interp_eq_none]
      }
    | @dand Δ' A B _ _ IA IB => 
      dsimp only [Term.denote_ty]
      simp only [pure]
      apply congr (congr rfl _) _;
      {
        rw [IA R rfl]
        rw [interp_eq_none]
      }
      {
        rw[@IB 
          ((Hyp.mk _ (HypKind.val prop))::Γ) 
          _ _ _ (none, G) R.lift rfl]
        apply congr (congr rfl _) _;
        {
          rw [<-Stlc.Context.interp.wk_lift]
          let Δ'' := Term.stlc_ty A :: Context.stlc (Context.upgrade Δ');
          let f: 
            (Γ: Stlc.Context) -> Γ.interp 
            -> Stlc.WkCtx ρ.lift Γ Δ'' -> (Stlc.Context.interp Δ'')
            := λΓ => @Stlc.Context.interp.wk Γ Δ'' ρ.lift;
          have Hf: ∀Γ, @Stlc.Context.interp.wk Γ Δ'' ρ.lift = f Γ 
            := by intros; rfl;
          rw [Hf]
          rw [Hf]
          apply cast_app_dep_two f;
          rfl
          {
            simp only [
              Context.upgrade, Hyp.upgrade, A.stlc_ty_wk, Context.stlc
            ]
          }
          {
            rw [cast_pair']
            {
              {
                apply congr (congr rfl _) rfl;
                rw [A.stlc_ty_wk]
                rw [cast_none]
                rw [A.stlc_ty_wk]
              }
            }
            rfl
          }
        }
        rw [interp_eq_none]
      }
    | or _ _ IA IB =>
      dsimp only [Term.denote_ty]
      rw [IA R rfl]
      rw [interp_eq_none]
      rw [IB R rfl]
      rw [interp_eq_none]
    | @forall_ Δ' A B _ _ IA IB => 
      dsimp only [Term.denote_ty]
      apply forall_helper_dep (by rw [Term.stlc_ty_wk]);
      intro x;
      apply arrow_equivalence;
      {
        rw [IA R rfl]
        rw [rec_to_cast']
        rw [rec_to_cast']
      }
      {
        rw [@IB 
          ((Hyp.mk _ (HypKind.val type))::Γ) 
          _ _ _ (x, G) R.lift rfl];
        apply congr (congr rfl _) _;
        {
          rw [<-Stlc.Context.interp.wk_lift]
          let Δ'' := Term.stlc_ty A :: Context.stlc (Context.upgrade Δ');
          let f: 
            (Γ: Stlc.Context) -> Γ.interp 
            -> Stlc.WkCtx ρ.lift Γ Δ'' -> (Stlc.Context.interp Δ'')
            := λΓ => @Stlc.Context.interp.wk Γ Δ'' ρ.lift;
          have Hf: ∀Γ, @Stlc.Context.interp.wk Γ Δ'' ρ.lift = f Γ 
            := by intros; rfl;
          rw [Hf]
          rw [Hf]
          apply cast_app_dep_two f;
          rfl
          {
            simp only [
              Context.upgrade, Hyp.upgrade, A.stlc_ty_wk, Context.stlc
            ]
          }
          {
            rw [cast_pair']
            {
              {
                apply congr (congr rfl _) rfl;
                rw [A.stlc_ty_wk]
                rw [rec_to_cast']
                rw [cast_merge]
                rfl
              }
            }
            rfl
          }
        }
        {
          rw [interp_eq_none]
        }
      }
    | @exists_ Δ' A B _ _ IA IB => 
      dsimp only [Term.denote_ty]
      simp only [pure]
      apply existential_forall_helper_dep (by rw [Term.stlc_ty_wk]);
      intro x;
      apply congr (congr rfl _) _;
      {
        rw [IA R rfl]
        rw [rec_to_cast']
        rw [rec_to_cast']
      }
      {
        rw [@IB 
          ((Hyp.mk _ (HypKind.val type))::Γ) 
          _ _ _ (x, G) R.lift rfl];            
        apply congr (congr rfl _) _;
        {
          rw [<-Stlc.Context.interp.wk_lift]
          let Δ'' := Term.stlc_ty A :: Context.stlc (Context.upgrade Δ');
          let f: 
            (Γ: Stlc.Context) -> Γ.interp 
            -> Stlc.WkCtx ρ.lift Γ Δ'' -> (Stlc.Context.interp Δ'')
            := λΓ => @Stlc.Context.interp.wk Γ Δ'' ρ.lift;
          have Hf: ∀Γ, @Stlc.Context.interp.wk Γ Δ'' ρ.lift = f Γ 
            := by intros; rfl;
          rw [Hf]
          rw [Hf]
          apply cast_app_dep_two f;
          rfl
          {
            simp only [
              Context.upgrade, Hyp.upgrade, A.stlc_ty_wk, Context.stlc
            ]
          }
          {
            rw [cast_pair']
            {
              {
                apply congr (congr rfl _) rfl;
                rw [A.stlc_ty_wk]
                rw [rec_to_cast']
                rw [cast_merge]
                rfl
              }
            }
            rfl
          }
        }
        {
          rw [interp_eq_none]
        }
      }
    | eq _ Hl Hr =>
      dsimp only [Term.denote_ty]
      apply propext;
      apply Iff.intro;
      {
        intro ⟨Hl', Hr', HG⟩;
        exists Hl.stlc, Hr.stlc;
        --TODO: report this "this pattern is a metavariable" trash
        rw [<-Hl.stlc.wk_def]
        rw [<-Hr.stlc.wk_def]
        rw [HasType.wk_stlc_interp_commute]
        rw [HasType.wk_stlc_interp_commute]
        rw [rec_to_cast']
        rw [rec_to_cast']
        apply congr rfl HG;
        assumption
        assumption
        assumption
        assumption
      }
      {
        intro ⟨Hl', Hr', HG⟩;
        exists (Hl.wk R).stlc, (Hr.wk R).stlc;
        rw [Hl.wk_stlc_interp_commute_cast_erased Hl']
        rw [Hr.wk_stlc_interp_commute_cast_erased Hr']
        rw [rec_to_cast']
        rw [rec_to_cast']
        apply congr rfl HG;
        assumption
        assumption
      }
    | _ => cases HS <;> rfl
  }


theorem HasType.wk_eq'
  {Γ Δ: Context} {ρ} {A A': Term} {a a' s} 
  {G: Γ.upgrade.stlc.interp}
  {D: Δ.upgrade.stlc.interp}
  (HΓ: Δ ⊢ A: sort s)
  (R: WkCtx ρ Γ.upgrade Δ.upgrade)
  (HAA': A' = A.wk ρ)
  (Haa': a' = A.stlc_ty_wk ρ ▸ HAA' ▸ a)
  (HD: D = G.wk R.stlc)
  : A'.denote_ty G a 
  = A.denote_ty D a'
  := by {
    cases HAA';
    cases HD;
    rw [Haa']
    rw [HΓ.wk_eq]
    exact R
  }

--TODO: move to HasType...
theorem HasType.denote_wk1_eq
  {Γ: Context}  {A B: Term}  {s}
  (HΓ: Γ ⊢ A: sort s)
  (x: Option B.stlc_ty.interp) 
  (G: Γ.upgrade.stlc.interp)
  (a: Option A.stlc_ty.interp)
  (a': Option A.wk1.stlc_ty.interp)
  (Haa': a' = (A.stlc_ty_wk Wk.wk1) ▸ a)
  : A.denote_ty G a 
  = @Term.denote_ty A.wk1 (B.stlc_ty::Γ.upgrade.stlc) (x, G) a'
  := by {
    rw [
      <-@HasType.wk_eq' ((Hyp.mk B (HypKind.val type))::Γ) Γ Wk.wk1 _ _ _ _ _
      _ _ HΓ WkCtx.wk1 rfl
    ]
    rw [Haa']
    rfl
    simp only [rec_to_cast', cast_merge]
    rfl
    simp only [Wk.wk1]
    rw [Stlc.Context.interp.wk_wk1]
  }

theorem HasType.denote_wk1
  {Γ: Context}  {A B: Term}  {s}
  (HΓ: Γ ⊢ A: sort s)
  (x: Option B.stlc_ty.interp) 
  (G: Γ.upgrade.stlc.interp) 
  (a: Option A.stlc_ty.interp)
  (a': Option A.wk1.stlc_ty.interp)
  (Haa': a' = A.stlc_ty_wk1 ▸ a)
  (H: A.denote_ty G a) 
  : @Term.denote_ty A.wk1 (B.stlc_ty::Γ.upgrade.stlc) (x, G) a'
  := by {
    rw [denote_wk1_eq] at H;
    exact H;
    exact HΓ;
    exact Haa';
  }

theorem cast_bin_cast_helper
  {A} {B: A -> Type} {C: (a: A) -> B a -> Type}
  (f: (a: A) -> (b: B a) -> C a b)
  (a a' b b')
  (Ha: a = a')
  (Hb: b = Ha ▸ b')
  (H: C a b = C a' b'):
  cast H (f a b) = f a' b'
  := by {
    cases Ha;
    cases Hb;
    rfl
  }

theorem HasType.denote_wk2_eq
  {Γ: Context}  {A B X: Term}  {s k}
  (HA: HasType ((Hyp.mk B k)::Γ) A (sort s))
  (b: Option B.wk1.stlc_ty.interp) 
  (x: Option X.stlc_ty.interp) 
  (G: Γ.upgrade.stlc.interp)
  (a: Option A.stlc_ty.interp)
  (a': Option (A.wknth 1).stlc_ty.interp)
  (Haa': a' = (A.stlc_ty_wk (Wk.wknth 1)) ▸ a)
  : @Term.denote_ty A (B.stlc_ty::Γ.upgrade.stlc) (B.stlc_ty_wk _ ▸ b, G) a 
  = @Term.denote_ty (A.wknth 1) (B.wk1.stlc_ty::X.stlc_ty::Γ.upgrade.stlc) (b, x, G) a'
  := by {
    simp only [Term.wknth]
    cases k with
    | val s => sorry
    | gst =>
      rw [
        <-@HasType.wk_eq' 
        ((Hyp.mk (B.wk1) HypKind.gst)::(Hyp.mk X (HypKind.val type))::Γ) 
        ((Hyp.mk B HypKind.gst)::Γ) 
        (Wk.wknth 1) _ _ _ _ _
        (b, x, G) _ HA (by repeat constructor) rfl
      ]
      rw [Haa']
      simp only [rec_to_cast', cast_merge]
      rfl
      simp only [Context.stlc, Context.upgrade, Term.stlc_ty_wk, Term.wk1]
      have He := Stlc.Context.interp.wk_wk2 G x (B.stlc_ty_wk _ ▸ b) (by repeat constructor);
      apply Eq.trans He.symm _;
      let f := λB' b => @Stlc.Context.interp.wk 
        (B'::X.stlc_ty::Γ.upgrade.stlc) 
        (B'::Γ.upgrade.stlc) 
        (Wk.wknth 1) (b, x, G)
        (by repeat constructor);
      have R: Stlc.WkCtx (Wk.wknth 1)
        (Context.stlc
          (Context.upgrade ({ ty := Term.wk1 B, kind := HypKind.gst } :: { ty := X, kind := HypKind.val type } :: Γ)))
        (Context.stlc (Context.upgrade ({ ty := B, kind := HypKind.gst } :: Γ))) 
        := by { 
          simp only [Context.upgrade, Context.stlc, Term.stlc_ty_wk1]; 
          repeat constructor
        };
      stop
      have Hfl: Stlc.Context.interp.wk (b, x, G) R = f B.stlc_ty (B.stlc_ty_wk _ ▸ b) := by {
        simp only []
      }
      have Hf: B.stlc_ty_wk _ ▸ f B.wk1.stlc_ty b = f B.stlc_ty (B.stlc_ty_wk _ ▸ b) := by {
        rw [rec_to_cast']
        rw [rec_to_cast']
        rw [cast_bin_cast_helper f B.wk1.stlc_ty]
        rw [Term.stlc_ty_wk1]
        simp only [rec_to_cast', cast_merge]
        rfl
      }
      rw [<-Hf]
  }
