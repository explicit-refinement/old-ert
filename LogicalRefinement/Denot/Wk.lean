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
    | pi _ _ IA IB =>
      stop
      cases a with
      | none => rw [interp_eq_none] rfl
      | some a => 
        rw [interp_eq_some]
        dsimp only [Term.denote_ty]
        --TODO: generalized forall_helper
        stop
        apply forall_helper;
        intro x;
        apply arrow_equivalence;
        apply IA;
        assumption
        rfl
        rw[
          @IB 
          ((Hyp.mk _ (HypKind.val type))::Δ)
          _ _ _ (x, G) (x, D) R.lift rfl
        ];
        rfl
    | @sigma Δ' A B _ _ IA IB =>
      stop
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
      stop
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
      stop
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
    | intersect _ _ IA IB => 
      stop
      cases a with
      | none => rw [interp_eq_none] rfl
      | some a => 
        rw [interp_eq_some]
        dsimp only [Term.denote_ty]
        --TODO: generalized forall helper
        stop
        apply forall_helper;
        intro x;
        apply arrow_equivalence;
        apply IA;
        assumption
        rfl
        rw [@IB 
          ((Hyp.mk _ (HypKind.val type))::Δ) 
          _ _ _ (x, G) (x, D) R.lift];
        rfl
        rfl
    | union _ _ IA IB =>
      stop 
      dsimp only [Term.denote_ty]
      simp only [pure]
      apply congr (congr rfl _) _;
      . sorry
      {
        --TODO: generalized extential helper
        stop
        apply congr rfl _;
        funext x;
        apply congr (congr rfl _) _;
        apply IA;
        assumption
        rfl
        rw [@IB 
          ((Hyp.mk _ (HypKind.val type))::Δ) 
          _ _ _ (x, G) (x, D) R.lift];
        rfl
        rfl
      }
    | dimplies _ _ IA IB => 
      stop
      dsimp only [Term.denote_ty]
      apply arrow_equivalence;
      {
        rw [IA R rfl]
        sorry
      }
      {
        rw [@IB 
          ((Hyp.mk _ (HypKind.val prop))::Γ) 
          _ _ _ (none, G) R.lift rfl];
        sorry
      }
    | dand _ _ IA IB =>  
      stop
      dsimp only [Term.denote_ty]
      simp only [pure]
      apply congr (congr rfl _) _;
      {
        rw [IA R rfl]
        sorry
      }
      {
        rw[@IB 
          ((Hyp.mk _ (HypKind.val prop))::Γ) 
          _ _ _ (none, G) R.lift rfl]
        sorry
      }
    | or _ _ IA IB =>
      stop
      dsimp only [Term.denote_ty]
      apply congr (congr rfl _) _;
      {
        rw [IA R rfl]
        sorry
      }
      {
        rw [IB R rfl]
        sorry
      }
    | forall_ _ _ IA IB =>  
      stop
      dsimp only [Term.denote_ty]
      --TODO: generalized forall helper
      stop
      apply forall_helper;
      intro x;
      apply arrow_equivalence;
      apply IA;
      assumption
      rfl
      rw [@IB 
        ((Hyp.mk _ (HypKind.val type))::Δ) 
        _ _ _ (x, G) (x, D) R.lift];
      rfl
      rfl
    | exists_ _ _ IA IB => 
      stop
      dsimp only [Term.denote_ty]
      simp only [pure]
      --TODO: generalized existential helper
      stop
      apply congr rfl _;
      funext x;
      apply congr (congr rfl _) _;
      apply IA;
      assumption
      rfl
      rw [@IB 
        ((Hyp.mk _ (HypKind.val type))::Δ) 
        _ _ _ (x, G) (x, D) R.lift];
      rfl
      rfl
    | eq _ Hl Hr =>
      stop
      dsimp only [Term.denote_ty]
      apply propext;
      apply Iff.intro;
      {
        intro ⟨Hl', Hr', HG⟩;
        exists Hl.stlc, Hr.stlc;
        --TODO: report this "this pattern is a metavariable trash"
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

--TODO: make stricter...
theorem Term.denote_wk1_eq
  {Γ: Context}  {A: Term}  {s}
  (HΓ: Γ ⊢ A: sort s) 
  (B: Term)
  (x: Option B.stlc_ty.interp) 
  (G: Γ.upgrade.stlc.interp)
  (a: Option A.stlc_ty.interp)
  (a': Option A.wk1.stlc_ty.interp)
  (Haa': a' = (A.stlc_ty_wk Wk.wk1) ▸ a)
  : A.denote_ty G a 
  = @denote_ty A.wk1 (B.stlc_ty::Γ.upgrade.stlc) (x, G) a'
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

theorem Term.denote_wk1
  {Γ: Context}  {A: Term}  {s}
  (HΓ: Γ ⊢ A: sort s) 
  (B: Term)
  (x: Option B.stlc_ty.interp) 
  (G: Γ.upgrade.stlc.interp) 
  (a: Option A.stlc_ty.interp)
  (a': Option A.wk1.stlc_ty.interp)
  (Haa': a' = A.stlc_ty_wk1 ▸ a)
  (H: A.denote_ty G a) 
  : @denote_ty A.wk1 (B.stlc_ty::Γ.upgrade.stlc) (x, G) a'
  := by {
    rw [Term.denote_wk1_eq] at H;
    exact H;
    exact HΓ;
    exact Haa';
  }