import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc
import LogicalRefinement.Denot.Basic
import LogicalRefinement.Denot.Irrel

open AnnotSort
open Annot

set_option maxHeartbeats 10000000

def ValidSubst {Γ Δ: Context} 
  (I: Stlc.InterpSubst Γ.upgrade.stlc Δ.upgrade.stlc): Prop 
  := ∀G, (G ⊧ ✓Γ) -> (I.transport_ctx G ⊧ ✓Δ)

theorem SubstCtx.subst_denot
  {Γ Δ: Context} {σ} {G: Γ.upgrade.stlc.interp} {A: Term} {a s}
  (S: SubstCtx σ Γ Δ)
  (IΓ: IsCtx Γ) (IΔ: IsCtx Δ)
  (HG: G ⊧ ✓Γ)
  (HA: Δ ⊢ A: sort s)
  : 
    A.denote_ty (S.transport_interp_up IΔ G) a =
    (A.subst σ).denote_ty G (HA.stlc_ty_subst ▸ a)
  := by {
    generalize HK: sort s = K;
    rw [HK] at HA;
    induction HA generalizing σ Γ s with
    | pi HA' HB IA IB =>
      cases a with
      | none => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_none]
      | some a => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_some]
        simp only []
        apply propext
        apply Iff.intro <;>
        intro H x xin <;>
        generalize Hb: Option.bind _ _ = b;
        {
          generalize Hx': 
            ((HasType.stlc_ty_subst (by assumption)) ▸ x) = x';
          have IA' :=
            Hx' ▸
            interp_eq_collapse ▸
            Hx'.symm ▸ 
            @IA Γ σ G x' type S IΓ IΔ HG (by assumption) rfl;
          have xin' := Hx' ▸ IA'.symm ▸ xin;
          have H' := H x' xin';
          have S' := S.lift_delta' (HypKind.val type) HA';
          have IB' := 
            interp_eq_collapse ▸ 
            @IB 
              ({ ty := Term.subst _ σ, kind := HypKind.val type } :: Γ) 
              σ.lift 
              (x, G) 
              (HB.stlc_ty_subst ▸ b)
              type 
              S'
              (IsCtx.cons_val IΓ (HA'.subst_sort S))
              (by constructor <;> assumption)
              ⟨xin, HG⟩
              (by assumption)
              rfl;
          dsimp only 
            [Context.upgrade, Hyp.upgrade, HypKind.upgrade] at IB';
          rw [<-IB']
          rw [
            S.transport_interp_up_lift S' IΔ 
            (by assumption)
            G x' x Hx'.symm
          ]
          have Hbind: 
            ((HasType.stlc_ty_subst (by assumption)) ▸ b) 
            = Option.bind x' a := by {
              rw [<-Hb]
              rw [<-Hx']
              cases x with
              | none => 
                simp [Ty.abort, interp_eq_none, Option.bind]
              | some x => 
                simp [interp_eq_some]
                rw [rec_to_cast']
                rw [rec_to_cast']
                rw [rec_to_cast']
                apply cast_tri''
            };
          rw [Hbind]
          exact H'
        }
        {
          generalize Hx': 
            (HA'.stlc_ty_subst.symm ▸ x) = x';
          have IA' :=
            Hx' ▸
            @IA Γ σ G x type S IΓ IΔ HG (by assumption) rfl;
          have xin' := Hx' ▸ IA' ▸ xin;
          have H' := H x' xin';
          have S' := S.lift_delta' (HypKind.val type) HA';
          have IB' :=
            @IB 
              ({ ty := Term.subst _ σ, kind := HypKind.val type } :: Γ) 
              σ.lift 
              (x', G) 
              b
              type 
              S'
              (IsCtx.cons_val IΓ (HA'.subst_sort S))
              (by constructor <;> assumption)
              ⟨xin', HG⟩
              (by assumption)
              rfl;
          dsimp only 
            [Context.upgrade, Hyp.upgrade, HypKind.upgrade] at IB';
          rw [
            <-S.transport_interp_up_lift S' IΔ 
            (by assumption)
            G x x' 
            (by
              rw [<-Hx']
              rw [rec_to_cast']
              rw [rec_to_cast']
              rw [cast_merge]
              rfl
            )
          ]
          rw [IB']
          apply equiv_prop_helper H';
          rw [<-Hb]
          rw [<-Hx']
          cases x with
          | none => simp [interp_eq_none, Ty.abort, Option.bind]
          | some x => 
            unfold Option.bind
            rw [interp_eq_some]
            simp only []
            rw [rec_to_cast']
            rw [rec_to_cast']
            rw [rec_to_cast']
            apply congr;
            rfl
            rw [cast_dist]
            rfl
        }
    | sigma HA' HB IA IB =>
      cases a with
      | none => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_none]
      | some a => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_some]
        cases a with
        | mk a b =>
          rw [rec_to_cast']
          rw [cast_pair' 
            (by rw [HA'.stlc_ty_subst]) 
            (by rw [HB.stlc_ty_subst])
          ]
          simp only [pure]
          rw [<-@cast_some _ _ (by rw [HA'.stlc_ty_subst])]
          simp only [rec_to_cast'] at IA;
          rw [IA _ IΓ IΔ HG HA' rfl]
          apply equiv_and_split;
          intro HGa;
          let S' := S.lift_type HA';
          generalize Ha': cast _ a = a';
          have HGa' := Ha' ▸ cast_some ▸ HGa;
          simp only [rec_to_cast'] at IB;
          rw [<-
            transport_interp_up_lift S S'
            IΔ HA' G (some a) (some a')
            (by
              rw [rec_to_cast']
              rw [<-Ha']
              rw [cast_some]
              rw [cast_merge]
              rfl
              rw [HA'.stlc_ty_subst]
              rw [HA'.stlc_ty_subst]
            )
          ]
          apply equiv_prop_split;
          apply 
            @IB ((Hyp.mk _ (HypKind.val type))::Γ) 
            σ.lift 
            (some a', G) 
            (some b)
            type
            S' 
            (IsCtx.cons_val IΓ (HA'.subst S))
            (IsCtx.cons_val IΔ HA')
            ⟨HGa', HG⟩ 
            HB 
            rfl;
          . rfl
          . generalize Hsa': cast _ (some a) = sa';
            have H: sa' = some a' := by rw [<-Hsa', <-Ha', cast_some]
            rw [H, cast_some]
    | coprod HA' HB IA IB =>
      cases a with
      | none => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_none]
      | some a => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_some]
        simp only []
        cases a with
        | inl a => 
          rw [rec_to_cast']
          rw [cast_inl']
          simp only [pure]
          apply equiv_prop_split (IA S IΓ IΔ HG HA' rfl)
          rfl
          rw [rec_to_cast']
          rw [cast_some]
          rw [HA'.stlc_ty_subst]
          rw [HB.stlc_ty_subst]
        | inr a => 
          rw [rec_to_cast']
          rw [cast_inr']
          simp only [pure]
          apply equiv_prop_split (IB S IΓ IΔ HG HB rfl)
          rfl
          rw [rec_to_cast']
          rw [cast_some]
          rw [HB.stlc_ty_subst]
          rw [HA'.stlc_ty_subst]
    | @assume Γ ϕ A' Hφ HA' Iφ IA =>
      cases a with
      | none => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_none]
      | some a => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_some]
        simp only []
        have Hhelp: 
          ϕ.denote_ty (transport_interp_up S IΔ G) none
          = (Term.subst ϕ σ).denote_ty G none
          := by
            rw [Iφ S IΓ IΔ HG Hφ]
            rw [interp_eq_none]
            rfl
        apply equiv_arrow_helper' Hhelp;
        {
          intro Dφ;
          have S' := S.lift_delta' (HypKind.val prop) Hφ;
          rw [<-transport_interp_up_lift S S' IΔ Hφ _ none none]
          rw [
            @IA 
            ((Hyp.mk (ϕ.subst σ) (HypKind.val prop))::Γ) _ 
            (none, G) (a ()) type
            S' 
            (IΓ.cons_val (Hφ.subst S)) 
            (IΔ.cons_val Hφ) 
            ⟨Hhelp ▸ Dφ, HG⟩
            HA' rfl
          ]
          apply congr rfl _;
          rw [rec_to_cast]
          rw [rec_to_cast]
          rw [<-cast_app_pull_in]
          rw [HA'.stlc_ty_subst]
          rw [HasType.stlc_ty_subst]
          constructor <;> assumption
          rw [interp_eq_none]
        }
    | @set Γ A B  HA' Hφ IA Iφ =>
      dsimp only [Term.denote_ty]
      have IA' := @IA Γ σ G a type S IΓ IΔ HG HA' rfl;
      rw [IA']
      apply equiv_and_split;
      intro Ha;
      have S' := S.lift_type HA';
      have Iφ' := @Iφ 
        ((Hyp.mk (A.subst σ) (HypKind.val type))::Γ) 
        σ.lift (HA'.stlc_ty_subst ▸ a, G) none prop 
        S'
        (IsCtx.cons_val IΓ (HA'.subst S)) (IsCtx.cons_val IΔ HA') 
        ⟨Ha, HG⟩ Hφ rfl;
      apply equiv_prop_split Iφ';
      {
        --TODO: this really shouldn't be using set, but eh it works
        cases s with
        | type => 
          rw [<-transport_interp_up_lift]
          rfl
          exact S.lift_type HA;
          exact HA;
          rw [rec_to_cast']
          rw [rec_to_cast']
          rw [cast_merge]
          rfl
        | prop => cases HA
      }
      {
        rw [interp_eq_none]
        rfl
      }
    | @intersect Γ A B HA' HB IA IB => 
      cases a with
      | none => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_none]
      | some a => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_some]
        simp only []
        apply propext
        apply Iff.intro <;>
        intro H x xin <;>
        generalize Hb: a () = b;
        {
          generalize Hx': 
            ((HasType.stlc_ty_subst (by assumption)) ▸ x) = x';
          have IA' :=
            Hx' ▸
            interp_eq_collapse ▸
            Hx'.symm ▸ 
            @IA Γ σ G x' type S IΓ IΔ HG (by assumption) rfl;
          have xin' := Hx' ▸ IA'.symm ▸ xin;
          have H' := H x' xin';
          have S' := S.lift_delta' (HypKind.val type) HA';
          have IB' := 
            @IB 
              ({ ty := Term.subst _ σ, kind := HypKind.val type } :: Γ) 
              σ.lift 
              (x, G) 
              b
              type 
              S'
              (IsCtx.cons_val IΓ (HA'.subst_sort S))
              (by constructor <;> assumption)
              ⟨xin, HG⟩
              (by assumption)
              rfl;
          dsimp only 
            [Context.upgrade, Hyp.upgrade, HypKind.upgrade] at IB';
          rw [<-Hb] at IB';
          rw [rec_to_cast] at IB';
          rw [rec_to_cast]
          rw [cast_app_pull_in]
          rw [<-IB']
          rw [
            S.transport_interp_up_lift S' IΔ 
            (by assumption)
            G x' x Hx'.symm
          ]
          exact H';
          rw [HB.stlc_ty_subst]
          rw [HB.stlc_ty_subst]
        }
        {
          generalize Hx': 
            (HA'.stlc_ty_subst.symm ▸ x) = x';
          have IA' :=
            Hx' ▸
            @IA Γ σ G x type S IΓ IΔ HG (by assumption) rfl;
          have xin' := Hx' ▸ IA' ▸ xin;
          have H' := H x' xin';
          have S' := S.lift_delta' (HypKind.val type) HA';
          have IB' :=
            @IB 
              ({ ty := Term.subst _ σ, kind := HypKind.val type } :: Γ) 
              σ.lift 
              (x', G) 
              b
              type 
              S'
              (IsCtx.cons_val IΓ (HA'.subst_sort S))
              (by constructor <;> assumption)
              ⟨xin', HG⟩
              (by assumption)
              rfl;
          dsimp only 
            [Context.upgrade, Hyp.upgrade, HypKind.upgrade] at IB';
          rw [
            <-S.transport_interp_up_lift S' IΔ 
            (by assumption)
            G x x' 
            (by
              rw [<-Hx']
              rw [rec_to_cast']
              rw [rec_to_cast']
              rw [cast_merge]
              rfl
            )
          ]
          rw [IB']
          apply equiv_prop_helper H';
          rw [<-Hb]
          rw [<-Hx']
          cases x with
          | none => 
            rw [interp_eq_none]
            rw [rec_to_cast]
            rw [rec_to_cast]
            rw [cast_app_pull_in]
            rw [HB.stlc_ty_subst]
            rw [HB.stlc_ty_subst]
          | some x => 
            rw [interp_eq_some]
            simp only []
            rw [rec_to_cast']
            rw [rec_to_cast']
            rw [rec_to_cast']
            apply congr;
            rfl
            rw [cast_dist]
            rfl
            rfl
        }
    | @union Γ A B HA' HB IA IB =>
      dsimp only [Term.denote_ty]
      rw [rec_to_cast']
      rw [cast_not_none_is_not_none]
      apply equiv_and_split;
      intro _;
      apply propext;
      apply Iff.intro <;> intro ⟨x, Hx, Ha⟩;
      {
        exists HA'.stlc_ty_subst.symm ▸ x;
        have IA' := 
          @IA Γ σ G x type S IΓ IΔ HG HA' rfl;         
        have S' := S.lift_type HA'
        have IB' := @IB 
          ((Hyp.mk _ (HypKind.val type))::Γ) 
          σ.lift (HA'.stlc_ty_subst.symm ▸ x, G) a type 
          S'
          (IsCtx.cons_val IΓ (HA'.subst S)) (IsCtx.cons_val IΔ HA') 
          ⟨IA' ▸ Hx, HG⟩ HB rfl;
        simp [
          Context.upgrade, Hyp.upgrade, HypKind.upgrade] at IB';
        rw [rec_to_cast'] at IB';
        rw [rec_to_cast'] at IB';
        apply And.intro;
        {
            rw [<-IA']
            exact Hx
        }
        {
            rw [rec_to_cast']
            dsimp only [Term.stlc_ty];
            rw [<-IB']
            rw [transport_interp_up_lift]
            exact Ha;
            assumption
            rw [rec_to_cast']
            rw [cast_merge]
            rfl
        }
      }
      {
        exists HA'.stlc_ty_subst.symm ▸ x;
        have IA' := 
          @IA Γ σ G (HA'.stlc_ty_subst.symm ▸ x) type S IΓ IΔ HG HA' rfl;         
        have S' := S.lift_type HA'
        have IB' := @IB 
          ((Hyp.mk _ (HypKind.val type))::Γ) 
          σ.lift (x, G) a type 
          S'
          (IsCtx.cons_val IΓ (HA'.subst S)) (IsCtx.cons_val IΔ HA') 
          ⟨Hx, HG⟩ HB rfl;
        simp [
          Context.upgrade, Hyp.upgrade, HypKind.upgrade] at IB';
        rw [rec_to_cast'] at IB';
        apply And.intro;
        {
            rw [IA']
            exact interp_eq_collapse ▸ Hx
        }
        {
          rw [rec_to_cast']
          dsimp only [Term.stlc_ty];
          rw [<-
            transport_interp_up_lift S S'
          ]
          rw [IB']
          exact Ha;
          assumption
          rw [rec_to_cast']
        }
      }
      rw [HA.stlc_ty_subst]
    | dimplies Hφ Hψ Iφ Iψ => 
      dsimp only [Term.denote_ty];
      have Iφ' := 
        interp_eq_none ▸ @Iφ Γ σ G none prop S IΓ IΔ HG Hφ rfl;
      apply equiv_arrow_helper';
      rw [Iφ']
      {
        intro HGφ;
        have S' := (S.lift_prop Hφ) 
        have Iψ' := 
          interp_eq_none ▸ 
          @Iψ 
          ((Hyp.mk _ (HypKind.val prop))::Γ)  
          σ.lift (none, G) none prop S'
          (IsCtx.cons_val IΓ (Hφ.subst S)) 
          (IsCtx.cons_val IΔ Hφ) 
          ⟨Iφ' ▸ HGφ, HG⟩ Hψ rfl;
        apply equiv_prop_split Iψ';
        {
          rw [
            transport_interp_up_lift
              S S' IΔ Hφ G
          ]
          rw [rec_to_cast]
          rw [cast_none]
          rw [Hφ.stlc_ty_subst]
        }
        rfl
      }
    | dand Hφ Hψ Iφ Iψ => 
      dsimp only [Term.denote_ty];
      have Iφ' := 
        interp_eq_none ▸ @Iφ Γ σ G none prop S IΓ IΔ HG Hφ rfl;
      rw [Iφ']
      apply equiv_and_split;
      intro HGφ;
      have S' := (S.lift_prop Hφ) 
      have Iψ' := 
        interp_eq_none ▸ 
        @Iψ 
        ((Hyp.mk _ (HypKind.val prop))::Γ)  
        σ.lift (none, G) none prop S'
        (IsCtx.cons_val IΓ (Hφ.subst S)) 
        (IsCtx.cons_val IΔ Hφ) 
        ⟨Iφ' ▸ HGφ, HG⟩ Hψ rfl;
      apply equiv_prop_split Iψ';
      {
          rw [
            <-transport_interp_up_lift
              S S' IΔ Hφ G
          ]
          rw [rec_to_cast]
          rw [cast_none]
          rw [Hφ.stlc_ty_subst]
      }
      rfl
    | or Hφ Hψ Iφ Iψ => 
      dsimp only [Term.denote_ty];
      apply equiv_or_split;
      {
        rw [Iφ]
        rw [interp_eq_none]
        exact prop;
        assumption
        assumption
        assumption
        rfl
      }
      {
        rw [Iψ]
        rw [interp_eq_none]
        exact prop;
        assumption
        assumption
        assumption
        rfl
      }
    | @forall_ Γ A φ HA' Hφ IA Iφ => 
      dsimp only [Term.denote_ty];
      apply propext;
      apply Iff.intro <;>
      intro H x Hx;
      {
        have IA' := 
          interp_eq_collapse ▸
          @IA Γ σ G (HA'.stlc_ty_subst ▸ x) type S IΓ IΔ HG HA' rfl;
        have S' := S.lift_type HA'
        have Iφ' := @Iφ 
          ((Hyp.mk _ (HypKind.val type))::Γ) 
          σ.lift (x, G) none prop 
          S'
          (IsCtx.cons_val IΓ (HA'.subst S)) (IsCtx.cons_val IΔ HA') 
          ⟨Hx, HG⟩ Hφ rfl;
        rw[interp_eq_none] at Iφ';
        simp [
          Context.upgrade, 
          Hyp.upgrade, HypKind.upgrade] at Iφ';
        rw [<-Iφ']
        rw [transport_interp_up_lift]
        exact H (HA'.stlc_ty_subst ▸ x) (IA'.symm ▸ Hx);
        exact HA';
        rfl
      }
      {
        have IA' := 
          @IA Γ σ G x type S IΓ IΔ HG HA' rfl;
        have S' := S.lift_type HA'
        have Iφ' := @Iφ 
          ((Hyp.mk _ (HypKind.val type))::Γ) 
          σ.lift (HA'.stlc_ty_subst ▸ x, G) none prop 
          S'
          (IsCtx.cons_val IΓ (HA'.subst S)) (IsCtx.cons_val IΔ HA') 
          ⟨IA' ▸ Hx, HG⟩ Hφ rfl;
        rw[interp_eq_none] at Iφ';
        simp [
          Context.upgrade, 
          Hyp.upgrade, HypKind.upgrade] at Iφ';
        rw [<-
          transport_interp_up_lift S S'
          IΔ HA' G x (HA'.stlc_ty_subst ▸ x)
        ]
        rw [Iφ']
        exact H (HA'.stlc_ty_subst ▸ x) (IA' ▸ Hx);
        rw [interp_eq_collapse]
      }
    | @exists_ Γ A φ HA' Hφ IA Iφ =>
      dsimp only [Term.denote_ty];
      apply propext;
      apply Iff.intro <;>
      intro ⟨x, ⟨Hx, HGφ⟩⟩;
      {
        let x': Option (A.subst σ).stlc_ty.interp := 
          HA'.stlc_ty_subst.symm ▸ x;
        exists x';
        have IA' := 
          @IA Γ σ G x type S IΓ IΔ HG HA' rfl;
        have S' := S.lift_type HA'
        have Iφ' := @Iφ 
          ((Hyp.mk (A.subst σ) (HypKind.val type))::Γ) 
          σ.lift (x', G) none prop 
          S'
          (IsCtx.cons_val IΓ (HA'.subst S)) (IsCtx.cons_val IΔ HA') 
          ⟨IA' ▸ Hx, HG⟩ Hφ rfl;
        rw[interp_eq_none] at Iφ';
        simp [
          Context.upgrade, Hyp.upgrade, HypKind.upgrade] at Iφ';
        apply And.intro;
        {
          rw [<-IA']
          exact Hx
        }
        {
          rw [<-Iφ']
          rw [
            transport_interp_up_lift S S'
            IΔ HA' G x (HA'.stlc_ty_subst ▸ x)
          ]
          exact HGφ;
          rw [interp_eq_collapse]
        }
      }
      {
        let x': Option A.stlc_ty.interp := 
          HA'.stlc_ty_subst.symm ▸ x;
        exists x';
        have IA' := 
          @IA Γ σ G x' type S IΓ IΔ HG HA' rfl;
        have S' := S.lift_type HA'
        have Iφ' := @Iφ 
          ((Hyp.mk _ (HypKind.val type))::Γ) 
          σ.lift (HA'.stlc_ty_subst ▸ x, G) none prop 
          S'
          (IsCtx.cons_val IΓ (HA'.subst S)) (IsCtx.cons_val IΔ HA') 
          ⟨interp_eq_collapse ▸ Hx, HG⟩ Hφ rfl;
        rw[interp_eq_none] at Iφ';
        simp [
          Context.upgrade, Hyp.upgrade, HypKind.upgrade] at Iφ';
        apply And.intro;
        {
          rw [IA']
          exact interp_eq_collapse ▸ Hx
        }
        {
          rw [<-
            transport_interp_up_lift S S'
            IΔ HA' G x' (HA'.stlc_ty_subst ▸ x)
          ]
          rw [Iφ']
          exact interp_eq_collapse ▸ HGφ;
          rw [interp_eq_collapse]
        }
      }
    | @eq Δ A l r _ Hl Hr _ _ _ =>
      dsimp only [Term.denote_ty];
      apply propext;
      apply Iff.intro
      {
        intro ⟨_, _, Hxy⟩;
        exists (Hl.subst S.upgrade).stlc;
        exists (Hr.subst S.upgrade).stlc;
        rw [Hl.subst_stlc_interp_up_commute S IΔ G]
        rw [Hr.subst_stlc_interp_up_commute S IΔ G]
        rw [rec_down]
        exact Hxy
      }
      {
        --TODO: report spurious unused variable warning
        intro ⟨_, _, Hxy⟩;
        dsimp only [Annot.stlc_ty] at Hxy
        exists Hl.stlc;
        exists Hr.stlc;
        have R := @HasType.subst_stlc_interp_up_commute';
        dsimp only [Stlc.Context.deriv.subst] at R;
        unfold transport_interp_up
        rw [<-R Hl]
        rw [<-R Hr]
        rw [rec_down]
        exact Hxy;
        assumption
        assumption
        assumption
        assumption
      }
    | _ => cases HK <;> cases a <;> rfl
  }


theorem SubstCtx.subst_denot'
  {Γ Δ: Context} {σ} {G: Γ.upgrade.stlc.interp} {G'} {A: Term} {a a' s}
  (S: SubstCtx σ Γ Δ)
  (IΓ: IsCtx Γ) (IΔ: IsCtx Δ)
  (HG: G ⊧ ✓Γ)
  (HA: Δ ⊢ A: sort s)
  (HG': G' = S.transport_interp_up IΔ G)
  (Ha': a' = HA.stlc_ty_subst ▸ a)
  : 
    A.denote_ty G' a =
    (A.subst σ).denote_ty G a'
  := by {
    rw [HG', Ha']
    apply subst_denot <;> assumption
  }

theorem SubstCtx.subst_denot''
  {Γ Δ: Context} {σ} {G: Γ.upgrade.stlc.interp} {G'} {A: Term} {a a' s}
  (S: SubstCtx σ Γ Δ)
  (IΓ: IsCtx Γ) (IΔ: IsCtx Δ)
  (HG: G ⊧ ✓Γ)
  (HA: Δ ⊢ A: sort s)
  (HG': G' = S.transport_interp_up IΔ G)
  (Ha': a' = HA.stlc_ty_subst ▸ a)
  : 
    A.denote_ty G' a =
    (A.subst σ).denote_ty G a'
  := by {
    rw [HG', Ha']
    apply subst_denot <;> assumption
  }

theorem HasType.denote_val_subst0
  {A: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} 
  {a: Option A.stlc_ty.interp}
  {B: Term} {b: Term}
  {a': Option (A.subst0 b).stlc_ty.interp}
  {b' s s'}
  (Hb: Γ ⊢ b: expr s' B)
  (HΓ: IsCtx Γ)
  (HG: G ⊧ ✓Γ)
  (HA: ({ ty := B, kind := HypKind.val s' } :: Γ) ⊢ A: sort s)
  (HAA': A.stlc_ty = (A.subst0 b).stlc_ty)
  (Haa': a' = HAA' ▸ a)
  (Hbb': b' = Hb.stlc.interp G.downgrade)
  : @Term.denote_ty A (B.stlc_ty::Γ.upgrade.stlc) (b', G) a =
    @Term.denote_ty (A.subst0 b) Γ.upgrade.stlc G a'
  := by {
    have I := 
      @SubstCtx.subst_denot 
      _ _ _ _ _ a _
      Hb.to_subst HΓ 
      (IsCtx.cons_val HΓ Hb.expr_regular) HG HA;
    apply equiv_prop_split I;
    {
      apply congr _ rfl;
      apply congr rfl;
      {
        simp only [
          SubstCtx.transport_interp_up, 
          SubstCtx.transport_interp,
          SubstCtx.interp,
          Stlc.SubstCtx.interp,
          Stlc.InterpSubst.transport_ctx
        ]
        apply congr;
        {
          apply congr rfl _;
          rw [Hbb'];
          rw [Hb.interp_upgrade]
          rfl
        }
        {
          --TODO: factor out as helper...
          sorry
        }
      }
    }
    {
      rw [Haa']
      rfl
    }
  }
    
theorem HasType.denote_val_subst0'
  {A: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} {a: Option A.stlc_ty.interp}
  {B: Term} {b: Term}
  {a': Option (A.subst0 b).stlc_ty.interp}
  {b' s'}
  (Hb: Γ ⊢ b: expr s' B)
  (HΓ: IsCtx Γ)
  (HG: G ⊧ ✓Γ)
  (HA: ({ ty := B, kind := HypKind.val s' } :: Γ) ⊢ A: type)
  (HAA': A.stlc_ty = (A.subst0 b).stlc_ty)
  (Haa': a' = HAA' ▸ a)
  (Hbb': b' = Hb.stlc.interp G.downgrade)
  (H: @Term.denote_ty A (B.stlc_ty::Γ.upgrade.stlc) (b', G) a)
  : @Term.denote_ty (A.subst0 b) Γ.upgrade.stlc G a'
  := by 
    rw [<-HasType.denote_val_subst0]
    exact H
    repeat assumption

theorem HasType.denote_val_antisubst0'
  {A: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} {a: Option A.stlc_ty.interp}
  {B: Term} {b: Term}
  {a': Option (A.subst0 b).stlc_ty.interp}
  {b' s'}
  (HΓ: IsCtx Γ)
  (HG: G ⊧ ✓Γ)
  (Hb: Γ ⊢ b: expr s' B)
  (HA: ({ ty := B, kind := HypKind.val s' } :: Γ) ⊢ A: sort s)
  (HAA': A.stlc_ty = (A.subst0 b).stlc_ty)
  (Haa': a' = HAA' ▸ a)
  (Hbb': b' = Hb.stlc.interp G.downgrade)
  (H: @Term.denote_ty (A.subst0 b) Γ.upgrade.stlc G a')
  : @Term.denote_ty A (B.stlc_ty::Γ.upgrade.stlc) (b', G) a
  := by 
    rw [HasType.denote_val_subst0]
    exact H
    repeat assumption

theorem HasType.denote_prop_subst0
  {A: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} 
  {a: Option A.stlc_ty.interp}
  {B: Term} {b: Term}
  {a': Option (A.subst0 b).stlc_ty.interp}
  {s b'}
  (Hb: Γ ⊢ b: proof B)
  (HΓ: IsCtx Γ)
  (HG: G ⊧ ✓Γ)
  (HA: ({ ty := B, kind := HypKind.val prop } :: Γ) ⊢ A: sort s)
  (HAA': A.stlc_ty = (A.subst0 b).stlc_ty)
  (Haa': a' = HAA' ▸ a)
  : @Term.denote_ty A (B.stlc_ty::Γ.upgrade.stlc) (b', G) a =
    @Term.denote_ty (A.subst0 b) Γ.upgrade.stlc G a'
  := by {
    rw [<-Hb.denote_val_subst0 HΓ HG HA HAA' Haa' rfl]
    rw [HA.eq_lrt_ty_denot']
    exact (G.eq_mod_lrt_refl Γ.upgrade Γ.upgrade).extend_prop
  }
    
theorem HasType.denote_prop_subst0'
  {A: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} 
  {a: Option A.stlc_ty.interp}
  {B: Term} {b: Term}
  {a': Option (A.subst0 b).stlc_ty.interp}
  {s b'}
  (Hb: Γ ⊢ b: proof B)
  (HΓ: IsCtx Γ)
  (HG: G ⊧ ✓Γ)
  (HA: ({ ty := B, kind := HypKind.val prop } :: Γ) ⊢ A: sort s)
  (HAA': A.stlc_ty = (A.subst0 b).stlc_ty)
  (Haa': a' = HAA' ▸ a)
  (H: @Term.denote_ty A (B.stlc_ty::Γ.upgrade.stlc) (b', G) a)
  : @Term.denote_ty (A.subst0 b) Γ.upgrade.stlc G a'
  := by 
    rw [<-HasType.denote_prop_subst0]
    exact H
    repeat assumption

theorem HasType.denote_prop_antisubst0'
  {A: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} {a: Option A.stlc_ty.interp}
  {B: Term} {b: Term}
  {a': Option (A.subst0 b).stlc_ty.interp}
  {s b'}
  (_: S = sort s)
  (HΓ: IsCtx Γ)
  (HG: G ⊧ ✓Γ)
  (Hb: Γ ⊢ b: proof B)
  (HA: ({ ty := B, kind := HypKind.val prop } :: Γ) ⊢ A: sort s)
  (HAA': A.stlc_ty = (A.subst0 b).stlc_ty)
  (Haa': a' = HAA' ▸ a)
  (H: @Term.denote_ty (A.subst0 b) Γ.upgrade.stlc G a')
  : @Term.denote_ty A (B.stlc_ty::Γ.upgrade.stlc) (b', G) a
  := by 
    rw [HasType.denote_prop_subst0]
    exact H
    repeat assumption