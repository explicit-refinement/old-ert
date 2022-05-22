import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc
import LogicalRefinement.Denot.Basic

open AnnotSort
open Annot

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
    A.denote_ty Δ.upgrade.sparsity (S.transport_interp_up IΔ G) a =
    (A.subst σ).denote_ty Γ.upgrade.sparsity G (HA.stlc_ty_subst ▸ a)
  := by {
    generalize HK: sort s = K;
    rw [HK] at HA;
    induction HA generalizing σ Γ s with
    | pi HA' HB IA IB =>
      stop
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
        generalize Hb: Ty.interp.bind_val _ _ = b;
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
          simp only [Context.sparsity_ty] at IB';
          rw [<-IB']
          rw [
            S.transport_interp_up_lift_ty S' IΔ 
            (by assumption)
            G x' x Hx'.symm
          ]
          have Hbind: 
            ((HasType.stlc_ty_subst (by assumption)) ▸ b) 
            = Ty.interp.bind_val a x' := by {
              rw [<-Hb]
              rw [<-Hx']
              cases x with
              | none => 
                simp [Ty.abort, interp_eq_none]
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
          simp only [Context.sparsity_ty] at IB';
          rw [
            <-S.transport_interp_up_lift_ty S' IΔ 
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
          | none => simp [interp_eq_none, Ty.abort, Ty.interp.bind_val]
          | some x => 
            unfold Ty.interp.bind_val
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
      stop
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
          simp only [Ty.eager, pure]
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
            transport_interp_up_lift_ty S S'
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
            rfl
    | coprod HA' HB IA IB =>
      stop
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
          simp only [Ty.eager, pure]
          apply equiv_prop_split (IA S IΓ IΔ HG HA' rfl)
          rfl
          rw [rec_to_cast']
          rw [cast_some]
          rw [HA'.stlc_ty_subst]
          rw [HB.stlc_ty_subst]
        | inr a => 
          rw [rec_to_cast']
          rw [cast_inr']
          simp only [Ty.eager, pure]
          apply equiv_prop_split (IB S IΓ IΔ HG HB rfl)
          rfl
          rw [rec_to_cast']
          rw [cast_some]
          rw [HB.stlc_ty_subst]
          rw [HA'.stlc_ty_subst]
    | assume Hφ HA' Iφ IA => 
      stop
      dsimp only [Term.denote_ty]
      rw [rec_to_cast']
      rw [cast_not_none_is_not_none]
      apply equiv_and_split;
      intro Ha;
      have Iφ' := 
        interp_eq_none ▸ @Iφ Γ σ G none prop S IΓ IΔ HG Hφ rfl;
      apply equiv_arrow_helper';
      {
       exact Iφ'
      }
      {
        intro Hφ';
        apply equiv_prop_split 
          (IA 
            (S.lift_prop Hφ) 
            (IsCtx.cons_val IΓ (Hφ.subst S)) 
            (IsCtx.cons_val IΔ Hφ) 
            ⟨Iφ' ▸ Hφ', HG⟩ HA' rfl);
        {
          rw [transport_interp_up_lift_prop]
          rfl
          exact Hφ
        }
        {
          rw [rec_to_cast']
          rfl
        }
      }
      rw [HA.stlc_ty_subst]
    | @set Γ A B  HA' Hφ IA Iφ =>
      stop
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
          rw [<-transport_interp_up_lift_ty]
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
    | intersect HA HB IA IB => 
      stop
      dsimp only [Term.denote_ty]
      rw [rec_to_cast']
      rw [cast_not_none_is_not_none]
      apply equiv_and_split;
      intro Ha;
      apply propext;
      apply Iff.intro <;> intro H x Hx;
      {
        sorry
      }
      {
        sorry
      }
      rw [HA.stlc_ty_subst]
    | union => 
      stop
      dsimp only [Term.denote_ty]
      rw [rec_to_cast']
      rw [cast_not_none_is_not_none]
      apply equiv_and_split;
      intro Ha;
      {
        sorry
      }
      {
        sorry
      }
    | dimplies Hφ Hψ Iφ Iψ => 
      stop
      cases a with
      | none => 
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
            σ.lift G none prop S'
            (IsCtx.cons_val IΓ (Hφ.subst S)) 
            (IsCtx.cons_val IΔ Hφ) 
            ⟨Iφ' ▸ HGφ, HG⟩ Hψ rfl;
          apply equiv_prop_split Iψ';
          {
            rw [
              <-transport_interp_up_lift_prop
                S S' IΔ Hφ G
            ]
            rfl
          }
          rfl
        }
      | some a => cases a
    | dand Hφ Hψ Iφ Iψ => 
      stop
      cases a with
      | none => 
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
          σ.lift G none prop S'
          (IsCtx.cons_val IΓ (Hφ.subst S)) 
          (IsCtx.cons_val IΔ Hφ) 
          ⟨Iφ' ▸ HGφ, HG⟩ Hψ rfl;
        apply equiv_prop_split Iψ';
        {
            rw [
              <-transport_interp_up_lift_prop
                S S' IΔ Hφ G
            ]
            rfl
        }
        rfl
      | some a => cases a
    | or Hφ Hψ Iφ Iψ => 
      stop
      cases a with
      | none => 
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
      | some a => cases a
    | @forall_ Γ A φ HA' Hφ IA Iφ => 
      stop
      cases a with
      | none => 
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
            Context.sparsity, Context.upgrade, 
            Hyp.sparsity, Hyp.upgrade, HypKind.upgrade] at Iφ';
          rw [<-Iφ']
          rw [transport_interp_up_lift_ty]
          apply H (HA'.stlc_ty_subst ▸ x) (IA'.symm ▸ Hx);
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
            Context.sparsity, Context.upgrade, 
            Hyp.sparsity, Hyp.upgrade, HypKind.upgrade] at Iφ';
          rw [<-
            transport_interp_up_lift_ty S S'
            IΔ HA' G x (HA'.stlc_ty_subst ▸ x)
          ]
          rw [Iφ']
          exact H (HA'.stlc_ty_subst ▸ x) (IA' ▸ Hx);
          rw [interp_eq_collapse]
        }
      | some a => cases a
    | @exists_ Γ A φ HA' Hφ IA Iφ =>
      cases a with
      | none => 
        dsimp only [Term.denote_ty];
        apply propext;
        apply Iff.intro <;>
        intro ⟨x, ⟨Hx, HGφ⟩⟩;
        {
          let x': (A.subst σ).stlc_ty.interp := 
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
            Context.sparsity, Context.upgrade, 
            Hyp.sparsity, Hyp.upgrade, HypKind.upgrade] at Iφ';
          apply And.intro;
          {
            sorry
          }
          {
            rw [<-Iφ']
            rw [
              transport_interp_up_lift_ty S S'
              IΔ HA' G x (HA'.stlc_ty_subst ▸ x)
            ]
            exact HGφ;
            rw [interp_eq_collapse]
          }
        }
        {
          let x': A.stlc_ty.interp := 
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
            Context.sparsity, Context.upgrade, 
            Hyp.sparsity, Hyp.upgrade, HypKind.upgrade] at Iφ';
          apply And.intro;
          {
            sorry
          }
          {
            rw [<-
              transport_interp_up_lift_ty S S'
              IΔ HA' G x' (HA'.stlc_ty_subst ▸ x)
            ]
            rw [Iφ']
            exact interp_eq_collapse ▸ HGφ;
            rw [interp_eq_collapse]
          }
        }
      | some a => cases a
    | @eq Δ A l r HA' Hl Hr IA Il Ir => 
      stop
      cases a with
      | none => 
        dsimp only [Term.denote_ty];
        apply propext;
        apply Iff.intro
        {
          intro ⟨px, py, Hxy⟩;
          exists (Hl.subst S.upgrade).stlc;
          exists (Hr.subst S.upgrade).stlc;
          rw [Hl.subst_stlc_interp_up_commute S IΔ G]
          rw [Hr.subst_stlc_interp_up_commute S IΔ G]
          rw [rec_down]
          exact Hxy
        }
        {
          intro ⟨px, py, Hxy⟩;
          dsimp only [Annot.stlc_ty] at Hxy
          exists Hl.stlc;
          exists Hr.stlc;
          have R := @HasType.subst_stlc_interp_up_commute';
          dsimp only [Stlc.Context.deriv.subst] at R;
          unfold transport_interp_up
          rw [<-R Hl]
          rw [<-R Hr]
          rw [rec_down]
          exact Hxy
        }
      | some a => cases a
    | _ => stop cases HK <;> cases a <;> rfl
  }

theorem HasType.denote_subst0'
  {A: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} {a: A.stlc_ty.interp}
  {B: Term} {b: Term}
  {a': (A.subst0 b).stlc_ty.interp}
  {b'}
  (Hb: Γ ⊢ b: term B)
  (HAA': A.stlc_ty = (A.subst0 b).stlc_ty)
  (Haa': a' = HAA' ▸ a)
  (Hbb': b' = Hb.stlc.interp G.downgrade)
  (H: @Term.denote_ty A (B.stlc_ty::Γ.upgrade.stlc) (true::σ) (b', G) a)
  : @Term.denote_ty (A.subst0 b) Γ.upgrade.stlc σ G a'
  := sorry

theorem HasType.denote_antisubst0'
  {A: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} {a: A.stlc_ty.interp}
  {B: Term} {b: Term}
  {a': (A.subst0 b).stlc_ty.interp}
  {b'}
  (HA: Γ ⊢ A: S)
  (HS: S = sort s)
  (Hb: Γ ⊢ b: term B)
  (HAA': A.stlc_ty = (A.subst0 b).stlc_ty)
  (Haa': a' = HAA' ▸ a)
  (Hbb': b' = Hb.stlc.interp G.downgrade)
  (H: @Term.denote_ty (A.subst0 b) Γ.upgrade.stlc σ G a')
  : @Term.denote_ty A (B.stlc_ty::Γ.upgrade.stlc) (true::σ) (b', G) a
  := sorry