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
          simp only []
          apply congr;
          apply congr rfl;
          {
            apply propext;
            apply Iff.intro <;>
            intro H;
            {
              sorry
            }
            {
              sorry
            }
          }
          {
            apply propext;
            apply Iff.intro <;>
            intro H;
            {
              sorry
            }
            {
              sorry
            }
          }
    | coprod => 
      stop
      cases a with
      | none => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_none]
      | some a => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_some]
        simp only []
        --TODO: injection transport...
        cases a with
        | inl a => 
          apply propext;
          apply Iff.intro <;>
          intro H;
          {
            sorry
          }
          {
            sorry
          }
        | inr a =>
          dsimp only [Term.denote_ty]
          apply propext;
          apply Iff.intro <;>
          intro H;
          {
            sorry
          }
          {
            sorry
          }
    | assume => 
      stop
      dsimp only [Term.denote_ty]
      apply propext;
      apply Iff.intro <;>
      intro ⟨Hφ, Ha⟩;
      {
        apply And.intro;
        {
          sorry
        }
        {
          sorry
        }
      }
      {
        apply And.intro;
        {
          sorry
        }
        {
          sorry
        }
      }
    | set => 
      stop
      dsimp only [Term.denote_ty]
      apply propext;
      apply Iff.intro <;>
      intro ⟨Ha, Hφ⟩;
      {
        apply And.intro;
        {
          sorry
        }
        {
          sorry
        }
      }
      {
        apply And.intro;
        {
          sorry
        }
        {
          sorry
        }
      }
    | intersect => 
      stop
      dsimp only [Term.denote_ty]
      apply propext;
      apply Iff.intro <;>
      intro ⟨Han, H⟩
      {
        apply And.intro;
        {
          sorry
        }
        {
          sorry
        }
      }
      {
        apply And.intro;
        {
          sorry
        }
        {
          sorry
        }
      }
    | union => 
      stop
      dsimp only [Term.denote_ty]
      apply propext;
      apply Iff.intro <;>
      intro ⟨Han, x, Hx, Ha⟩;
      {
        sorry
      }
      {
        sorry
      }
    | dimplies => 
      stop
      cases a with
      | none => 
        dsimp only [Term.denote_ty];
        apply propext;
        apply Iff.intro <;>
        intro Hl Hr;
        {
          sorry
        }
        {
          sorry
        }
      | some a => cases a
    | dand => 
      stop
      cases a with
      | none => sorry
      | some a => cases a
    | or => 
      stop
      cases a with
      | none => 
        dsimp only [Term.denote_ty];
        apply propext;
        apply Iff.intro <;>
        intro H;
        {
          cases H with
          | inl H => sorry
          | inr H => sorry
        }
        {
          cases H with
          | inl H => sorry
          | inr H => sorry
        }
      | some a => cases a
    | forall_ => 
      stop
      cases a with
      | none => 
        dsimp only [Term.denote_ty];
        apply propext;
        apply Iff.intro <;>
        intro H x Hx;
        {
          sorry
        }
        {
          sorry
        }
      | some a => cases a
    | exists_ HA' Hφ IA Iφ =>
      stop
      cases a with
      | none => 
        dsimp only [Term.denote_ty];
        apply propext;
        apply Iff.intro <;>
        intro ⟨x, ⟨Hx, Hφ⟩⟩;
        {
          generalize Hx': HA'.stlc_ty_subst.symm ▸ x = x';
          exists x';
          apply And.intro;
          {
            sorry
          }
          {
            sorry
          }
        }
        {
          generalize Hx': HA'.stlc_ty_subst ▸ x = x';
          exists x';
          apply And.intro;
          {
            sorry
          }
          {
            sorry
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