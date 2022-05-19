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
            = Ty.interp.bind_val a x' := sorry;
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
            G x x' sorry
          ]
          rw [IB']
          sorry
        }
    | sigma => 
      stop
      cases a with
      | none => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_none]
      | some a => sorry
    | coprod => 
      stop
      cases a with
      | none => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_none]
      | some a => sorry
    | assume => 
      stop
      cases a with
      | none => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_none]
        apply propext
        apply Iff.intro <;> intro ⟨c, _⟩ <;> exact (c rfl).elim
      | some a => sorry
    | set => 
      stop
      cases a with
      | none => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_none]
        apply propext
        apply Iff.intro <;> 
        intro ⟨HAG, HφG⟩ <;>
        apply False.elim <;>
        apply HasType.denote_ty_non_null 
          (by first 
            | assumption 
            | (apply HasType.subst_sort <;> assumption)
          ) 
          HAG
      | some a => sorry
    | intersect => 
      stop
      cases a with
      | none => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_none]
        apply propext
        apply Iff.intro <;> intro ⟨c, _⟩ <;> exact (c rfl).elim
      | some a => sorry
    | union => 
      stop
      cases a with
      | none => 
        dsimp only [Term.denote_ty]
        rw [interp_eq_none]
        apply propext
        apply Iff.intro <;> intro ⟨c, _⟩ <;> exact (c rfl).elim
      | some a => sorry
    | dimplies => 
      stop
      cases a with
      | none => sorry
      | some a => cases a
    | dand => 
      stop
      cases a with
      | none => sorry
      | some a => cases a
    | or => 
      stop
      cases a with
      | none => sorry
      | some a => cases a
    | forall_ => 
      stop
      cases a with
      | none => sorry
      | some a => cases a
    | exists_ HA' Hφ =>
      cases a with
      | none => 
        dsimp only [Term.denote_ty];
        apply propext;
        apply Iff.intro <;>
        intro ⟨x, Hx⟩;
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