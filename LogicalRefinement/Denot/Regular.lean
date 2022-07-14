import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc
import LogicalRefinement.Denot.Basic
import LogicalRefinement.Denot.Wk
import LogicalRefinement.Denot.Subst

open AnnotSort
open Annot

theorem HasVar.denote_annot
  (Hv: HasVar Γ n (HypKind.val s) A)
  (HΓ: IsCtx Γ)
  (G: Γ.upgrade.stlc.interp)
  (HG: G ⊧ ✓Γ)
  : (expr s A).denote G ((HΓ.var Hv).stlc.interp G.downgrade)
  := by {
    induction Γ generalizing s n A with
    | nil => cases Hv
    | cons H Γ I =>   
      cases H with
      | mk A k =>
        cases k with
        | val s => 
          cases HΓ with
          | cons_val HΓ HA =>
            cases s <;> (
              let (x, G) := G;
              have ⟨Hx, HG⟩ := HG;
              cases Hv with
              | zero =>
                simp only [denote, Context.stlc]
                apply HA.denote_wk1 _ G _ _ _ Hx
                rw [Stlc.Context.interp.downgrade]
                rw [Stlc.HasType.interp_var]
                dsimp only [Stlc.HasVar.interp, Sparsity.ix]
                simp only [Eq.mp, Eq.mpr]
                conv =>
                  rhs
                  rw [monorecursor]
                  skip
                  rw [<-A.stlc_ty_wk1]
              | succ Hv => 
                have I' := I Hv HΓ G HG;
                cases s <;> (
                  simp only [denote, Context.stlc]
                  apply (HΓ.var_valid Hv).denote_wk1 _ G _ _ _ I';
                  rw [monorecursor]
                  rename Nat => n;
                  rw [Stlc.HasType.interp_transport_mono]
                  rw [Stlc.Context.interp.downgrade]
                  rw [Stlc.HasType.var_interp_wk1]
                  rfl
                  rw [Term.stlc_var]
                  constructor
                  rw [Term.stlc_ty_wk1]
                  exact Hv.stlc
                  rw [Term.stlc_var]
                  rw [Term.stlc_ty_wk1]
                  rfl
                  rw [Term.stlc_ty_wk1]
                  rfl
                )
            )
        | gst => 
          cases Hv with
          | succ Hv => 
            cases HΓ with
            | cons_gst HΓ => 
              let (x, G) := G;
              have ⟨_, HG⟩ := HG;
              have I' := I Hv HΓ G HG;
              cases s <;> (
                simp only [denote, Context.stlc]
                apply (HΓ.var_valid Hv).denote_wk1 _ G _ _ _ I';
                rw [monorecursor]
                rename Nat => n;
                rw [Stlc.HasType.interp_transport_mono]
                rw [Stlc.Context.interp.downgrade]
                rw [Stlc.HasType.var_interp_wk1]
                rfl
                rw [Term.stlc_var]
                constructor
                rw [Term.stlc_ty_wk1]
                exact Hv.stlc
                rw [Term.stlc_var]
                rw [Term.stlc_ty_wk1]
                rfl
                rw [Term.stlc_ty_wk1]
                rfl
              )
  }

theorem HasType.stlc_ty_let_bin' {X Γ A s b} (H: (X::Γ) ⊢ A: sort s):
  ((A.wknth 1).alpha0 b).stlc_ty = A.stlc_ty
  := by {
    simp only [Term.alpha0]
    rw [(H.wk2).stlc_ty_subst]
    rw [Term.stlc_ty_wknth]
    exact Hyp.unit;
  }

--TODO: this is probably much cleaner when done by substitution composition...
theorem HasType.stlc_ty_let_bin {Γ A s b} (H: Γ ⊢ A: sort s):
  ((A.wknth 1).alpha0 b).stlc_ty = A.stlc_ty
  := by {
    cases Γ with
    | nil => 
      rw [A.wknth_closed]
      exact H.stlc_ty_subst;
      rw [<-Nat.le_zero_eq]
      exact H.fv;
    | cons => exact H.stlc_ty_let_bin'
  }

theorem HasType.denote_subst_let_bin
  {A B X Y: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} 
  {a: Option A.stlc_ty.interp}
  {b: Term}
  {a': Option ((A.wknth 1).alpha0 b).stlc_ty.interp}
  {x: Option X.stlc_ty.interp}
  {y: Option Y.stlc_ty.interp}
  {Ixy: Option B.stlc_ty.interp}
  {sa sb sx sy: AnnotSort}
  (Hb: ((Hyp.mk Y (HypKind.val sy))::(Hyp.mk X (HypKind.val sx))::Γ) ⊢ b: expr sb B.wk1.wk1)
  (HΓ: IsCtx Γ)
  (HG: G ⊧ ✓Γ)
  (HA: ({ ty := B, kind := HypKind.val sb } :: Γ) ⊢ A: sort sa)
  (HB: Γ ⊢ B: sort sb)
  (HX: Γ ⊢ X: sort sx)
  (HY: ({ ty := X, kind := HypKind.val sx } :: Γ) ⊢ Y: sort sy)
  (Hx: X.denote_ty G x)
  (Hy: @Term.denote_ty Y (X.stlc_ty::Γ.upgrade.stlc) (x, G) y)
  (Ha': a' = HA.stlc_ty_let_bin ▸ a)
  (HIxy: Ixy = Term.stlc_ty_wk1 _ ▸ Term.stlc_ty_wk1 _ ▸ Hb.stlc.interp (y, x, G.downgrade))
  : @Term.denote_ty A (B.stlc_ty::Γ.upgrade.stlc) (Ixy, G) a =
    @Term.denote_ty ((A.wknth 1).alpha0 b) (Y.stlc_ty::X.stlc_ty::Γ.upgrade.stlc) (y, x, G) a'
  := by {
    rw [
      <-Hb.denote_val_alpha0''
        (HΓ.cons_val HX)
        (by exact ⟨Hx, HG⟩) --TODO: why is by exact necessary here?
        HB.wk1
        HY
        Hy
        HA.wk2_sort
        (doublecast_self _)
        rfl
        rfl
        rfl
        rfl
        rfl
    ]
    rw [Stlc.Context.interp.downgrade]
    rw [HIxy]
    let Db := Annot.stlc_ty_wk ▸ Hb.stlc.interp (y, x, G.downgrade);
    rw [<-HA.denote_wk2_eq'
        Db _
        _ _ _ _
        (by rw [Ha', rec_to_cast', rec_to_cast', cast_merge])
        (by 
          apply congr
          . rw [Term.stlc_ty_wk1]
          . rfl
        )
        (by
          simp only [rec_to_cast']
          rw [
            cast_pair'
             (by simp only [Term.stlc_ty_wk1])
             rfl
             (by simp only [Term.stlc_ty_wk1])
            ]
          rw [cast_merge]
          rfl
        )
    ]
  }

theorem HasType.denote_subst_let_pair
  {A B C: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} 
  {c: Option C.stlc_ty.interp}
  {c': Option ((C.wknth 1).alpha0 (Term.pair (Term.var 1) (Term.var 0))).stlc_ty.interp}
  {a: A.stlc_ty.interp}
  {b: B.stlc_ty.interp}
  {sc: AnnotSort}
  (HC: ({ ty := Term.sigma A B, kind := HypKind.val type } :: Γ) ⊢ C: sort sc)
  (HΓ: IsCtx Γ)
  (HG: G ⊧ ✓Γ)
  (HA: Γ ⊢ A: sort type)
  (HB: ((Hyp.mk A (HypKind.val type))::Γ) ⊢ B: sort type)
  (Ha: A.denote_ty G (some a))
  (Hb: @Term.denote_ty B (A.stlc_ty::Γ.upgrade.stlc) (some a, G) (some b))
  (Hc': c' = HC.stlc_ty_let_bin ▸ c)
  : @Term.denote_ty C ((Term.sigma A B).stlc_ty::Γ.upgrade.stlc) (some (a, b), G) c =
    @Term.denote_ty 
      ((C.wknth 1).alpha0 (Term.pair (Term.var 1) (Term.var 0))) 
      (B.stlc_ty::A.stlc_ty::Γ.upgrade.stlc) (some b, some a, G) c'
  := HasType.denote_subst_let_bin
    (by
      rw [<-Term.wk1_wk1_wkn2]
      constructor 
        <;> constructor 
        <;> (try exact HasType.wk_sort (by assumption) (by repeat constructor))
        <;> simp only [Term.lift_wkn2_subst0_var1, Term.wk1_wk1_wkn2]
        <;> repeat first | constructor | assumption | apply HasType.wk1_sort
    ) 
    HΓ HG HC (by constructor <;> assumption) HA HB 
    Ha Hb
    Hc' 
    (by 
      rw [
        Stlc.HasType.interp_pair
        _
        (by
          simp only [Annot.stlc_ty]
          rw [Term.stlc_ty_wk1, Term.stlc_ty_wk1]
          rfl
        )
        (by repeat constructor)
        (by repeat constructor)
      ]
      simp only [rec_to_cast', cast_merge]
      rfl
    )

theorem HasType.denote_subst_let_set
  {A B C: Term} {Γ: Context} {G: Γ.upgrade.stlc.interp} 
  {c: Option C.stlc_ty.interp}
  {c': Option ((C.wknth 1).alpha0 (Term.elem (Term.var 1) (Term.var 0))).stlc_ty.interp}
  {a: A.stlc_ty.interp}
  {b: Option B.stlc_ty.interp}
  {sc: AnnotSort}
  (HC: ({ ty := Term.set A B, kind := HypKind.val type } :: Γ) ⊢ C: sort sc)
  (HΓ: IsCtx Γ)
  (HG: G ⊧ ✓Γ)
  (HA: Γ ⊢ A: sort type)
  (HB: ((Hyp.mk A (HypKind.val type))::Γ) ⊢ B: sort prop)
  (Ha: A.denote_ty G (some a))
  (Hb: @Term.denote_ty B (A.stlc_ty::Γ.upgrade.stlc) (some a, G) b)
  (Hc': c' = HC.stlc_ty_let_bin ▸ c)
  : @Term.denote_ty C ((Term.set A B).stlc_ty::Γ.upgrade.stlc) (some a, G) c =
    @Term.denote_ty 
      ((C.wknth 1).alpha0 (Term.elem (Term.var 1) (Term.var 0))) 
      (B.stlc_ty::A.stlc_ty::Γ.upgrade.stlc) (b, some a, G) c'
  := HasType.denote_subst_let_bin
    (by
      rw [<-Term.wk1_wk1_wkn2]
      constructor 
        <;> constructor 
        <;> (try exact HasType.wk_sort (by assumption) (by repeat constructor))
        <;> simp only [Term.lift_wkn2_subst0_var1, Term.wk1_wk1_wkn2]
        <;> repeat first | constructor | assumption | apply HasType.wk1_sort
    ) 
    HΓ HG HC (by constructor <;> assumption) HA HB 
    Ha Hb
    Hc' 
    (by 
      dsimp only [Stlc.HasType.interp, Stlc.HasVar.interp, Eq.mp]
      simp only [rec_to_cast', cast_merge]
      rfl
    )

theorem HasType.denote
  (H: Γ ⊢ a: A)
  (HΓ: IsCtx Γ)
  (G: Γ.upgrade.stlc.interp)
  (HG: Γ.denote G)
  : A.denote G (H.stlc.interp G.downgrade)
  := by {
    --TODO: replace with a recursive match?
    induction H with
    | var HA Hv IA => exact Hv.denote_annot HΓ G HG
    | lam Hs HA Is IA =>
      stop
      intro x Hx
      cases x with
      | some x => exact Is (HΓ.cons_val HA) _ ⟨Hx, HG⟩
      | none => exact False.elim (HA.denote_ty_non_null Hx)
    | @app Γ A B l r HAB Hl Hr IA Il Ir =>
      stop
      dsimp only [Annot.denote]
      dsimp only [
        Annot.stlc_ty, term, Term.stlc_ty, Term.stlc, 
        Stlc.HasType.interp, 
        Ty.interp.app
      ]
      generalize Hlg:
        Stlc.HasType.interp
        (_ : _⊧Term.stlc l:_)
        (Stlc.Context.interp.downgrade G) = li;
      have Il' := Hlg ▸ (Il HΓ G HG);
      generalize Hrg:
        Stlc.HasType.interp
        (_ : _⊧Term.stlc r:_)
        (Stlc.Context.interp.downgrade G) = ri;
      have Ir' := Hrg ▸ (Ir HΓ G HG);
      have HA: Γ ⊢ A: type := by cases HAB; assumption;
      have HB: ((Hyp.val A type)::Γ) ⊢ B: type := 
        by cases HAB; assumption;
      cases li with
      | some li => 
        cases ri with
        | some ri => 
          have Ilr := Il' (some ri) Ir';
          simp only []
          dsimp only [Annot.denote, Term.denote_ty] at Il'
          dsimp only [Annot.denote, Term.denote_ty]
          rw [<-Hr.denote_val_subst0' HΓ HG HB HB.stlc_ty_subst.symm _ Hrg.symm];
          exact Ilr
          rw [monorecursor]
          rfl
        | none => exact False.elim (HA.denote_ty_non_null Ir')
      | none => exact False.elim (HAB.denote_ty_non_null Il')
    | @pair Γ A B l r HAB Hl Hr IAB Il Ir =>
      stop
      dsimp only [Term.denote_ty, 
        Stlc.HasType.interp, Term.stlc, stlc_ty, term, Term.stlc_ty, 
        Ty.interp.pair]
      generalize Hli: Stlc.HasType.interp _ _ = li;
      have Il' := Hli ▸ Il HΓ G HG;
      generalize Hri: Stlc.HasType.interp _ _ = ri;
      have HB: (_::Γ) ⊢ B: type := by cases HAB; assumption;
      have Ir' := Ir HΓ G HG;
      cases li with
      | some li => 
        cases ri with
        | some ri => 
          simp only [pure]
          apply And.intro;
          {
            exact Il'
          }
          {
            simp only [<-Hli, <-Hri]
            rw [denote_val_subst0']
            exact Ir';
            assumption
            assumption
            assumption
            assumption
            rw [HB.stlc_ty_subst0]
            rw [rec_to_cast']
            stop
            rw [Stlc.HasType.interp_transport_cast']
            rfl
            rw [HB.stlc_ty_subst0]
            rfl
          }
        | none => 
          apply Hr.term_regular.denote_ty_non_null
          apply Term.denote_ty_transport rfl rfl rfl _ Ir'
          simp only []
          rw [<-Stlc.HasType.interp_transport_inner _ _ rfl HB.stlc_ty_subst.symm]
          exact (interp_eq_none' Hri).symm
      | none => exact Hl.term_regular.denote_ty_non_null Il'
    | @let_pair Γ A B C e e' He HA HB HC He' Ie IA IB IC Ie' =>
      stop
      have De := Ie HΓ G HG;
      dsimp only [
        Term.denote_ty, Term.stlc, Annot.denote,
        stlc_ty, Term.stlc_ty, Stlc.HasType.interp
      ] at *;
      generalize HSe: He.stlc.interp G.downgrade = Se;
      rw [HSe] at De;
      cases Se with
      | some p => 
        cases p with
        | mk a b =>
          have ⟨Da, Db⟩ := De;    
          simp only [Ty.interp.let_pair, Option.bind]
          have De' := 
            Ie' ((HΓ.cons_val HA).cons_val HB) 
            (some b, some a, G)
            ⟨Db, Da, HG⟩
            ;
          rw [
            <-He.denote_val_subst0' HΓ HG HC 
            (by rw [HC.stlc_ty_subst0])
            (by rw [rec_to_cast']; rw [cast_trans])
            rfl
            ]
          rw [HSe]
          rw [HC.denote_subst_let_pair HΓ HG HA HB Da Db rfl]
          rw [rec_to_cast', cast_merge]
          apply equiv_prop_helper De';
          apply congr rfl _;
          rw [Stlc.HasType.interp_transport_cast']
          rfl
          rfl
          rw [HC.stlc_ty_let_bin, HC.stlc_ty_subst0]
      | none => exact False.elim De;
    | inj_l He HB Ie IB => 
      stop
      dsimp only [
        Term.denote_ty, Term.stlc, 
        stlc_ty, Term.stlc_ty, Stlc.HasType.interp,
        Ty.interp.inl
      ]
      generalize Hei: Stlc.HasType.interp _ _ = ei;
      have Ie' := Hei ▸ Ie HΓ G HG;
      cases ei with
      | some ei => 
        dsimp only [Option.map, Option.bind, Function.comp]
        exact Ie'
      | none => exact He.term_regular.denote_ty_non_null Ie'
    | inj_r He HA Ie IA => 
      stop
      dsimp only [
        Term.denote_ty, Term.stlc, 
        stlc_ty, Term.stlc_ty, Stlc.HasType.interp,
        Ty.interp.inl
      ]
      generalize Hei: Stlc.HasType.interp _ _ = ei;
      have Ie' := Hei ▸ Ie HΓ G HG;
      cases ei with
      | some ei => 
        dsimp only [Option.map, Option.bind, Function.comp]
        exact Ie'
      | none => exact He.term_regular.denote_ty_non_null Ie'
    | @case Γ A B C e l r He HA HB HC Hl Hr Ie IA IB IC Il Ir =>
      stop
      have HAB: Γ ⊢ Term.coprod A B: type := HasType.coprod HA HB;
      cases k with
      | type => 
        dsimp only [Term.stlc, Term.stlc_ty, stlc_ty, Stlc.HasType.interp]
        have Ie' := Ie HΓ G HG;
        dsimp only [Term.stlc, Term.stlc_ty, stlc_ty, Stlc.HasType.interp] at Ie';
        generalize Hei: Stlc.HasType.interp (_ : _⊧Term.stlc e:_) _ = ei;
        --TODO: wait for Zulip to answer regarding the requirement to have
        -- Stlc.HasType.interp_irrel here.
        rw [Stlc.HasType.interp_irrel] at Ie'
        rw [Hei] at Ie'
        cases ei with
        | some ei => 
          cases ei with
          | inl a => 
            simp only [Ty.interp.case]
            have Il' := Il 
              (HΓ.cons_val HA)
              (return a, G)
              ⟨Ie', HG⟩
              ;
            sorry --TODO: appropriate typecasting for Il'
          | inr b => 
            simp only [Ty.interp.case]
            have Ir' := Ir
              (HΓ.cons_val HB)
              (return b, G)
              ⟨Ie', HG⟩
              ;
            sorry --TODO: appropriate typecasting for Ir'
        | none => exact False.elim (HAB.denote_ty_non_null Ie')
      | prop => 
        have Ie' := Ie HΓ G HG;
        dsimp only [
          Term.stlc, Term.stlc_ty, stlc_ty, Stlc.HasType.interp] 
          at Ie';
        generalize Hei: Stlc.HasType.interp (_ : _⊧Term.stlc e:_) _ = ei;
        rw [Stlc.HasType.interp_irrel] at Ie'
        rw [Hei] at Ie'
        cases ei with
        | some ei => 
          cases ei with
          | inl a => 
            simp only [Ty.interp.case]
            have Il' := Il 
              (HΓ.cons_val HA)
              (return a, G)
              ⟨Ie', HG⟩
              ;
            sorry --TODO: appropriate typecasting for Il'
          | inr b => 
            simp only [Ty.interp.case]
            have Ir' := Ir
              (HΓ.cons_val HB)
              (return b, G)
              ⟨Ie', HG⟩
              ;
            sorry --TODO: appropriate typecasting for Ir'
        | none => exact False.elim (HAB.denote_ty_non_null Ie')
        exact He.stlc
    | elem =>
      stop 
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      apply And.intro;
      {
        sorry
      }
      {
        sorry
      }
    | @let_set Γ A B C e e' He HA HB HC He' Ie IA IB IC Ie' =>       
      have De := Ie HΓ G HG;
      dsimp only [
        Term.denote_ty, Term.stlc, Annot.denote,
        stlc_ty, Term.stlc_ty, Stlc.HasType.interp
      ] at *;
      generalize HSe: He.stlc.interp G.downgrade = Se;
      rw [HSe] at De;
      have ⟨Da, Db⟩ := De;
      cases Se with
      | some a => 
        simp only [Ty.interp.let_pair, Option.bind]
        have De' := 
          Ie' ((HΓ.cons_val HA).cons_val HB) 
          (none, some a, G)
          ⟨Db, Da, HG⟩
          ;
        rw [
          <-He.denote_val_subst0' HΓ HG HC 
          (by rw [HC.stlc_ty_subst0])
          (by rw [rec_to_cast']; rw [cast_trans])
          rfl
          ]
        rw [HSe]
        simp only [Ty.interp.pair, Option.bind]
        rw [HC.denote_subst_let_set HΓ HG HA HB Da Db rfl]
        rw [rec_to_cast', cast_merge]
        apply equiv_prop_helper De';
        apply congr rfl _;
        rw [Stlc.HasType.interp_transport_cast']
        simp only [Stlc.Context.interp.downgrade]
        rw [
          @HasType.interp_irrel_ty
          ({ ty := B, kind := HypKind.val prop } ::
           { ty := A, kind := HypKind.val type } :: Γ) 
          ({ ty := B, kind := HypKind.val prop } ::
           { ty := A, kind := HypKind.val type } :: Γ)  
          _ _
          (none, some a, G.downgrade)
          (HB.prop_is_unit ▸ some (), some a, G.downgrade)
          He'
          He'
          (@Stlc.Context.interp.eq_mod_lrt.extend_prop 
            (A.stlc_ty::Γ.stlc) (A.stlc_ty::Γ.stlc) B _ _ 
            (some a, G.downgrade) 
            (some a, G.downgrade)
            _
            _
              (Stlc.Context.interp.eq_mod_lrt_refl 
                _
                ({ ty := A, kind := HypKind.val type } :: Γ)
                ({ ty := A, kind := HypKind.val type } :: Γ))
          )
        ]
        let f: 
          (Γ : Stlc.Context) → 
          (a : Stlc) → 
          (Γ ⊧ a : (Term.stlc_ty (Term.alpha0 (Term.wknth C 1) (Term.elem (Term.var 1) (Term.var 0))))) →
          Γ.interp →
          Option ((Term.stlc_ty (Term.alpha0 (Term.wknth C 1) (Term.elem (Term.var 1) (Term.var 0))))).interp 
          := λ Γ a => @Stlc.HasType.interp Γ a (Term.stlc_ty (Term.alpha0 (Term.wknth C 1) (Term.elem (Term.var 1) (Term.var 0))));
        have Hf: ∀ Γ a, @Stlc.HasType.interp Γ a (Term.stlc_ty (Term.alpha0 (Term.wknth C 1) (Term.elem (Term.var 1) (Term.var 0)))) = f Γ a := by intros; rfl;
        rw [Hf]
        apply 
          cast_app_dep_three f
          _ _ _ _ _ _ _ _ 
          (by rw [Context.stlc, HB.prop_is_unit]; rfl)
          rfl rfl 
          (by
            rw [cast_pair']
            rw [rec_to_cast']
            rfl
            rfl
            apply equiv_prop_helper He'.stlc;
            rw [Context.stlc, HB.prop_is_unit]; rfl
          )
        ;
        rfl
        simp only [
          Term.wknth, <-Subst.subst_wk_compat, Term.alpha0, 
          Term.subst_composes, Term.subst0, HC.stlc_ty_subst
        ]
      | none => exact False.elim (HA.denote_ty_non_null Da);
    | lam_pr Hϕ Hs _Iϕ Is => 
      stop
      dsimp only [
        Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty
      ] at *
      let Is' := Is (HΓ.cons_val Hϕ) (none, G) ⟨sorry, HG⟩;
      sorry
    | app_pr HφA Hl Hr IφA Il Ir =>
      stop
      dsimp only [Term.denote_ty]
      sorry
    | lam_irrel => 
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      apply And.intro
      {
        sorry
      }
      {
        sorry
      }
    | app_irrel =>
      stop  
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      sorry
    | @repr Γ A B l r HAB Hl Hr IAB Il Ir =>
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
      apply And.intro
      . sorry -- not_none + Ir?
      . exists Hl.stlc.interp G
        sorry
    | let_repr =>
      stop  
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ]
    | abort Hp HA Ip IA => stop exact False.elim (Ip HΓ G HG)
    | @dconj Γ A B l r HAB Hl Hr IAB Il Ir => 
      dsimp only [
        Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty
      ] at *
      apply And.intro
      apply HasType.denote_prop_none;
      cases HAB; assumption
      exact Il HΓ G HG;
      have Ir' := Ir HΓ G HG;
      apply equiv_prop_helper Ir';
      simp only [Annot.denote]
      rw [@HasType.eq_lrt_ty_denot' ((Hyp.mk A (HypKind.val prop))::Γ) _ _ _ (none, G)]
      rw [
        Hl.denote_val_subst0' HΓ HG 
        (by cases HAB; assumption)
        (by rw [HasType.stlc_ty_subst0]; cases HAB; assumption)
        rfl
        rfl
      ];
      rw [rec_to_cast']
      rw [cast_none']
      rw [HasType.denote_prop_eq]
      exact Hr.proof_regular
      rw [HasType.stlc_ty_subst0]
      cases HAB <;> assumption
      cases HAB <;> assumption
      {
        apply Stlc.Context.interp.eq_mod_lrt.extend_prop;
        apply Stlc.Context.interp.eq_mod_lrt_refl;
      }
    | let_conj He HA HB HC He' Ie _IA _IB _IC Ie' =>
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ] at *
      --TODO: alpha0 theorems...
      sorry
    | disj_l He _ Ie _ => 
      exact Or.inl (He.proof_regular.denote_prop_none (Ie HΓ G HG))
    | disj_r He _ Ie _ => 
      exact Or.inr (He.proof_regular.denote_prop_none (Ie HΓ G HG))
    | case_pr He HA HB HC Hl Hr Ie IA IB IC Il Ir => 
      stop
      dsimp only [
        denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty', Term.denote_ty
      ] at *
      have Ie' := Ie HΓ G HG;
      cases Ie' with
      | inl Ie' => 
        have Il' := Il (IsCtx.cons_val HΓ HA) G ⟨Ie', HG⟩;
        sorry
      | inr Ie' =>  
        have Ir' := Ir (IsCtx.cons_val HΓ HB) G ⟨Ie', HG⟩;
        sorry
    | imp Hϕ Hs Iϕ Is => stop 
      exact λDϕ => Hs.proof_regular.denote_prop_none (Is (IsCtx.cons_val HΓ Hϕ) (none, G) ⟨Dϕ, HG⟩);
    | @mp Γ φ ψ l r Hϕψ Hl Hr _ Il Ir => 
      stop
      dsimp only [
        Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty, Ty.abort, Annot.denote
      ] at *
      have Hψ: _ ⊢ ψ: prop := by cases Hϕψ <;> assumption;
      rw [<-Hr.denote_prop_subst0 HΓ HG]
      exact Il HΓ G HG (Hr.proof_regular.denote_prop_none (Ir HΓ G HG))
      exact Hψ;
      rw [Hψ.stlc_ty_subst0]
      rw [interp_eq_none]
    | general HA Hs IA Is => stop
      exact λx Dx => Hs.proof_regular.denote_prop_none 
        (Is (IsCtx.cons_val HΓ HA) (x, G) ⟨Dx, HG⟩);
    | inst HAϕ Hl Hr _ Il Ir => 
      stop
      dsimp only [
        Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty, Ty.abort, Annot.denote
      ] at *
      --TODO: ghost denotation...
      -- rw [<-Hr.denote_val_subst0]
      -- apply Il HΓ G HG;
      -- -- Double upgrade
      -- sorry
      repeat sorry
    | @wit Γ A φ l r HAφ Hl Hr IAφ Il Ir =>
      stop
      exists Hl.stlc.interp G
      have Il' := Il HΓ.upgrade (Context.upgrade_idem.symm ▸ G) HG.upgrade;
      apply And.intro
      . sorry
      . sorry
    | let_wit => sorry
    | case_prop => sorry
    | @let_pair_prop Γ A B C e e' He HA HB HC He' Ie IA IB IC Ie' =>
      stop 
      have De := Ie HΓ.upgrade (Context.upgrade_idem.symm ▸ G) HG.upgrade;
      dsimp only [
        Term.denote_ty, Term.stlc, Annot.denote,
        stlc_ty, Term.stlc_ty, Stlc.HasType.interp
      ] at *;
      generalize HSe: He.stlc.interp G = Se;
      rw [rec_to_cast'] at De;
      rw [Stlc.Context.interp.downgrade_cast] at De;
      rw [HSe] at De;
      cases Se with
      | some p => 
        cases p with
        | mk a b =>
          have ⟨Da, Db⟩ := De;    
          rw []
          simp only [Ty.abort]
          have De' := 
            Ie' (
            (HΓ.upgrade.cons_val HA.upgrade).cons_val HB) 
            (some b, some a, (cast (by rw [Context.upgrade_idem]) G))
            ⟨Db, Da, rec_to_cast' ▸ HG.upgrade⟩
            ;
          rw [Term.denote_upgrade_eq]
          rw [
            <-He.denote_val_subst0'
            HΓ.upgrade
            HG.upgrade
            HC
            (by rw [HC.stlc_ty_subst0])
            (by rw [interp_eq_none])
            rfl
            ]
          rw [rec_to_cast']
          rw [Stlc.Context.interp.downgrade_cast]
          rw [HSe]
          rw [
            HC.denote_subst_let_pair HΓ.upgrade 
            (by --TODO: why can't we just do rec_to_cast' ▸ HG.upgrade
              have HG' := HG.upgrade; 
              rw [rec_to_cast'] at HG';
              exact HG'
            ) HA.upgrade HB
            Da Db rfl
          ]
          apply equiv_prop_helper De';
          rw [HasType.denote_prop_eq']
          apply HC.wk2_sort.alpha0_sort;
          apply @HasType.pair 
            ((Hyp.mk B (HypKind.val type))
              ::(Hyp.mk A (HypKind.val type))
              ::Γ.upgrade);
          {
            constructor;
            exact HA.upgrade.wk1_sort.wk1_sort;
            simp only [Term.wk_composes]
            apply HB.wk_sort;
            repeat constructor
          }
          {
            constructor
            exact HA.upgrade.wk1_sort.wk1_sort;
            constructor
            constructor
          }
          {
            rw [Term.lift_wk1_wk1_subst0_var1]
            constructor
            exact HB.wk1_sort;
            constructor
          }
            
      | none => exact False.elim De;
    | let_set_prop => sorry
    | let_repr_prop => sorry
    | refl Ha => stop exact ⟨Ha.stlc, Ha.stlc, rfl⟩
    | discr Ha Hb Hp Ia Ib Ip => sorry
    | cong => 
      stop
      dsimp only [denote', Annot.denote]
      sorry
    | beta Hs HA Ht Is _IA It => 
      stop
      dsimp only [
        Stlc.HasType.interp, 
        Term.stlc, Term.stlc_ty, stlc_ty, Term.denote_ty,
        Ty.abort, Annot.denote
      ]
      exact ⟨
        by {
          rw [Hs.expr_regular.stlc_ty_subst0]
          constructor
          constructor
          exact Hs.stlc;
          exact Ht.stlc
        },
        (Hs.subst0 Ht).stlc,
        sorry
      ⟩
    | beta_ir Hs HA Ht Is _IA It =>
      stop
      dsimp only [
        Stlc.HasType.interp, 
        Term.stlc, Term.stlc_ty, stlc_ty, Term.denote_ty,
        Ty.abort, Annot.denote
      ]
      exact ⟨
        by {
          rw [Hs.expr_regular.stlc_ty_subst0]
          constructor
          constructor
          exact Hs.stlc;
          constructor
        },
        (Context.upgrade_idem ▸ Hs.upgrade.subst0 Ht.upgrade).stlc,
        sorry
      ⟩
    | beta_pr Hs HA Ht Is _IA It => 
      stop
      dsimp only [
        Stlc.HasType.interp, 
        Term.stlc, Term.stlc_ty, stlc_ty, Term.denote_ty,
        Ty.abort, Annot.denote
      ]
      exact ⟨
        by {
          rw [Hs.expr_regular.stlc_ty_subst0]
          constructor
          constructor
          exact HA.prop_is_unit ▸ Hs.stlc;
          constructor
        },
        (Hs.subst0 Ht).stlc,
        sorry
      ⟩
    | @eta Γ A B f Hf HA If IA => stop
      have pe
        : Γ.upgrade.stlc ⊧ (Term.eta_ex A B f).stlc
          : Ty.arrow A.stlc_ty B.stlc_ty 
        := by {
          constructor
          dsimp only [Term.stlc]
          have H: 
            Term.stlc 
              (Term.app (Term.pi (Term.wk1 A) (Term.wknth B 1)) 
                (Term.wk1 f) (Term.var 0))
          = Stlc.app (Ty.arrow A.stlc_ty B.stlc_ty) 
            (f.wk1.stlc)
            (Stlc.var 0)
          := by {
            dsimp only [Term.stlc];
            apply congr _ rfl;
            apply congr _ rfl;
            simp only [Term.stlc_ty, Term.wk1, Term.wknth, Term.stlc_ty_wk]
          };
          rw [H]
          constructor
          have Hf': ((Hyp.val A type)::Γ.upgrade) ⊢ f.wk1: _ := Hf.wk1;
          have Hf'' := Hf'.stlc;
          simp only [stlc_ty, Annot.wk1, term, Term.stlc_ty_wk, Annot.wk] at Hf'';
          exact Hf'';
          constructor
          constructor
        };
      have pf
        : Γ.upgrade.stlc ⊧ f.stlc
          : Ty.arrow A.stlc_ty B.stlc_ty 
        := Hf.stlc;
      --TODO: get rid of double upgrade...
      have If' := If HΓ.upgrade (Context.upgrade_idem.symm ▸ G) HG.upgrade;
      have HAB := Hf.term_regular;
      have ⟨yi, Hyi⟩ := HAB.denote_ty_some If';
      exists pe, pf;
      unfold Term.eta_ex
      dsimp only [Term.stlc_ty, Stlc.HasType.interp, Term.stlc]
      simp only []
      generalize Hsf: Stlc.HasType.interp pf G = sf;
      cases sf with
      | some sf => 
        apply congr rfl;
        funext x;
        generalize Hwf: Stlc.HasType.interp 
          (_: _ ⊧ f.wk1.stlc: _)
          _ = wf;
        {
          have H: cast (by simp only [Term.wk1, Term.wknth, Term.stlc_ty_wk]) wf 
            = some sf := by {
              rw [<-Hsf, <-Hwf];
              rw [Stlc.HasType.interp_wk1']
              apply Stlc.HasType.interp_transport_cast'';
              rfl
              simp only [Term.wk1, Term.wknth, Term.stlc_ty_wk]
              rfl
              rfl
              simp only [Term.wk1, Term.wknth, Term.stlc_ty_wk]
              exact Hf.stlc;
              simp only [Term.wk1, Stlc.wk1, Term.wk_stlc_commute]
            }
          cases wf with
          | some wf =>
            simp only [
              Ty.interp.app, Stlc.HasVar.interp,
              Option.bind, pure, mp_to_cast
            ]
            rw [cast_some]
            simp only []
            rw [cast_tri']
            apply congr _ rfl;
            simp only [Term.wk1, Term.stlc_ty_wk]
            simp only [Term.wknth, Term.stlc_ty_wk]
            rw [cast_some] at H;
            apply some_eq_helper H;
          | none => 
            stop
            rw [cast_none'] at H;
            contradiction
            simp only [Term.wk1, Term.wknth, Term.stlc_ty_wk]
        }
      | none => 
        dsimp only [Term.denote_ty] at If'
        simp only [Eq.rec] at If';
        generalize Hsf': Stlc.HasType.interp _ _ = sf';
        rw [Hsf'] at If';
        cases sf' with
        | some sf' => 
          have C: some sf' = none := by {
            rw [<-Hsf]
            rw [<-Hsf']
            rw [rec_to_cast']
            rw [Stlc.Context.interp.downgrade_cast]
            rfl
          };
          contradiction
        | none => exact If'.elim
    | irir Hf Hx Hy => 
      stop
      exact ⟨
        by {
          simp only [Term.irir_ex, Term.const_arrow]
          dsimp only [Term.stlc, Term.stlc_ty]
          rw [Term.stlc_ty_wk1]
          constructor
          {
            have Hf' := Hf.stlc;
            dsimp only 
              [stlc_ty, Term.const_arrow, Term.wk1, Term.stlc_ty] at Hf'
            rw [Term.stlc_ty_wk] at Hf'
            exact Hf'
          }
          constructor
        }, 
        by {
          simp only [Term.irir_ex, Term.const_arrow]
          dsimp only [Term.stlc, Term.stlc_ty]
          rw [Term.stlc_ty_wk1]
          constructor
          {
            have Hf' := Hf.stlc;
            dsimp only 
              [stlc_ty, Term.const_arrow, Term.wk1, Term.stlc_ty] at Hf'
            rw [Term.stlc_ty_wk] at Hf'
            exact Hf'
          }
          constructor
        }, 
        rfl
      ⟩
    | prir HP HA Hx Hy _  _ Ix Iy =>
      stop
      dsimp only [
        Stlc.HasType.interp, 
        Term.stlc, Term.stlc_ty, stlc_ty, Term.denote_ty,
        Ty.abort, Annot.denote
      ]
      rw [<-Hx.denote_prop_subst0]
      intro Dx;
      rw [<-HasType.denote_wk1_eq]
      rw [<-Hy.denote_prop_subst0]
      exact Dx
      assumption
      assumption
      assumption
      rw [HP.stlc_ty_subst0]
      rfl
      exact HP.subst0_sort Hy;
      rw [interp_eq_none]
      rw [interp_eq_none]
      assumption
      assumption
      exact HP
      rw [HP.stlc_ty_subst0]
      rw [interp_eq_none]
      constructor
    | beta_left He HA HB HC Hl Hr Ie _IA _IB _IC Il Ir =>  
      stop
      dsimp only [
        Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty, Ty.abort, Annot.denote
      ]
      exact ⟨
        by {
          constructor
          constructor
          exact He.stlc;
          have Hl' := Hl.stlc;
          rw [HC.stlc_ty_subst0]
          simp only [Term.alpha0] at Hl';
          rw [Annot.stlc_ty_subst HC] at Hl';
          exact Hl'
          have Hr' := Hr.stlc;
          rw [HC.stlc_ty_subst0]
          simp only [Term.alpha0] at Hr';
          rw [Annot.stlc_ty_subst HC] at Hr';
          exact Hr'
        },
        by {
          have Hle := (Hl.subst0 He).stlc;
          simp only [
            Term.alpha0, Annot.subst0, Annot.subst, Term.subst_composes
          ] at Hle;
          rw [Annot.stlc_ty_subst HC] at Hle;
          rw [HC.stlc_ty_subst0]
          exact Hle
        },
        sorry
      ⟩
    | beta_right He HA HB HC Hl Hr Ie _IA _IB _IC Il Ir =>
      stop
      dsimp only [
        Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty, Ty.abort, Annot.denote
      ]
      exact ⟨
        by {
          constructor
          constructor
          exact He.stlc;
          have Hl' := Hl.stlc;
          rw [HC.stlc_ty_subst0]
          simp only [Term.alpha0] at Hl';
          rw [Annot.stlc_ty_subst HC] at Hl';
          exact Hl'
          have Hr' := Hr.stlc;
          rw [HC.stlc_ty_subst0]
          simp only [Term.alpha0] at Hr';
          rw [Annot.stlc_ty_subst HC] at Hr';
          exact Hr'
        },
        by {
          have Hre := (Hr.subst0 He).stlc;
          simp only [
            Term.alpha0, Annot.subst0, Annot.subst, Term.subst_composes
          ] at Hre;
          rw [Annot.stlc_ty_subst HC] at Hre;
          rw [HC.stlc_ty_subst0]
          exact Hre
        },
        sorry
      ⟩
    | beta_pair Hl Hr HA HB HC He Il Ir _IA _IB IC Ie =>
      stop
      dsimp only [
        Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty, Ty.abort, Annot.denote
      ]
      exact ⟨
        by {
          constructor;
          constructor;
          exact Hl.stlc;
          exact HB.stlc_ty_subst0 ▸ Hr.stlc;
          have He' := He.stlc;
          rw [HC.stlc_ty_subst0]
          simp only [
            Term.alpha0, Annot.subst0, Annot.subst, 
            Term.wknth, <-Subst.subst_wk_compat,
            Term.subst_composes
          ] at He';
          rw [Annot.stlc_ty_subst HC] at He';
          exact He'
        },
        by {
          have Hre := (He.subst01 Hr Hl).stlc;
          simp only [
            Term.alpha0, Annot.subst01, Annot.subst, 
            Term.subst_composes,
            Term.wknth, <-Subst.subst_wk_compat
          ] at Hre;
          rw [Annot.stlc_ty_subst HC] at Hre;
          rw [HC.stlc_ty_subst0]
          exact Hre
        },
        sorry
      ⟩
    | beta_set Hl Hr HA HB HC He Il Ir _IA _IB IC Ie =>
      stop        
      dsimp only [
        Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty, Ty.abort, Annot.denote
      ]
      exact ⟨
        by {
          constructor;
          constructor;
          exact Hl.stlc;
          constructor
          have He' := He.stlc;
          rw [HC.stlc_ty_subst0]
          simp only [
            Term.alpha0, Annot.subst0, Annot.subst, 
            Term.wknth, <-Subst.subst_wk_compat,
            Term.subst_composes, Context.stlc
          ] at He';
          rw [Annot.stlc_ty_subst HC] at He';
          rw [HB.prop_is_unit] at He';
          exact He'
        },
        by {
          have Hre := (He.subst01 Hr.upgrade Hl).stlc;
          simp only [
            Term.alpha0, Annot.subst01, Annot.subst, 
            Term.subst_composes,
            Term.wknth, <-Subst.subst_wk_compat
          ] at Hre;
          rw [Annot.stlc_ty_subst HC] at Hre;
          rw [HC.stlc_ty_subst0]
          exact Hre
        },
        sorry
      ⟩
    | beta_repr Hl Hr HA HB HC He Il Ir _IA _IB IC Ie => 
      stop     
      dsimp only [
        Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty, Ty.abort, Annot.denote
      ]
      exact ⟨
        by {
          constructor;
          constructor;
          constructor;
          exact HB.stlc_ty_subst0 ▸ Hr.stlc;
          have He' := He.stlc;
          rw [HC.stlc_ty_subst0]
          simp only [
            Term.alpha0, Annot.subst0, Annot.subst, 
            Term.wknth, <-Subst.subst_wk_compat,
            Term.subst_composes
          ] at He';
          rw [Annot.stlc_ty_subst HC] at He';
          exact He'
        },
        by {
          have Hre := (He.upgrade.subst01 Hr.upgrade Hl.upgrade).stlc;
          simp only [
            Term.alpha0, Annot.subst01, Annot.subst, 
            Term.subst_composes,
            Term.wknth, <-Subst.subst_wk_compat,
            Context.upgrade_idem
          ] at Hre;
          rw [Annot.stlc_ty_subst HC] at Hre;
          rw [HC.stlc_ty_subst0]
          exact Hre
        },
        sorry
      ⟩
    | succ => 
      stop
      intro x H;
      cases x with
      | none => cases H
      | some x => exact True.intro
    | @natrec Γ C e z s HC He Hz Hs IC Ie Iz Is =>
      stop
      generalize Hei:
        Stlc.HasType.interp
          He.stlc
          (Stlc.Context.interp.downgrade G) = ei;
      cases ei with
      | none => 
        have Ie' := Ie HΓ G HG;
        dsimp only [Term.denote_ty', Term.denote_ty] at Ie';
        rw [Hei] at Ie';
        exact Ie'.elim
      | some n =>
        cases k with
        | type =>
          dsimp only [
            denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
            Term.denote_ty', Term.denote_ty
          ]
          simp only []
          generalize Hei':
            Stlc.HasType.interp
              (_: _ ⊧ e.stlc _: _)
              (Stlc.Context.interp.downgrade G) = ei';
          induction n generalizing e with
          | zero => 
            cases ei' with
            | some n' =>
              cases n' with
              | zero => 
                simp only [
                  Ty.interp.natrec_int, Ty.interp.natrec_inner, 
                  Ty.interp.bind_val
                ]
                --TODO: subst0 invariance
                sorry
              | succ n' => sorry
            | none => sorry
          | succ n I =>
            cases ei' with
            | some n' =>
              cases n' with
              | zero => sorry
              | succ n' => 
                simp only [
                  Ty.interp.natrec_int, Ty.interp.natrec_inner, 
                  Ty.interp.bind_val
                ]
                generalize HIi': Ty.interp.natrec_inner n' _ _ = Ii;
                cases Ii with
                | none => 
                  apply False.elim;
                  sorry
                | some Ii => 
                  simp only []
                  --TODO: subst0 invariance, s application...
                  sorry
            | none => sorry
        | prop =>         
          dsimp only [
            denote', Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
            Term.denote_ty', Term.denote_ty
          ]
          induction n generalizing e with
          | zero => 
            --TODO: subst0 invariance...
            sorry
          | succ n I => 
            --TODO: subst0 invariance...
            sorry
    | natrec_prop => sorry
    | @beta_zero Γ C z s HC Hz Hs IC Iz Is => 
      stop
      dsimp only [
        Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty
      ]
      exists by {
        simp only [if_pos, HC.stlc_ty_subst, Term.subst0]
        exact 
          @Stlc.HasType.natrec
          Γ.upgrade.stlc
          _ _ _ _
          Stlc.HasType.zero
          (HC.stlc_ty_subst ▸ Hz.stlc)
          (by {
            have Hs' := Hs.stlc;
            simp only [
              Term.alpha0, Term.wknth, stlc_ty
            ] at Hs';
            rw [HasType.stlc_ty_subst] at Hs';
            rw [Term.stlc_ty_wk] at Hs';
            exact Hs';
            exact HC.wk_sort (by repeat constructor);
          })
      }, Hz.stlc;
    | @beta_succ Γ C e z s HC He Hz Hs IC Ie Iz Is => 
      stop
      dsimp only [
        Stlc.HasType.interp, Term.stlc, Term.stlc_ty, stlc_ty,
        Term.denote_ty, Ty.abort, Annot.denote
      ]
      exact ⟨
        by {
          stop
          rw [HC.stlc_ty_subst0]
          constructor
          constructor
          constructor
          exact He.stlc;
          exact HC.stlc_ty_subst0 ▸ Hz.stlc;
          have Hs' := Hs.stlc;
          simp only [
            Term.alpha0, Annot.subst0, Annot.subst, 
            Term.wknth, <-Subst.subst_wk_compat,
            Term.subst_composes
          ] at Hs';
          rw [Annot.stlc_ty_subst HC] at Hs';
          exact Hs'
        },
        by {
          have Hn := 
            HasType.natrec (by upgrade_ctx assumption) He Hz Hs;
          have Hs' := (Hs.subst01_gen_gst Hn He rfl).stlc;
          simp only [
            Term.alpha0, Annot.subst0, Annot.subst, 
            Term.wknth, <-Subst.subst_wk_compat,
            Term.subst_composes, Annot.subst01
          ] at Hs';
          rw [Annot.stlc_ty_subst HC] at Hs';
          rw [HC.stlc_ty_subst0]
          exact Hs'
        },
        sorry
      ⟩
    | _ => exact True.intro
  }