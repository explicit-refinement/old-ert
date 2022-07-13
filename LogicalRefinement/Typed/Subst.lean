import LogicalRefinement.Untyped
import LogicalRefinement.Untyped.Subst
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Wk
open Term
open Annot
open AnnotSort

inductive SubstVar': Subst -> Context -> Nat -> Term -> HypKind -> Prop
  | expr {σ Γ n A k}: (Γ ⊢ σ n: expr k.annot (A.subst σ)) -> SubstVar' σ Γ n A k
  | var {σ Γ n A k m}: σ n = var m 
    -> HasVar' Γ m k (A.subst σ) -> SubstVar' σ Γ n A k

inductive SubstVar: Subst -> Context -> Nat -> Term -> HypKind -> Prop
  | expr {σ Γ n A s}: (Γ ⊢ σ n: expr s (A.subst σ)) -> SubstVar σ Γ n A (HypKind.val s)
  | var {σ Γ n A k m}: σ n = var m 
    -> (Γ ⊢ A.subst σ: sort k.annot)
    -> HasVar Γ m k (A.subst σ) -> SubstVar σ Γ n A k

theorem SubstVar'.wk_sort {σ Γ n A k k'} (H: SubstVar' σ Γ n A k) (Hk: k'.is_sub k):
  SubstVar' σ Γ n A k'
  := by {
    cases H with
    | expr => 
      cases k <;> cases k' <;> cases Hk <;>
      apply SubstVar'.expr <;> assumption
    | var Ha Hv => exact SubstVar'.var Ha (Hv.wk_sort Hk)
  }

theorem SubstVar.v {σ Γ n A k} (H: SubstVar σ Γ n A k): SubstVar' σ Γ n A k
  := by {
    cases H with
    | expr => apply SubstVar'.expr <;> assumption
    | var Hn _HA HΓ => exact SubstVar'.var Hn HΓ.v
  }

def SubstCtx' (σ: Subst) (Γ Δ: Context): Prop :=  
  ∀n A k, HasVar Δ n k A -> SubstVar' σ Γ n A k

def SubstCtx (σ: Subst) (Γ Δ: Context): Prop :=  
  ∀n A k, HasVar Δ n k A -> SubstVar σ Γ n A k

theorem SubstCtx.v {σ: Subst} {Γ Δ: Context} (S: SubstCtx σ Γ Δ)
  : SubstCtx' σ Γ Δ := 
  λn A k Hv => (S n A k Hv).v

theorem SubstCtx'.id {Γ}: SubstCtx' Subst.id Γ Γ := 
  λ_ _ _ Hv => SubstVar'.var rfl (Term.subst_id _ ▸ Hv.v)

theorem SubstCtx'.lift_primitive 
  {σ: Subst} {Γ Δ: Context} {A: Term} {k k': HypKind}:
  SubstCtx' σ Γ Δ ->
  k.is_sub k' ->
  IsHyp Γ (Hyp.mk (A.subst σ) k') ->
  SubstCtx' σ.lift ((Hyp.mk (A.subst σ) k')::Γ) ((Hyp.mk A k)::Δ) := by {
    intro S Hk _ n A k HΔ;
    cases n with
    | zero =>
      simp only [Annot.subst]
      cases HΔ with
      | zero =>
        apply SubstVar'.var
        rfl
        simp only [Subst.lift_wk]
        simp only [Subst.lift]
        apply HasVar'.zero
        assumption
    | succ n =>
      simp only [Annot.subst, Hyp.annot]
      cases HΔ;
      rename_i A n H
      cases S _ _ _ H with
      | expr S =>
        apply SubstVar'.expr
        simp only [Subst.lift_wk, Nat.add]
        simp only [Subst.lift, Subst.wk1]
        rw [<-Annot.wk1_expr_def]
        exact HasType.wk1 S
      | var Hv HΓ =>
        apply SubstVar'.var
        simp [Subst.wk1, Hv]
        rfl
        simp only [Subst.lift_wk]
        exact HasVar'.succ HΓ
  }

theorem SubstCtx.lift_primitive 
  {σ: Subst} {Γ Δ: Context} {A: Term} {k: HypKind}:
  SubstCtx σ Γ Δ ->
  IsHyp Γ (Hyp.mk (A.subst σ) k) ->
  SubstCtx σ.lift ((Hyp.mk (A.subst σ) k)::Γ) ((Hyp.mk A k)::Δ) := by {
    intro S IH n A k HΔ;
    cases n with
    | zero =>
      simp only [Annot.subst]
      cases HΔ with
      | zero =>
        apply SubstVar.var
        rfl
        simp only [Subst.lift_wk]
        simp only [Subst.lift]
        apply HasType.wk1_sort
        exact IH
        rw [Subst.lift_wk]
        constructor
    | succ n =>
      simp only [Annot.subst, Hyp.annot]
      cases HΔ;
      rename_i A n H
      cases S _ _ _ H with
      | expr S =>
        apply SubstVar.expr
        simp only [Subst.lift_wk, Nat.add]
        simp only [Subst.lift, Subst.wk1]
        rw [<-Annot.wk1_expr_def]
        exact HasType.wk1 S
      | var Hv _ HΓ =>
        apply SubstVar.var
        simp [Subst.wk1, Hv]
        rfl
        simp only [Subst.lift_wk]
        apply HasType.wk1_sort
        assumption
        simp only [Subst.lift_wk]
        exact HasVar.succ HΓ
  }

theorem SubstCtx'.lift_loose
  {σ σ': Subst} {Γ Δ: Context} {A A': Term} {k: HypKind} {s: AnnotSort}:
  σ' = σ.lift ->
  A' = A.subst σ ->
  SubstCtx' σ Γ Δ ->
  k.is_sub (HypKind.val s) ->
  IsHyp Γ (Hyp.mk A' (HypKind.val s)) ->
  SubstCtx' σ' ((Hyp.mk A' (HypKind.val s))::Γ) ((Hyp.mk A k)::Δ) := by {
    intro Hσ HA;
    rw [Hσ, HA];
    apply lift_primitive
  }

theorem SubstCtx.lift_loose
  {σ σ': Subst} {Γ Δ: Context} {A A': Term} {s: AnnotSort}:
  σ' = σ.lift ->
  A' = A.subst σ ->
  SubstCtx σ Γ Δ ->
  IsHyp Γ (Hyp.mk A' (HypKind.val s)) ->
  SubstCtx σ' ((Hyp.mk A' (HypKind.val s))::Γ) ((Hyp.mk A (HypKind.val s))::Δ) := by {
    intro Hσ HA;
    rw [Hσ, HA];
    apply lift_primitive
  }

theorem SubstCtx'.upgrade (S: SubstCtx' σ Γ Δ): SubstCtx' σ Γ.upgrade Δ.upgrade 
:= by {
  intro n A k H;
  have ⟨k', Hk', H'⟩ := HasVar.downgrade H;  
  cases S _ _ _ H' with
  | expr S =>
    apply SubstVar'.expr;
    cases k with
    | val s => cases s <;> cases Hk' <;> exact S.upgrade
    | gst => cases Hk' <;> exact S.upgrade
  | var Hv HΓ =>
    cases k' with
    | val s => 
      cases k with
      | val s => 
        cases s <;> cases Hk' <;> exact SubstVar'.var Hv HΓ.upgrade_val
      | gst => cases H.no_ghosts
    | gst =>
      cases k with
      | val s => cases s <;> cases Hk' <;> 
        exact SubstVar'.var Hv HΓ.upgrade
      | gst => cases H.no_ghosts;
}

theorem SubstCtx.upgrade (S: SubstCtx σ Γ Δ): 
SubstCtx σ Γ.upgrade Δ.upgrade 
:= by {
  intro n A k H;
  have ⟨k', Hk', H'⟩ := HasVar.downgrade H;
  cases S _ _ _ H' with
  | expr S =>
    cases k with
    | val s => 
      apply SubstVar.expr;cases s <;> cases Hk' <;> exact S.upgrade
    | gst => cases H.no_ghosts
  | var Hv HA HΓ =>
    cases k' with
    | val s => 
      cases k with
      | val s => 
        cases s <;> cases Hk' <;> exact SubstVar.var Hv HA.upgrade HΓ.upgrade_val
      | gst => cases H.no_ghosts
    | gst =>
      cases k with
      | val s => cases s <;> cases Hk' <;> 
        exact SubstVar.var Hv HA.upgrade HΓ.ghost_up
      | gst => cases H.no_ghosts;
}

theorem SubstCtx'.upgrade_left (S: SubstCtx' ρ Γ Δ): SubstCtx' ρ Γ.upgrade Δ
:= by {
  intro n A k H;
  cases S _ _ _ H with
  | expr S =>
    exact SubstVar'.expr (HasType.upgrade S)
  | var Hv HΓ =>
    exact SubstVar'.var Hv HΓ.upgrade_weak
}

theorem Term.alpha0_natrec_subst_helper {C: Term} {σ: Subst}:
  ((C.subst σ.lift).wknth 1).alpha0 (Term.app (Term.arrow Term.nats Term.nats) Term.succ (Term.var 1))
    = ((C.wknth 1).alpha0 (Term.app (Term.arrow Term.nats Term.nats) Term.succ (Term.var 1))).subst (σ.liftn 2)
  := by {
    simp only [
      subst01, wknth, alpha0, subst0,
      <-Subst.subst_wk_compat,
      subst_composes
    ]
    apply congr rfl;
    funext n;
    cases n with
    | zero => rfl
    | succ n => 
      simp only [
        Subst.comp, Subst.subst_wk_compat, Subst.lift, Subst.wk1, subst, 
        Wk.var, Nat.succ, Nat.add, Subst.liftn, wk1
        ]
      simp only [<-Subst.subst_wk_compat, subst_composes]
      apply congr rfl;
      funext n;
      cases n <;> rfl
  }

theorem Term.pi_funext_subst_helper {A B f: Term} {σ: Subst}:
  Term.app 
    (Term.wk1 (Term.pi (Term.subst A σ) (Term.subst B (Subst.lift σ)))) 
    (Term.wk1 (Term.subst f σ))
    (Term.var 0)
  = tri TermKind.app
    (abs TermKind.pi (Term.subst (Term.wk A Wk.wk1) (Subst.lift σ))
    (Term.subst (Term.wk B (Wk.lift Wk.wk1)) (Subst.lift (Subst.lift σ))))
    (Term.subst (Term.wk1 f) (Subst.lift σ)) (Subst.lift σ 0)
  := by {
    apply congr _ rfl;
    apply congr;
    apply congr rfl _;
    simp only [wk1, wk]
    apply congr;
    apply congr rfl;
    rw [<-Term.wk1]
    rw [<-Subst.lift_wk]
    rfl
    {
      simp only [<-Subst.subst_wk_compat, Term.subst_composes]
      apply congr rfl;
      funext v;
      cases v with
      | zero => rfl
      | succ n => 
        simp only [Subst.comp, subst, Subst.lift, Wk.var, Subst.wk1, wk1]
        simp only [<-Subst.subst_wk_compat, Term.subst_composes]
        apply congr rfl;
        funext v;
        cases v <;> rfl
    }
    rw [<-Subst.lift_wk]
  }

theorem HasType.subst' {σ Γ Δ a A} (HΔ: Δ ⊢ a: A) (S: SubstCtx' σ Γ Δ):
  (Γ ⊢ (a.subst σ): (A.subst σ)) := by {
    induction HΔ generalizing σ Γ;

    case var H I =>
      cases S _ _ _ H with
      | expr E => exact E
      | var Hv HΓ =>
        dsimp only [Term.subst]
        rw [Hv]
        exact HasType.var (I S) HΓ.v

    all_goals (
      rename_i' I5 I4 I3 I2 I1 I0;
      simp only [
        Annot.sym_ty_subst,
        Annot.trans_ty_subst
      ]
      simp only [Annot.subst, term, proof, implies_subst, const_arrow_subst, assume_wf_subst] at *
      try rw [eta_ex_eq_subst]
      try rw [irir_ex_eq_subst]
      try rw [prir_ex_eq_subst]
      simp only [Term.subst, Term.subst0_subst, Subst.subst01_subst] at *
      constructor <;>
      repeat (
        try rw [Term.alpha00_comm (by simp)]
        try rw [Term.let_bin_ty_alpha_pair]
        try rw [Term.let_bin_ty_alpha_elem]
        try rw [Term.let_bin_ty_alpha_repr]
        try rw [Term.let_bin_ty_alpha_wit]
        try rw [Term.let_bin_ty_alpha_conj]
        try rw [Term.alpha0_natrec_subst_helper]
        try rw [Term.var2_var1_alpha]
        repeat rw [Term.pi_funext_subst_helper]
        first | apply I0 | apply I1 | apply I2 | apply I3 | apply I4 | apply I5 | constructor
        first
        | exact S
        | exact SubstCtx'.upgrade S
        | exact SubstCtx'.upgrade_left S
        | repeat any_goals (
          apply SubstCtx'.lift_primitive _ (by constructor <;> simp only [HypKind, Hyp.subst]) <;>
          first 
          | exact S 
          | exact SubstCtx'.upgrade S 
          | exact SubstCtx'.upgrade_left S
          | skip
        )
      )
    )
  }


theorem HasType.subst {σ Γ Δ a A} (HΔ: Δ ⊢ a: A) (S: SubstCtx σ Γ Δ):
  (Γ ⊢ (a.subst σ): (A.subst σ))
  := HΔ.subst' S.v

theorem HasType.subst_sort' {Γ Δ σ a k} 
  (HΔ: Δ ⊢ a: sort k) (S: SubstCtx' σ Γ Δ):
  (Γ ⊢ (a.subst σ): sort k) := HΔ.subst' S

theorem HasType.subst_sort {Γ Δ σ a k} 
  (HΔ: Δ ⊢ a: sort k) (S: SubstCtx σ Γ Δ):
  (Γ ⊢ (a.subst σ): sort k) := HΔ.subst S

theorem HasType.to_subst' {Γ a s A} (H: HasType Γ a (expr s A)):
  SubstCtx' a.to_subst Γ ((Hyp.mk A (HypKind.val s))::Γ) := by {
    intro n A k Hv;
    cases Hv with
    | zero => 
      apply SubstVar'.expr
      rw [<-Term.subst0_def]
      rw [Term.subst0_wk1]
      exact H
    | succ Hv => 
      apply SubstVar'.var
      rfl
      rw [<-Term.subst0_def]
      rw [Term.subst0_wk1]
      exact Hv.v
  }

theorem HasType.to_subst {Γ a s A} (H: HasType Γ a (expr s A)) (HΓ: IsCtx Γ):
  SubstCtx a.to_subst Γ ((Hyp.mk A (HypKind.val s))::Γ) := by {
    intro n A k Hv;
    cases Hv with
    | zero => 
      apply SubstVar.expr
      rw [<-Term.subst0_def]
      rw [Term.subst0_wk1]
      exact H
    | succ Hv => 
      apply SubstVar.var
      rfl
      rw [<-Term.subst0_def]
      rw [Term.subst0_wk1]
      exact HΓ.var_valid Hv
      rw [<-Term.subst0_def]
      rw [Term.subst0_wk1]
      exact Hv
  }

theorem HasType.subst0 {Γ e B t s A} 
  (He: HasType ((Hyp.mk A (HypKind.val s))::Γ) e B)
  (Ht: HasType Γ t (expr s A))
  : Γ ⊢ (e.subst0 t): (B.subst0 t) 
  := He.subst' Ht.to_subst'

theorem HasType.subst0_expr {Γ e s' t s A B} 
  (He: HasType ((Hyp.mk A (HypKind.val s))::Γ) e (expr s' B))
  (Ht: HasType Γ t (expr s A))
  : Γ ⊢ (e.subst0 t): expr s' (B.subst0 t)
  := He.subst' Ht.to_subst'

theorem HasType.subst0_sort {Γ e s' t s A} 
  (He: HasType ((Hyp.mk A (HypKind.val s))::Γ) e (sort s'))
  (Ht: HasType Γ t (expr s A))
  : Γ ⊢ (e.subst0 t): sort s'
  := He.subst' Ht.to_subst'

theorem HasType.subst0_gen {Γ e B t s A B'} 
  (He: HasType ((Hyp.mk A (HypKind.val s))::Γ) e B)
  (Ht: HasType Γ t (expr s A))
  (HBB': B' = B.subst0 t)
  : Γ ⊢ (e.subst0 t): (B') 
  := HBB' ▸ He.subst' Ht.to_subst'

theorem HasType.to_alpha {Γ a sa sb A B} 
  (H: ((Hyp.mk B (HypKind.val sb))::Γ) ⊢ a: expr sa A.wk1) 
  (HΓ: IsCtx Γ):
  SubstCtx a.to_alpha 
    ((Hyp.mk B (HypKind.val sb))::Γ) 
    ((Hyp.mk A (HypKind.val sa))::Γ) := by {
    intro n A k Hv;
    cases Hv with
    | zero => 
      apply SubstVar.expr
      rw [<-Term.alpha0_def]
      rw [Term.alpha0_wk1]
      exact H
    | succ Hv => 
      apply SubstVar.var
      rfl
      rw [<-Term.alpha0_def]
      rw [Term.alpha0_wk1]
      exact (HΓ.var_valid Hv).wk1_sort
      rw [<-Term.alpha0_def]
      rw [Term.alpha0_wk1]
      constructor
      exact Hv
  }

theorem HasType.to_alpha' {Γ a sa sb A B} 
  (H: ((Hyp.mk B (HypKind.val sb))::Γ) ⊢ a: expr sa A.wk1):
  SubstCtx' a.to_alpha 
    ((Hyp.mk B (HypKind.val sb))::Γ) 
    ((Hyp.mk A (HypKind.val sa))::Γ) := by {
    intro n A k Hv;
    cases Hv with
    | zero => 
      apply SubstVar'.expr
      rw [<-Term.alpha0_def]
      rw [Term.alpha0_wk1]
      exact H
    | succ Hv => 
      apply SubstVar'.var
      rfl
      rw [<-Term.alpha0_def]
      rw [Term.alpha0_wk1]
      constructor
      exact Hv.v
  }

theorem HasType.subst01 {Γ e C l r sl sr A B} 
  (He: HasType 
    ((Hyp.mk B (HypKind.val sl))
    ::(Hyp.mk A (HypKind.val sr))::Γ) e C)
  (Hl: HasType Γ l (expr sl (B.subst0 r)))
  (Hr: HasType Γ r (expr sr A))
  : Γ ⊢ (e.subst01 l r): (C.subst01 l r) 
  := by {
    unfold Term.subst01;
    unfold Annot.subst01;
    apply subst';
    exact He;
    intro n;
    cases n with
    | zero =>
      intro n A Hv;
      cases Hv with
      | zero =>
        apply SubstVar'.expr <;>
        rw [<-Term.subst01_wk1] at Hl <;>
        exact Hl
    | succ n => 
      cases n with
      | zero => 
        intro n A Hv;
        cases Hv with
        | succ Hv =>
          cases Hv with
          | zero =>
            apply SubstVar'.expr <;>
            rw [Term.subst01_def, Term.subst01_wk1_wk1] <;>
            exact Hr
      | succ n => 
        intro n A Hv;
        apply SubstVar'.var;
        rfl
        cases Hv with
        | succ Hv =>
          cases Hv with
          | succ Hv => 
            rw [Term.subst01_def, Term.subst01_wk1_wk1]
            exact Hv.v
  }

theorem HasType.subst01_gen {Γ e C l r sl sr A B} 
  (He: HasType 
    ((Hyp.mk B (HypKind.val sl))
    ::(Hyp.mk A (HypKind.val sr))::Γ) e C)
  (Hl: HasType Γ l (expr sl (B.subst0 r)))
  (Hr: HasType Γ r (expr sr A))
  (HCC': C' = C.subst01 l r)
  : Γ ⊢ (e.subst01 l r): C' 
  := HCC' ▸ (He.subst01 Hl Hr)

theorem HasType.subst01_gen_gst {Γ e C l r sl A B} 
  (He: HasType 
    ((Hyp.mk B (HypKind.val sl))
    ::(Hyp.mk A HypKind.gst)::Γ) e C)
  (Hl: HasType Γ l (expr sl (B.subst0 r)))
  (Hr: HasType Γ r (expr type A))
  (HCC': C' = C.subst01 l r)
  : Γ ⊢ (e.subst01 l r): C' 
  := by {
    apply subst01_gen _ Hl Hr HCC';
    upgrade_ctx assumption
  }

theorem HasType.subst01_sort {Γ e s' l r sl sr A B} 
  (He: HasType 
    ((Hyp.mk B (HypKind.val sl))
    ::(Hyp.mk A (HypKind.val sr))::Γ) e (sort s'))
  (Hl: HasType Γ l (expr sl (B.subst0 r)))
  (Hr: HasType Γ r (expr sr A))
  : Γ ⊢ (e.subst01 l r): sort s' 
  := He.subst01 Hl Hr

theorem HasType.sym_ty (H: Γ ⊢ A: type): Γ ⊢ A.sym_ty: prop
  := by {
    constructor
    exact H;
    constructor
    exact H.wk1_sort;
    constructor
    constructor
    apply H.wk1_sort.wk_sort;
    repeat constructor
    exact H.upgrade.wk1_sort.wk1_sort;
    repeat constructor
    exact H.upgrade.wk1_sort.wk1_sort;
    constructor
    constructor
    simp only [Term.subst, Wk.var, Subst.lift, Subst.wk1, Context.upgrade]
    exact H.wk1_sort.wk1_sort.wk1_sort;
    constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
  }
  
theorem HasType.trans_ty (H: Γ ⊢ A: type): Γ ⊢ A.trans_ty: prop
  := by {
    constructor
    exact H;
    constructor
    exact H.wk1_sort;
    constructor
    exact H.wk1_sort.wk1_sort;
    constructor
    constructor
    exact H.wk1_sort.wk1_sort.wk1_sort;
    constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
    exact H.wk1_sort.wk1_sort.wk1_sort.wk1_sort;
    constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
    exact H.wk1_sort.wk1_sort.wk1_sort.wk1_sort.wk1_sort;
    constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
    exact H.upgrade.wk1_sort.wk1_sort.wk1_sort.wk1_sort.wk1_sort;
    repeat constructor
  }

theorem SubstCtx.subst_var 
  (S: SubstCtx σ Γ Δ) 
  (HA: Δ ⊢ A: sort s) 
  (HΔ: HasVar Δ n (HypKind.val s) A)
  : Γ ⊢ σ n: expr s (A.subst σ)
  := (HasType.var HA HΔ).subst S

theorem SubstCtx.lift_delta {σ Γ Δ A k}
  (S: SubstCtx σ Γ Δ)
  (HA: Δ ⊢ A: sort k.annot):
  SubstCtx σ.lift ((Hyp.mk (A.subst σ) k)::Γ) ((Hyp.mk A k)::Δ)
  := by {
    -- Again, the strange "exact" bug...
    -- 
    -- Note: I think this is not actually a bug, but rather the `constructor` tactic
    -- failing to infer an appropriate constructor due to being confused by the
    -- additional constraints induced by the `HA.subst S` argument
    apply S.lift_primitive;
    exact HA.subst S
  }

theorem SubstCtx.lift_type {σ Γ Δ A}
  (S: SubstCtx σ Γ Δ)
  (HA: Δ ⊢ A: sort type):
  SubstCtx σ.lift 
  ((Hyp.mk (A.subst σ) (HypKind.val type))::Γ) 
  ((Hyp.mk A (HypKind.val type))::Δ)
  := @SubstCtx.lift_delta σ Γ Δ A (HypKind.val type) S HA

theorem SubstCtx.lift_gst {σ Γ Δ A}
  (S: SubstCtx σ Γ Δ)
  (HA: Δ ⊢ A: sort type):
  SubstCtx σ.lift 
  ((Hyp.mk (A.subst σ) HypKind.gst)::Γ) 
  ((Hyp.mk A HypKind.gst)::Δ)
  := @SubstCtx.lift_delta σ Γ Δ A HypKind.gst S HA

theorem SubstCtx.lift_prop {σ Γ Δ A}
  (S: SubstCtx σ Γ Δ)
  (HA: Δ ⊢ A: sort prop):
  SubstCtx σ.lift 
  ((Hyp.mk (A.subst σ) (HypKind.val prop))::Γ) 
  ((Hyp.mk A (HypKind.val prop))::Δ)
  := @SubstCtx.lift_delta σ Γ Δ A (HypKind.val prop) S HA

theorem SubstCtx.lift_delta' {σ Γ Δ A}
  (S: SubstCtx σ Γ Δ)
  (k: HypKind)
  (HA: Δ ⊢ A: sort k.annot):
  SubstCtx σ.lift ((Hyp.mk (A.subst σ) k)::Γ) ((Hyp.mk A k)::Δ)
  := S.lift_delta HA

theorem WkCtx.to_subst {ρ Γ Δ} (R: WkCtx ρ Γ Δ): SubstCtx' ρ Γ Δ
  := λ_ _ _ Hv => SubstVar'.var rfl (Subst.subst_wk_compat.symm ▸ Hv.wk R).v