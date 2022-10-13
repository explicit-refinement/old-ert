import LogicalRefinement.Untyped
import LogicalRefinement.Utils
import LogicalRefinement.Tactics
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Wk
import LogicalRefinement.Typed.Subst
import LogicalRefinement.Typed.Downgrade
open Term
open Annot
open AnnotSort

--TODO: report invalid environment extension

theorem HasType.no_poly {Γ v s}: ¬(HasType Γ (Term.var v) (sort s)) := by {
  intro H; cases H
}

theorem HasType.no_poly_ty {Γ v}: ¬(Γ ⊢ (Term.var v): type) := no_poly

inductive Annot.regular: Annot -> Context -> Prop
  | sort {Γ s}: regular (sort s) Γ
  | expr {Γ s A}: (Γ ⊢ A: sort s) -> regular (expr s A) Γ

def Annot.regular_expr: regular (expr s A) Γ -> (Γ ⊢ A: sort s)
  | Annot.regular.expr Hr => Hr

theorem HasType.regular (p: Γ ⊢ a: A): A.regular Γ := by {
  induction p;

  -- Types and propositions are trivially regular
  all_goals try exact Annot.regular.sort

  case app A B _ r HP _ Hr _ _ _ =>
    constructor
    apply subst_sort'
    cases HP <;> assumption
    intro n A k;
    apply Hr.to_subst'

  case app_pr A B _ r HP _ Hr _ _ _ =>
    constructor
    apply subst_sort'
    cases HP <;> assumption
    intro n A k;
    apply Hr.to_subst'

  case lam_irrel _ _ _ IB => 
    constructor
    constructor
    assumption
    cases IB
    apply HasType.sub
    assumption
    constructor
    exact Context.is_sub.refl
    repeat constructor
    
  case app_irrel A B _ r HP _ Hr _ _ _ =>
    constructor
    apply HasType.downgrade
    apply subst_sort'
    cases HP <;> assumption
    intro n A k Hv;
    cases k with
    | val s => 
      apply Hr.to_subst'
      rw [HasVar.v_eq]
      exact Hv.v.upgrade
    | gst => 
      apply SubstVar'.wk_sort
      apply Hr.to_subst'
      apply Hv.ghost_up
      constructor

  case dconj HD _ _ _ IA _ => 
    constructor
    constructor
    cases IA
    assumption
    cases HD
    assumption

  case mp HM _ Hr _ _ _ =>
    cases HM with
    | dimplies Hφ Hψ =>
      constructor
      apply HasType.downgrade
      apply HasType.subst0_sort
      exact Hψ.upgrade
      upgrade_ctx assumption

  case inst Hf _ Hr _ _ _ => 
    constructor
    apply HasType.downgrade
    apply HasType.subst0_sort
    cases Hf with
    | forall_ HA Hφ => exact Hφ.upgrade
    assumption

  case refl Ha IA =>  
    cases IA;
    constructor
    apply HasType.downgrade
    constructor
    assumption
    apply HasType.upgrade
    assumption
    apply HasType.upgrade
    assumption

  case cong _ _ _ _ _ Ip _ => 
    constructor
    apply HasType.downgrade
    apply HasType.subst0_sort
    upgrade_ctx assumption
    cases Ip with
    | expr Ip => cases Ip; assumption

  -- case trans _ _ _ _ _ Ip _ => 
  --   constructor
  --   apply HasType.downgrade
  --   apply HasType.subst0_sort
  --   upgrade_ctx assumption
  --   cases Ip with
  --   | expr Ip => cases Ip; assumption

  case beta Hs HA Ht Is _ _ => 
    cases Is with
    | expr HB =>
      constructor
      apply HasType.downgrade
      constructor
      exact Context.upgrade_idem ▸ HB.upgrade.subst0_sort Ht.upgrade
      constructor
      constructor
      exact HA.upgrade.upgrade
      exact HB.upgrade
      constructor
      exact Hs.upgrade
      exact HA.upgrade.upgrade
      exact Ht.upgrade
      exact Context.upgrade_idem ▸ Hs.upgrade.upgrade.subst0 Ht.upgrade.upgrade

  case beta_ir Hs HA Ht Is _ _ => 
    cases Is with
    | expr HB =>
      constructor
      apply HasType.downgrade
      constructor
      exact Context.upgrade_idem ▸ HB.upgrade.subst0_sort Ht.upgrade
      constructor
      constructor
      exact HA.upgrade.upgrade
      exact HB.upgrade
      constructor
      exact HA.upgrade.upgrade
      upgrade_ctx assumption
      exact Ht.upgrade.upgrade
      exact Context.upgrade_idem ▸ Hs.upgrade.upgrade.subst0 Ht.upgrade.upgrade

  case beta_pr Hs Hφ Hp Is _ _  => 
    cases Is with
    | expr HA =>
      constructor
      apply HasType.downgrade
      constructor
      exact Context.upgrade_idem ▸ HA.upgrade.subst0_sort Hp.upgrade
      constructor
      constructor
      exact Hφ.upgrade.upgrade
      exact HA.upgrade
      constructor
      exact Hφ.upgrade.upgrade
      exact Hs.upgrade
      exact Hp.upgrade
      exact Context.upgrade_idem ▸ Hs.upgrade.upgrade.subst0 Hp.upgrade.upgrade

  case eta Hf _ If _ =>
    constructor
    constructor
    apply HasType.downgrade
    cases If <;> assumption
    apply HasType.eta_ex_ty;
    cases If <;> assumption
    exact Hf
    exact Hf

  case irir Γ A B f x y Hf Hx Hy If Ix _ => 
    cases Ix with
    | expr HA =>
      cases If with
      | expr HF =>
        cases HF with
        | intersect HA HB =>
          constructor
          apply HasType.downgrade
          constructor
          rw [<-B.subst0_wk1]
          exact HB.subst0_sort Hx
          conv =>
            arg 3
            rw [<-@Term.subst0_wk1 B x]
          constructor
          exact HA.upgrade.intersect HB.upgrade
          exact Hf.upgrade
          exact Hx.upgrade.upgrade
          conv =>
            arg 3
            rw [<-@Term.subst0_wk1 B y]
          constructor
          exact HA.upgrade.intersect HB.upgrade
          exact Hf.upgrade
          exact Hy.upgrade.upgrade

  case prir => 
    constructor
    constructor
    apply subst0_sort
    assumption
    assumption
    apply wk1_sort
    apply subst0_sort
    assumption
    assumption

  case beta_left => 
    constructor
    constructor
    apply downgrade
    apply subst0_sort
    upgrade_ctx assumption
    constructor
    assumption
    upgrade_ctx assumption
    constructor
    constructor
    assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    apply subst0_gen
    assumption
    assumption
    rw [Term.alpha0_inj_subst]
    rfl

  case beta_right => 
    constructor
    constructor
    apply downgrade
    apply subst0_sort
    upgrade_ctx assumption
    constructor
    assumption
    upgrade_ctx assumption
    constructor
    constructor
    assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    apply subst0_gen
    assumption
    assumption
    rw [Term.alpha0_inj_subst]
    rfl

  case beta_pair => 
    constructor
    constructor
    apply HasType.downgrade
    apply subst0_sort
    upgrade_ctx assumption
    constructor
    constructor
    upgrade_ctx assumption
    upgrade_ctx assumption
    assumption
    assumption
    constructor
    constructor
    constructor
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    apply subst01_gen;
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    simp only [Annot.subst01, Annot.subst, term]
    apply congr rfl
    exact Term.alpha0_subst01_bin.symm

  case beta_set => 
    constructor
    constructor
    apply HasType.downgrade
    apply subst0_sort
    upgrade_ctx assumption
    constructor
    constructor
    upgrade_ctx assumption
    upgrade_ctx assumption
    assumption
    upgrade_ctx assumption
    constructor
    constructor
    constructor
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    apply subst01_gen;
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    simp only [Annot.subst01, Annot.subst, term]
    apply congr rfl
    exact Term.alpha0_subst01_bin.symm

  case beta_repr => 
    constructor
    constructor
    apply HasType.downgrade
    apply subst0_sort
    upgrade_ctx assumption
    constructor
    constructor
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    constructor
    constructor
    constructor
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    upgrade_ctx assumption
    apply subst01_gen;
    upgrade_ctx assumption
    upgrade_ctx assumption
    assumption
    simp only [Annot.subst01, Annot.subst, term]
    apply congr rfl
    exact Term.alpha0_subst01_bin.symm

  case natrec HC Hn _ _ _ _ _ _ => 
    constructor
    apply HasType.subst0_sort
    apply HC.sub
    constructor
    apply Context.is_sub.refl
    constructor
    constructor
    assumption

  case natrec_prop => 
    constructor
    apply HasType.downgrade
    apply HasType.subst0_sort
    upgrade_ctx assumption
    upgrade_ctx assumption

  case case_prop =>
    constructor 
    apply HasType.downgrade
    apply HasType.subst0_sort;
    upgrade_ctx assumption
    assumption

  case let_pair_prop => 
    constructor 
    apply HasType.downgrade
    apply HasType.subst0_sort;
    upgrade_ctx assumption
    assumption

  case let_set_prop => 
    constructor 
    apply HasType.downgrade
    apply HasType.subst0_sort;
    upgrade_ctx assumption
    assumption

  case let_repr_prop => 
    constructor 
    apply HasType.downgrade
    apply HasType.subst0_sort;
    upgrade_ctx assumption
    assumption

  case beta_zero => 
    constructor
    constructor
    apply downgrade
    apply subst0_sort
    upgrade_ctx assumption
    constructor
    constructor
    upgrade_ctx assumption
    constructor
    assumption
    upgrade_ctx assumption
    assumption

  case beta_succ => 
    constructor
    constructor
    apply downgrade
    apply subst0_sort
    upgrade_ctx assumption
    focus repeat constructor
    assumption
    constructor
    upgrade_ctx assumption
    focus repeat constructor
    assumption
    assumption
    assumption
    apply subst01_gen_gst;
    assumption
    constructor
    upgrade_ctx assumption
    assumption
    assumption
    assumption
    assumption
    apply congr rfl
    simp only [
      Term.subst01, Term.wknth, Term.alpha0, Term.subst0,
      <-Subst.subst_wk_compat,
      Term.subst_composes
    ]
    apply congr rfl;
    funext n;
    cases n <;> rfl

  case succ => repeat constructor

  case unit_unique =>
    constructor
    constructor
    constructor
    assumption
    constructor

  all_goals (
    constructor; 
    first 
    | assumption 
    | (
      apply subst0_sort
      assumption
      assumption
    )
    | (constructor <;> (
        first 
        | assumption 
        | ( apply Annot.regular_expr; assumption )
      ))
  )
}

theorem HasType.expr_regular (p: HasType Γ a (expr s A)): HasType Γ A (sort s) 
  := by {
    let H := regular p;
    cases H with
    | expr H => exact H
  }

theorem HasType.term_regular (p: HasType Γ a (term A)): HasType Γ A type 
  := by {
    let H := regular p;
    cases H with
    | expr H => exact H
  }

theorem HasType.proof_regular (p: HasType Γ a (proof A)): HasType Γ A prop 
  := by {
    let H := regular p;
    cases H with
    | expr H => exact H
  }

theorem HasType.downgrade_prop {Γ: Context} {p ϕ} 
  (H: Γ.upgrade ⊢ p: proof ϕ): Γ ⊢ p: proof ϕ
  := by {
    generalize HΓ': Γ.upgrade = Γ';
    generalize HP: proof ϕ = P;
    rw [HΓ', HP] at H; 
    induction H generalizing Γ ϕ with
    | var HA Hv IA => 
      cases HP;
      generalize HP: (HypKind.val prop) = P;
      rw [HP] at Hv;
      constructor;
      {
        cases HΓ';
        exact HA.downgrade
      }
      clear HA;
      clear IA;
      induction Hv generalizing Γ with
      | zero => 
        cases Γ with
        | nil => cases HΓ'
        | cons H Γ =>
          cases H with
          | mk A k =>
            cases k with
            | val s => 
              cases s with
              | prop => cases HΓ'; constructor
              | type => cases HΓ'; cases HP
            | gst => cases HΓ'; cases HP
      | succ Hv I => 
        cases Γ with
        | nil => cases HΓ'
        | cons H Γ =>
          cases HΓ'
          constructor;
          apply I rfl HP;
    | _ =>
      cases HP <;>
      cases HΓ' <;>  
      rename_i' I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 IA IB IC ID <;>
      constructor <;>
      (first 
        | assumption
        | exact I0 rfl rfl
        | exact I1 rfl rfl
        | exact I2 rfl rfl
        | exact I3 rfl rfl
        | exact I4 rfl rfl
        | exact I5 rfl rfl
        | exact I6 rfl rfl
        | exact I7 rfl rfl
        | exact I8 rfl rfl
        | exact I9 rfl rfl
        | exact IA rfl rfl
        | exact IB rfl rfl
        | exact IC rfl rfl
        | exact ID rfl rfl
        | apply HasType.downgrade <;> (
          first
          | assumption
          | exact Context.upgrade_idem ▸ I0.upgrade
          | exact Context.upgrade_idem ▸ I1.upgrade
          | exact Context.upgrade_idem ▸ I2.upgrade
          | exact Context.upgrade_idem ▸ I3.upgrade
          | exact Context.upgrade_idem ▸ I4.upgrade
          | exact Context.upgrade_idem ▸ I5.upgrade
          | exact Context.upgrade_idem ▸ I6.upgrade
          | exact Context.upgrade_idem ▸ I7.upgrade
          | exact Context.upgrade_idem ▸ I8.upgrade
          | exact Context.upgrade_idem ▸ I9.upgrade
          | exact Context.upgrade_idem ▸ IA.upgrade
          | exact Context.upgrade_idem ▸ IB.upgrade
          | exact Context.upgrade_idem ▸ IC.upgrade
          | exact Context.upgrade_idem ▸ ID.upgrade
          | upgrade_ctx assumption
        )
        | upgrade_ctx assumption)
  }
