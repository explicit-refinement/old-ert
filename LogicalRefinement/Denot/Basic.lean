import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc

open AnnotSort
open Annot

def Term.denote_ty (A: Term) (Γ: Context)
  (G: Γ.upgrade.stlc.interp)
  (a: A.stlc_ty.interp): Prop
  := match A with
  | const TermKind.unit => 
    match a with
    | some () => True
    | none => False
  | abs TermKind.pi A B => 
    ∀x: A.stlc_ty.interp,
      A.denote_ty Γ G x ->
      B.denote_ty ((Hyp.val A type)::Γ) (x, G) (a.app x)
  | abs TermKind.sigma A B => 
    match a with
    | some (a, b) => 
      let a := Ty.eager a;
      let b := Ty.eager b;
      A.denote_ty Γ G a ∧ B.denote_ty ((Hyp.val A type)::Γ) (a, G) b
    | none => False
  | bin TermKind.coprod A B =>
    match a with
    | some a => 
      match a with
      | Sum.inl a => A.denote_ty Γ G (Ty.eager a)
      | Sum.inr b => B.denote_ty Γ G (Ty.eager b)
    | none => False
  | abs TermKind.assume φ A => 
    (φ.denote_ty Γ G none) -> (A.denote_ty Γ G a)
  | abs TermKind.set A φ => 
    A.denote_ty Γ G a ∧ φ.denote_ty ((Hyp.val A type)::Γ) (a, G) none
  | abs TermKind.intersect A B => 
    ∀x: A.stlc_ty.interp,
      A.denote_ty Γ G x ->
      B.denote_ty ((Hyp.gst A)::Γ) (x, G) a
  | abs TermKind.union A B => 
    ∃x: A.stlc_ty.interp,
      A.denote_ty Γ G x ->
      B.denote_ty ((Hyp.gst A)::Γ) (x, G) a
  | const TermKind.top => True
  | const TermKind.bot => False
  | abs TermKind.dimplies A B => 
    --TODO: think about this...
    (A.denote_ty Γ G none) -> (B.denote_ty Γ G none)
  | abs TermKind.dand A B =>
    --TODO: think about this...
    A.denote_ty Γ G none ∧ B.denote_ty Γ G none
  | bin TermKind.or A B => 
    A.denote_ty Γ G none ∨ B.denote_ty Γ G none
  | abs TermKind.forall_ A φ => 
    ∀x: A.stlc_ty.interp,
      A.denote_ty Γ G x ->
      φ.denote_ty ((Hyp.val A type)::Γ) (x, G) none
  | abs TermKind.exists_ A φ => 
    ∃x: A.stlc_ty.interp,
      A.denote_ty Γ G x ->
      φ.denote_ty ((Hyp.gst A)::Γ) (x, G) none
  | tri TermKind.eq A x y => 
    (px: Γ.upgrade ⊢ x: term A) -> 
    (py: Γ.upgrade ⊢ y: term A) ->
    px.stlc.interp G = py.stlc.interp G
  | const TermKind.nats => 
    match a with
    | some _ => True
    | none => False
  | _ => False

theorem interp_eq_none
  : @Eq.rec Ty a (λx _ => Ty.interp x) none x p = none := by {
    cases p <;> rfl
  }

theorem interp_eq_some
  : @Eq.rec Ty a (λx _ => Ty.interp x) (some v) x p = (some (p ▸ v)) := by {
    cases p <;> rfl
  }

theorem monorecursor
  : 
  @Eq.rec A x F D y p =
  @Eq.rec (Type) (F x rfl) (λA p => A) D (F y p) p'  
  := by {
    cases p;
    cases p';
    simp
  }

theorem Term.denote_wk1_ty
  (A: Term) 
  (B: Term)
  (Γ: Context)
  (x: B.stlc_ty.interp) 
  (G: Γ.upgrade.stlc.interp) 
  (a: A.stlc_ty.interp)
  (a': A.wk1.stlc_ty.interp)
  (Haa': a' = A.stlc_ty_wk1 ▸ a)
  (H: A.denote_ty Γ G a) 
  : A.wk1.denote_ty ((Hyp.val B type)::Γ) (x, G) a'
  := sorry
  
theorem Term.denote_wk1_prop
  (A: Term) 
  (φ: Term)
  (Γ: Context)
  (G: Γ.upgrade.stlc.interp) 
  (a: A.stlc_ty.interp)
  (a': A.wk1.stlc_ty.interp)
  (Haa': a' = A.stlc_ty_wk1 ▸ a)
  (H: A.denote_ty Γ G a) 
  : A.wk1.denote_ty ((Hyp.val φ prop)::Γ) G a'
  := sorry
  
theorem Term.denote_wk1_gst
  (A: Term) 
  (B: Term)
  (Γ: Context) 
  (x: B.stlc_ty.interp)
  (G: Γ.upgrade.stlc.interp) 
  (a: A.stlc_ty.interp)
  (a': A.wk1.stlc_ty.interp)
  (Haa': a' = A.stlc_ty_wk1 ▸ a)
  (H: A.denote_ty Γ G a) 
  : A.wk1.denote_ty ((Hyp.gst B)::Γ) (x, G) a'
  := sorry

def Annot.denote (A: Annot) (Γ: Context)
  (G: Γ.upgrade.stlc.interp)
  (a: A.stlc_ty.interp): Prop
  := match A with
  | sort s => True
  | expr type A => A.denote_ty Γ G a
  | expr prop A => A.denote_ty Γ G none

def Annot.denote_regular (A: Annot) (Γ: Context) (H: A.regular Γ)
  (G: Γ.upgrade.stlc.interp)
  (a: A.stlc_ty.interp): Prop
  := match A with
     | sort s => True
     | expr s A => by {
       apply A.denote_ty Γ G;
       rw [<-Annot.sort_case (by cases H <;> assumption)]
       exact a
     }

theorem Annot.denote_regular_eq (A: Annot) (Γ: Context) (H: A.regular Γ)
  : A.denote_regular Γ H = A.denote Γ
  := by {
    funext G a;
    cases A with
    | sort => rfl
    | expr s A =>
      cases s with
      | type => rfl
      | prop => 
        simp only [denote_regular, denote]
        have H: ∀a': A.stlc_ty.interp, a' = none 
          := by {
            cases H with
            | expr H => 
              intro a';
              cases a' with
              | none => rfl
              | some a' => 
                rw [H.prop_is_bot] at a'
                cases a'
          };
        rw [<-H]
  }

-- NOTE: I don't think wk1 is necessary here, due to the fact that
-- A.wk1.stlc_ty = A.stlc_ty, and also that a is not passed to itself...
-- or something like that...
def Context.denote: (Γ: Context) -> Γ.upgrade.stlc.interp -> Prop
| [], () => True
| (Hyp.mk A (HypKind.val type))::Γ, (a, G) => 
  A.denote_ty Γ G a ∧ denote Γ G
| (Hyp.mk φ (HypKind.val prop))::Γ, G =>
  φ.denote_ty Γ G none ∧ denote Γ G
| (Hyp.mk A HypKind.gst)::Γ, (a, G) =>
  A.denote_ty Γ G a ∧ denote Γ G

--set_option pp.explicit true

theorem HasVar.denote_annot
  (Hv: HasVar Γ n (HypKind.val s) A)
  (HΓ: IsCtx Γ)
  (G: Γ.upgrade.stlc.interp)
  (HG: Γ.denote G)
  : (expr s A).denote Γ G ((HΓ.var Hv).stlc.interp G.downgrade)
  := by {
    induction Γ generalizing s n A with
    | nil => cases Hv
    | cons H Γ I =>   
      cases H with
      | mk A k =>
        cases k with
        | val s => 
          cases s with
          | type => 
            let (x, G) := G;
            have ⟨Hx, HG⟩ := HG;
            cases Hv with
            | zero Hk => 
              cases Hk;
              simp only [denote, Context.stlc]
              apply Term.denote_wk1_ty _ _ Γ x G _ _ _ Hx
              rw [Stlc.Context.interp.downgrade_ty]
              rw [Stlc.HasType.interp_var]
              dsimp only [Stlc.HasVar.interp, Sparsity.ix]
              simp only [Eq.mp, Eq.mpr]
              conv =>
                rhs
                rw [monorecursor]
                skip
                rw [<-A.stlc_ty_wk1]
            | succ Hv => 
              cases HΓ with
              | cons_val HΓ =>
                have I' := I Hv HΓ G HG;
                cases s with
                | type =>
                  simp only [denote, Context.stlc]
                  apply Term.denote_wk1_ty _ _ Γ x G _ _ _ I'
                  rw [monorecursor]
                  rename Nat => n;
                  rw [Stlc.HasType.interp_transport_mono]
                  rw [Stlc.Context.interp.downgrade_ty]
                  rw [Stlc.HasType.var_interp_wk1]
                  rfl
                  rw [Term.stlc_var]
                  dsimp only [Sparsity.stlc]
                  split
                  . rfl
                  . have s := Hv.sigma_ty;
                    contradiction
                  rw [Term.stlc_ty_wk1]
                  constructor
                  exact Hv.stlc
                  rw [Term.stlc_var]
                  dsimp only [Sparsity.stlc]
                  split
                  . rfl
                  . have s := Hv.sigma_ty;
                    contradiction
                  rw [Term.stlc_ty_wk1]
                  rfl
                  rw [Term.stlc_ty_wk1]
                  rfl
                | prop => 
                  simp only [denote]
                  exact 
                    Term.denote_wk1_ty _ _ Γ x G 
                      none none (by rw [interp_eq_none]) I';
          | prop => 
            have ⟨Hx, HG⟩ := HG;
            cases Hv with
            | zero Hk => 
              cases Hk;
              simp only [denote, Context.stlc]
              apply Term.denote_wk1_prop _ _ Γ G _ _ _ Hx
              rw [interp_eq_none]
            | succ Hv => 
              cases HΓ with
              | cons_val HΓ =>
                have I' := I Hv HΓ G HG;
                cases s with
                | type =>                   
                  simp only [denote, Context.stlc]
                  apply Term.denote_wk1_prop _ _ Γ G _ _ _ I'
                  rw [monorecursor]
                  rename Nat => n;
                  rw [Stlc.HasType.interp_transport_mono]
                  rfl
                  rw [Term.stlc_var]
                  dsimp only [Sparsity.stlc]
                  split
                  . dsimp only [Term.stlc, Sparsity.stlc]
                    split
                    . rfl
                    . have s := Hv.sigma_ty;
                      contradiction
                  . have s := Hv.sigma_ty;
                    contradiction
                  rw [Term.stlc_ty_wk1]
                  constructor
                  rw [Term.stlc_ty_wk1]
                  rfl
                | prop => 
                  simp only [denote]
                  exact 
                    Term.denote_wk1_prop _ _ Γ G 
                      none none (by rw [interp_eq_none]) I';
        | gst => 
          cases Hv with
          | zero Hk => cases Hk
          | succ Hv => 
            cases HΓ with
            | cons_gst HΓ => 
              let (x, G) := G;
              have ⟨Hx, HG⟩ := HG;
              have I' := I Hv HΓ G HG;
              cases s with
              | type => 
                simp only [denote, Context.stlc]
                apply Term.denote_wk1_gst _ _ Γ x G _ _ _ I'
                rw [monorecursor]
                rw [Stlc.HasType.interp_transport_mono]
                rw [Stlc.Context.interp.downgrade_gst]
                rfl
                rw [Term.stlc_ty_wk1]
                rfl
                rw [Term.stlc_ty_wk1]
                rfl
              | prop => 
                simp only [denote]
                exact 
                  Term.denote_wk1_gst _ _ Γ x G 
                    none none (by rw [interp_eq_none]) I';
  }

theorem HasType.denote
  (H: Γ ⊢ a: A)
  (HΓ: IsCtx Γ)
  (G: Γ.upgrade.stlc.interp)
  (HG: Γ.denote G)
  : A.denote Γ G (H.stlc.interp G.downgrade)
  := by {
    induction H with
    | var HA Hv IA => exact Hv.denote_annot HΓ G HG
    | lam Hs HA Is IA => 
      dsimp only [Annot.denote, Term.denote_ty]
      intro x Hx
      cases x with
      | some x => 
        dsimp only [
          Annot.stlc_ty, term, Term.stlc_ty, Term.stlc, 
          Stlc.HasType.interp, 
          Ty.interp.app, Ty.interp.bind_val
        ]
        rw [<-Stlc.Context.interp.downgrade_ty]
        apply Is
        constructor
        exact HΓ
        exact HA
        exact ⟨Hx, HG⟩
      | none => sorry --TODO: contradiction
    | app => sorry
    | pair => sorry
    | let_pair => sorry
    | inj_l => sorry
    | inj_r => sorry
    | case => sorry
    | elem => sorry
    | let_set => sorry
    | lam_pr => sorry
    | app_pr => sorry
    | lam_irrel => sorry
    | app_irrel => sorry
    | repr => sorry
    | let_repr => sorry
    | top => sorry
    | bot => sorry
    | nil => sorry
    | abort => sorry
    | dconj => sorry
    | let_conj => sorry
    | disj_l => sorry
    | disj_r => sorry
    | case_pr => sorry
    | imp => sorry
    | mp => sorry
    | general => sorry
    | inst => sorry
    | wit => sorry
    | let_wit => sorry
    | refl => sorry
    | sym => sorry
    | trans => sorry
    | cong => sorry
    | beta => sorry
    | eta => sorry
    | irir => sorry
    | prir => sorry
    | succ => 
      intro x H;
      cases x with
      | none => cases H
      | some x => exact True.intro
    | natrec => sorry
    | _ => exact True.intro
  }