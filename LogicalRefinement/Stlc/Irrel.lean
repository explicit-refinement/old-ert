import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Utils
open Annot
open AnnotSort

@[simp] def Stlc.has_dep: Stlc -> Nat -> Prop
  | var v, i => v = i
  | lam _ s, i => s.has_dep (i + 1)
  | app _ l r, i => l.has_dep i ∨ r.has_dep i
  | let_in _ e e', i => e.has_dep i ∨ e'.has_dep (i + 1)
  | pair l r, i => l.has_dep i ∨ r.has_dep i
  | let_pair _ e e', i => e.has_dep i ∨ e'.has_dep (i + 2)
  | inj _ e, i => e.has_dep i
  | case _ d l r, i => d.has_dep i ∨ l.has_dep (i + 1) ∨ r.has_dep (i + 1)
  | natrec _ n z s, i => n.has_dep i ∨ z.has_dep i ∨ s.has_dep (i + 2)
  | _, _ => False

@[simp] def Stlc.Context.eq_at:  
  (Γ Δ: Stlc.Context) -> Nat -> Prop
  | [], [], _ => True
  | (A::_), (B::_), 0 => A = B
  | (_::Γ), (_::Δ), n + 1 => eq_at Γ Δ n
  | _, _, _ => False

@[simp] def Stlc.Context.interp.eq_at:  
  {Γ Δ: Stlc.Context} -> (G: Γ.interp) -> (D: Δ.interp) -> Nat -> Prop
  | [], [], (), (), _ => True
  | (A::_), (B::_), (x, _), (x', _), 0 => ∃p: A = B, p ▸ x = x'
  | (_::_), (_::_), (_, G), (_, G'), n + 1 => G.eq_at G' n
  | _, _, _, _, _ => False

theorem Stlc.Context.interp.eq_at.ctx_eq_at 
  {Γ Δ: Stlc.Context} {G: Γ.interp} {D: Δ.interp} {n: Nat}
  (H: G.eq_at D n)
  : Γ.eq_at Δ n
  := by {
    induction n generalizing Γ Δ with
    | zero => 
      cases Γ with
      | nil => cases Δ <;> cases H <;> simp
      | cons A Γ => cases Δ <;> cases H <;> assumption
    | succ n I => 
      cases Γ with
      | nil => cases Δ <;> cases H <;> simp
      | cons A Γ => 
        cases Δ with
        | nil => cases H
        | cons => exact I H
  }

theorem Stlc.Context.interp.eq_at_refl  
  {Γ: Stlc.Context} (G: Γ.interp) (n: Nat):
  G.eq_at G n
  := by {
    induction Γ generalizing n with
    | nil => exact True.intro
    | cons H Γ I =>
      cases n with
      | zero => exact ⟨rfl, rfl⟩
      | succ n => exact I _ _
  }

theorem Stlc.Context.eq_at_refl  
  (Γ: Stlc.Context) (n: Nat):
  Γ.eq_at Γ n
  := by {
    induction Γ generalizing n with
    | nil => exact True.intro
    | cons H Γ I =>
      cases n with
      | zero => rfl
      | succ n => exact I n
  }

def Stlc.Context.eq_mod 
  (Γ Δ: Stlc.Context) (a: Stlc): Prop
  := ∀n: Nat, a.has_dep n -> Γ.eq_at Δ n

def Stlc.Context.interp.eq_mod 
  {Γ Δ: Stlc.Context} (G: Γ.interp) (D: Δ.interp) (a: Stlc): Prop
  := ∀n: Nat, a.has_dep n -> G.eq_at D n

theorem Stlc.Context.interp.eq_mod.ctx_eq_mod 
  {Γ Δ: Stlc.Context} {G: Γ.interp} {D: Δ.interp} {a: Stlc}
  (H: G.eq_mod D a)
  : Γ.eq_mod Δ a
  := λn Hd => (H n Hd).ctx_eq_at

theorem Stlc.HasVar.interp_eq_mod
  {Γ Δ: Stlc.Context} {n: Nat} {A: Ty} {G: Γ.interp} {D: Δ.interp}
  (Hv: HasVar Γ n A)
  (Hv': HasVar Δ n A)
  (H: G.eq_at D n)
  : Hv.interp G = Hv'.interp D
  := by {
    induction Hv generalizing Δ with
    | zero => 
      cases Hv'; 
      cases G; 
      cases D; 
      have ⟨HAB, Hxy⟩ := H;
      cases HAB;
      cases Hxy;
      rfl
    | succ Hv I =>
      cases Hv'; cases G; cases D; 
      dsimp only [interp]
      rw [I]
      exact H
  }

theorem Stlc.HasType.eq_mod
  {Γ Δ: Stlc.Context} {a: Stlc} {A: Ty} 
  {G: Γ.interp} {D: Δ.interp}
  (Ha: Γ ⊧ a: A)
  (Ha': Δ ⊧ a: A)
  (H: G.eq_mod D a)
  : Ha.interp G = Ha'.interp D
  := by {
    induction Ha generalizing Δ with
    | var Hv => exact Hv.interp_eq_mod _ (H _ rfl)
    | lam Hs Is =>
      cases Ha';
      dsimp only [interp]
      apply congr rfl;
      funext x;
      apply Is;
      intro n Hn;
      cases n with
      | zero => exact ⟨rfl, rfl⟩
      | succ n => exact H _ Hn;
    | app Hl Hr Il Ir => 
      cases Ha';
      dsimp only [interp]
      rw [Il]
      rw [Ir]
      intro n Ht; exact H _ (Or.inr Ht);
      intro n Hs; exact H _ (Or.inl Hs);
    | let_in He He' Ie Ie' => 
      cases Ha';
      dsimp only [interp]
      apply congr _ rfl;
      apply congr _ rfl;
      apply congr;
      apply congr rfl _;
      apply Ie;
      intro n He; exact H _ (Or.inl He);
      funext _;
      apply Ie';
      intro n He';
      cases n with
      | zero => exact ⟨rfl, rfl⟩
      | succ n => exact H _ (Or.inr He')
    | pair Hl Hr Il Ir => 
      cases Ha';
      dsimp only [interp]
      rw [Il]
      rw [Ir]
      intro n Ht; exact H _ (Or.inr Ht);
      intro n Hs; exact H _ (Or.inl Hs);
    | let_pair He He' Ie Ie' => 
      cases Ha';
      dsimp only [interp]
      apply congr _ rfl;
      apply congr _ rfl;
      apply congr;
      apply congr rfl _;
      apply Ie;
      intro n He; exact H _ (Or.inl He);
      funext _;
      apply Ie';
      intro n He';
      cases n with
      | zero => exact ⟨rfl, rfl⟩
      | succ n => 
        cases n with
        | zero => exact ⟨rfl, rfl⟩
        | succ n => exact H _ (Or.inr He')
    | inj0 He Ie => 
      cases Ha';
      dsimp only [interp]
      rw [Ie]
      intro n He; exact H _ He;
    | inj1 He Ie => 
      cases Ha';
      dsimp only [interp]
      rw [Ie]
      intro n He; exact H _ He;
    | case Hd Hl Hr Id Il Ir => 
      cases Ha';
      dsimp only [interp]
      apply congr _ rfl;
      apply congr _ rfl;
      apply congr;
      apply congr rfl _;
      apply Id;
      intro n Hd; exact H _ (Or.inl Hd);
      funext _;
      apply congr;
      apply congr rfl _;
      funext _;
      apply Il;
      intro n He';
      cases n with
      | zero => exact ⟨rfl, rfl⟩
      | succ n => exact H _ (Or.inr (Or.inl He'))
      funext _;
      apply Ir;
      intro n He';
      cases n with
      | zero => exact ⟨rfl, rfl⟩
      | succ n => exact H _ (Or.inr (Or.inr He'))
    | natrec Hn Hz Hs In Iz Is =>       
      cases Ha';
      dsimp only [interp]
      apply congr _ rfl;
      apply congr _ rfl;
      apply congr;
      apply congr rfl _;
      apply In;
      intro n Hn; exact H _ (Or.inl Hn);
      funext _;
      apply congr;
      apply congr rfl _;
      apply Iz;
      intro n Hz; exact H _ (Or.inr (Or.inl Hz));
      funext _;
      apply Is;
      intro n He';
      cases n with
      | zero => exact ⟨rfl, rfl⟩
      | succ n => 
        cases n with
        | zero => exact ⟨rfl, rfl⟩
        | succ n => exact H _ (Or.inr (Or.inr He'))
    | _ => rfl
  }