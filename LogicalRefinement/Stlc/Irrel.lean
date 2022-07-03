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

@[simp] def Stlc.Context.interp.eq_at:  
  {Γ: Stlc.Context} -> (G G': Γ.interp) -> Nat -> Prop
  | [], (), (), _ => True
  | (_::_), (x, _), (x', _), 0 => x = x'
  | (_::_), (_, G), (_, G'), n + 1 => G.eq_at G' n

def Stlc.Context.interp.eq_mod 
  {Γ: Stlc.Context} (G G': Γ.interp) (a: Stlc): Prop
  := ∀n: Nat, a.has_dep n -> G.eq_at G' n

theorem Stlc.HasVar.interp_eq_mod
  {Γ: Stlc.Context} {n: Nat} {A: Ty} {G G': Γ.interp}
  (Hv: HasVar Γ n A)
  (H: G.eq_at G' n)
  : Hv.interp G = Hv.interp G'
  := by {
    induction Hv with
    | zero => cases G; cases G'; rw [H]; rfl
    | succ Hv I =>
      cases G; cases G'; 
      dsimp only [interp]
      rw [I]
      exact H
  }

theorem Stlc.HasType.eq_mod
  {Γ: Stlc.Context} {a: Stlc} {A: Ty} {G G': Γ.interp}
  (Ha: Γ ⊧ a: A)
  (H: G.eq_mod G' a)
  : Ha.interp G = Ha.interp G'
  := by {
    induction Ha with
    | var Hv => exact Hv.interp_eq_mod (H _ rfl)
    | lam Hs Is =>
      dsimp only [interp]
      apply congr rfl;
      funext x;
      apply Is;
      intro n Hn;
      cases n with
      | zero => rfl
      | succ n => exact H _ Hn;
    | app Hl Hr Il Ir => sorry
    | let_in He He' Ie Ie' => sorry
    | pair Hl Hr Il Ir => sorry
    | let_pair He He' Ie Ie' => sorry
    | inj0 He Ie => sorry
    | inj1 He Ie => sorry
    | case Hd Hl Hr Id Il Ir => sorry
    | natrec Hn Hz Hs In Iz Is => sorry
    | _ => rfl
  }