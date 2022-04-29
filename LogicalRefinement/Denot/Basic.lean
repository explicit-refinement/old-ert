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
  | abs TermKind.sigma _ _ => sorry
  | abs TermKind.assume _ _ => sorry
  | abs TermKind.set _ _ => sorry
  | abs TermKind.intersect _ _ => sorry
  | abs TermKind.union _ _ => sorry
  | const TermKind.top => True
  | const TermKind.bot => False
  | abs TermKind.dimplies A B => 
    --TODO: think about this...
    (A.denote_ty Γ G none) -> (B.denote_ty Γ G none)
  | abs TermKind.dand A B =>
    --TODO: think about this...
    (A.denote_ty Γ G none) ∧ (B.denote_ty Γ G none)
  | bin TermKind.or A B => 
    (A.denote_ty Γ G none) ∨ (B.denote_ty Γ G none)
  | abs TermKind.forall_ _ _ => sorry
  | abs TermKind.exists_ _ _ => sorry
  | tri TermKind.eq A x y => 
    (px: Γ.upgrade ⊢ x: term A) -> 
    (py: Γ.upgrade ⊢ y: term A) ->
    (px.stlc.interp G) = (py.stlc.interp G)
  | const TermKind.nats => 
    match a with
    | some _ => True
    | none => False
  | _ => False