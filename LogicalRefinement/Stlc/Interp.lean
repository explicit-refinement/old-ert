import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Untyped.Basic
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Regular
open Term
open TermKind

def Term.stlc_ty: (a: Term) -> {Γ: Context} -> (p: HasType Γ a AnnotSort.type) -> Ty
| var v, _, H => False.elim H.no_poly

| const TermKind.unit, _, _ => Ty.unit
| abs TermKind.pi l r, Γ, H => by {
    apply Ty.arrow (stlc_ty l _) (stlc_ty r _) 
    <;> (try cases H; assumption)
  }
| _, _, _ => sorry