import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Untyped.Basic
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Regular
open Term

def Term.stlc_ty: (a: Term) -> {Γ: Context} -> (p: HasType Γ a AnnotSort.type) -> Ty
| var v, _, H => False.elim H.no_poly
| _, _, _ => sorry