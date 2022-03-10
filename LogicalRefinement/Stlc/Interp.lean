import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Untyped.Basic
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
open Term

def Term.stlc_ty: (a: Term) -> {Γ: Context} -> (p: HasType Γ a type) -> Ty
| _, _, _ => sorry