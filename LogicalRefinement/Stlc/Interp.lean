import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Untyped.Basic
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Regular
open Term
open TermKind

-- tfw your termination checker doesn't terminate
set_option maxHeartbeats 1000000

def Term.stlc_ty: Term -> Ty
| var _ => Ty.unit
| const TermKind.unit => Ty.unit
| const TermKind.nats => Ty.nats
| abs TermKind.pi A B => Ty.arrow A.stlc_ty B.stlc_ty
| _ => Ty.bot