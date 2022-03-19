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
| const TermKind.unit => Ty.unit
| abs TermKind.pi A B => Ty.arrow A.stlc_ty B.stlc_ty
| abs TermKind.sigma A B => Ty.prod A.stlc_ty B.stlc_ty
| bin TermKind.coprod A B => Ty.coprod A.stlc_ty B.stlc_ty
| abs TermKind.assume φ A => A.stlc_ty
| abs TermKind.set A φ => A.stlc_ty
| abs TermKind.intersect A B => B.stlc_ty
| abs TermKind.union A B => B.stlc_ty
| const TermKind.nats => Ty.nats
| _ => Ty.bot