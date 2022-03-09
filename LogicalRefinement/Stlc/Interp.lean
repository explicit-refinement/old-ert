import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Untyped.Basic

inductive Stlc.Interp
| ty (A: Ty)
| term (s: Stlc)

open Stlc.Interp
open Term

def Term.interp: Term -> Stlc.Interp
| _ => sorry