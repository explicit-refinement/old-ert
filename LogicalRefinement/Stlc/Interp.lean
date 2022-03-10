import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Untyped.Basic
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Regular
open Term
open TermKind

def Term.stlc_ty (a: Term) {Γ: Context} (p: HasType Γ a AnnotSort.type): Ty := by {
  cases a with
  | var => exact False.elim p.no_poly
  | const k =>
    cases k with
    | unit => exact Ty.unit
    | nats => exact Ty.nats
    | _ => apply False.elim; cases p
  | abs k =>
    cases k with
    | pi => sorry
    | sigma => sorry
    | assume => sorry
    | set => sorry
    | intersect => sorry
    | union => sorry
    | _ => apply False.elim; cases p
  | unary k => cases k <;> apply False.elim <;> cases p
  | let_bin k => cases k <;> apply False.elim <;> cases p
  | bin k =>
    cases k with
    | coprod => sorry
    | _ => apply False.elim; cases p
  | tri k => cases k <;> apply False.elim <;> cases p
  | cases k => cases k <;> apply False.elim <;> cases p
  | natrec => apply False.elim; cases p
}