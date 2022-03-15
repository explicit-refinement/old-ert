import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Untyped.Basic
import LogicalRefinement.Typed.Context
import LogicalRefinement.Typed.Basic
import LogicalRefinement.Typed.Regular
open Term
open TermKind

def Term.stlc_ty: {a: Term} -> {Γ: Context} -> (p: HasType Γ a AnnotSort.type) -> Ty
| var _, _, p => False.elim p.no_poly
| const k, _, p => by {
  cases k with
  | unit => exact Ty.unit
  | nats => exact Ty.nats
  | _ => apply False.elim; cases p
}
| abs k A B, _, p => by {
    cases k with
    | pi =>
      apply Ty.arrow
      apply @stlc_ty A
      cases p; assumption
      apply @stlc_ty B
      cases p; assumption
    | sigma => sorry
    | assume => sorry
    | set => sorry
    | intersect => sorry
    | union => sorry
    | _ => apply False.elim; cases p
}
| unary k _, _, p => by { cases k <;> apply False.elim <;> cases p }
| let_bin k _ _, _, p => by { cases k <;> apply False.elim <;> cases p }
| bin k A B, _, p => by {
  cases k with
  | coprod => sorry
  | _ => apply False.elim; cases p
}
| tri k _ _ _, _, p => by { cases k <;> apply False.elim <;> cases p }
| cases k _ _ _ _, _, p => by { cases k <;> apply False.elim <;> cases p }
| natrec _ _ _ _, _, p => by { apply False.elim; cases p }