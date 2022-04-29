import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc

def Term.denote_ty (A: Term) (Γ: Context)
  (G: Γ.stlc.interp)
  (G': Γ.ghosts.interp)
  (a: A.stlc_ty.interp): Prop
  := match A with
  | const TermKind.unit => True
  | abs TermKind.pi _ _ => sorry
  | abs TermKind.sigma _ _ => sorry
  | abs TermKind.assume _ _ => sorry
  | abs TermKind.set _ _ => sorry
  | abs TermKind.intersect _ _ => sorry
  | abs TermKind.union _ _ => sorry
  | const TermKind.top => True
  | const TermKind.bot => False
  | abs TermKind.dimplies _ _ => sorry
  | abs TermKind.dand _ _ => sorry
  | bin TermKind.or _ _ => sorry
  | abs TermKind.forall_ _ _ => sorry
  | abs TermKind.exists_ _ _ => sorry
  | tri TermKind.eq _ _ _ => sorry
  | const TermKind.nats => True
  | _ => False