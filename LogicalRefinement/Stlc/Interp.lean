import LogicalRefinement.Stlc.Basic
import LogicalRefinement.Untyped
import LogicalRefinement.Typed
open Term
open TermKind

-- tfw your termination checker doesn't terminate
set_option maxHeartbeats 1000000

def Term.stlc_ty: Term -> Ty
| const TermKind.unit => Ty.unit
| abs TermKind.pi A B => Ty.arrow A.stlc_ty B.stlc_ty
| abs TermKind.sigma A B => Ty.prod A.stlc_ty B.stlc_ty
| bin TermKind.coprod A B => Ty.coprod A.stlc_ty B.stlc_ty
| abs TermKind.assume φ A => Ty.arrow φ.stlc_ty A.stlc_ty
| abs TermKind.set A φ => Ty.prod A.stlc_ty φ.stlc_ty
| abs TermKind.intersect A B => Ty.arrow Ty.unit B.stlc_ty
| abs TermKind.union A B => Ty.prod Ty.unit B.stlc_ty
| const TermKind.nats => Ty.nats
| _ => Ty.unit

def Term.stlc: Term -> Stlc
| var n => Stlc.var n
| const TermKind.nil => Stlc.nil
| abs TermKind.lam A x => Stlc.lam A.stlc_ty x.stlc
| tri TermKind.app P l r => Stlc.app P.stlc_ty l.stlc r.stlc
| bin TermKind.pair l r => Stlc.pair l.stlc r.stlc
| let_bin TermKind.let_pair P e e' => 
  Stlc.let_pair P.stlc_ty e.stlc e'.stlc
| unary (TermKind.inj i) e => Stlc.inj i e.stlc
| cases TermKind.case P d l r => 
  Stlc.case P.stlc_ty d.stlc l.stlc r.stlc
| abs TermKind.lam_pr φ x => Stlc.lam φ.stlc_ty x.stlc
| tri TermKind.app_pr P e φ => Stlc.app P.stlc_ty e.stlc φ.stlc
| bin TermKind.elem e φ => e.stlc
| let_bin TermKind.let_set P e e' => Stlc.pair e.stlc Stlc.nil
| abs TermKind.lam_irrel A x => Stlc.lam Ty.unit x.stlc
| tri TermKind.app_irrel P l r => Stlc.app P.stlc_ty l.stlc Stlc.nil
| bin TermKind.repr l r => Stlc.pair Stlc.nil r.stlc
| let_bin TermKind.let_repr P e e' => 
  Stlc.let_pair P.stlc_ty e.stlc e'.stlc
| const TermKind.zero => Stlc.zero
| const TermKind.succ => Stlc.succ
| _ => Stlc.nil

def Context.stlc: Context -> Stlc.Context
| [] => []
| (Hyp.mk A (HypKind.val type))::Hs => A.stlc_ty::(stlc Hs)
| _::Hs => Ty.unit::(stlc Hs)

open Annot
open AnnotSort

theorem HasType.stlc_helper {Γ a A} (H: Γ ⊢ a: A):
  ∀{X}, A = term X -> 
  Stlc.HasType Γ.stlc a.stlc X.stlc_ty
  := by {
    induction H <;> intro X HX;

    --TODO: this

    all_goals sorry
  }

theorem HasType.stlc {Γ a A} (H: Γ ⊢ a: term A)
  : Stlc.HasType Γ.stlc a.stlc A.stlc_ty
  := stlc_helper H rfl