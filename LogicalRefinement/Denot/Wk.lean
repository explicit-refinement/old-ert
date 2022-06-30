import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc
import LogicalRefinement.Denot.Basic

open AnnotSort
open Annot

--TODO: make stricter...
theorem Term.denote_wk1
  (A: Term) 
  (B: Term)
  (Γ: Context)
  (x: Option B.stlc_ty.interp) 
  (G: Γ.upgrade.stlc.interp) 
  (a: Option A.stlc_ty.interp)
  (a': Option A.wk1.stlc_ty.interp)
  (Haa': a' = A.stlc_ty_wk1 ▸ a)
  (H: A.denote_ty G a) 
  : @denote_ty A.wk1 (B.stlc_ty::Γ.upgrade.stlc) (x, G) a'
  := sorry