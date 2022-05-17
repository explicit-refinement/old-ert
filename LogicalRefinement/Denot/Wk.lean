import LogicalRefinement.Untyped
import LogicalRefinement.Typed
import LogicalRefinement.Stlc
import LogicalRefinement.Denot.Basic

open AnnotSort
open Annot

theorem Term.denote_wk1_ty
  (A: Term) 
  (B: Term)
  (Γ: Context)
  (x: B.stlc_ty.interp) 
  (G: Γ.upgrade.stlc.interp) 
  (a: A.stlc_ty.interp)
  (a': A.wk1.stlc_ty.interp)
  (Haa': a' = A.stlc_ty_wk1 ▸ a)
  (H: A.denote_ty' G a) 
  : @denote_ty' A.wk1 ((Hyp.val B type)::Γ) (x, G) a'
  := sorry
  
theorem Term.denote_wk1_prop
  (A: Term) 
  (φ: Term)
  (Γ: Context)
  (G: Γ.upgrade.stlc.interp) 
  (a: A.stlc_ty.interp)
  (a': A.wk1.stlc_ty.interp)
  (Haa': a' = A.stlc_ty_wk1 ▸ a)
  (H: @denote_ty' A Γ G a) 
  : @denote_ty' A.wk1 ((Hyp.val φ prop)::Γ) G a'
  := sorry
  
theorem Term.denote_wk1_gst
  (A: Term) 
  (B: Term)
  (Γ: Context) 
  (x: B.stlc_ty.interp)
  (G: Γ.upgrade.stlc.interp) 
  (a: A.stlc_ty.interp)
  (a': A.wk1.stlc_ty.interp)
  (Haa': a' = A.stlc_ty_wk1 ▸ a)
  (H: A.denote_ty' G a) 
  : @denote_ty' A.wk1 ((Hyp.gst B)::Γ) (x, G) a'
  := sorry