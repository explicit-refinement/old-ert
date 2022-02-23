import Lean

open Lean Elab.Tactic Meta

-- Adapted from https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/BuiltinTactic.lean
def renameInaccessibles' (mvarId : MVarId) (hs : Array Syntax) : TacticM MVarId := do
  if hs.isEmpty then
    return mvarId
  else
    let mvarDecl ← getMVarDecl mvarId
    let mut lctx  := mvarDecl.lctx
    let mut hs    := hs
    let mut found : NameSet := {}
    let n := lctx.numIndices
    for i in [:n] do
      let j := n - i - 1
      match lctx.getAt? j with
      | none => pure ()
      | some localDecl =>
        if localDecl.userName.hasMacroScopes || found.contains localDecl.userName then
          let h := hs.back
          if h.isIdent then
            let newName := h.getId
            lctx := lctx.setUserName localDecl.fvarId newName
          hs := hs.pop
          if hs.isEmpty then
            break
        found := found.insert localDecl.userName
    -- unless hs.isEmpty do
    --   Lean.Elab.logError m!"too many variable names provided"
    let mvarNew ← mkFreshExprMVarAt lctx mvarDecl.localInstances mvarDecl.type MetavarKind.syntheticOpaque mvarDecl.userName
    assignExprMVar mvarId mvarNew
    return mvarNew.mvarId!

syntax "rename_i'" ident*: tactic

elab_rules : tactic
  | `(tactic| rename_i' $hs*) => 
    do replaceMainGoal [← renameInaccessibles' (← getMainGoal) hs]

def test_assumption: A -> A := by {
  intros;
  rename_i' a b c d e;
  first | apply e | apply d | apply c | apply b | apply a
}