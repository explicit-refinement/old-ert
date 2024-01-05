# Stuff that broke:
- `simp`/`dsimp` now errors when it fails to make progress
    - Fixes:
        - Needed to change things to `try simp`
        - Needed to fix bracketing around `try` in a few places
        - Removed a lot of unnecessary use of `simp` which originally cleaned up syntax
        - Had to fix the `upgrade_ctx` custom tactic to use `try simp`
- A few lemmas don't seem to work with `rw` anymore, all of a similar family
    - Lemmas:
        - `Annot.stlc_ty_wk` ==> had to use `Annot.stlc_ty_wk'`
            - Seems `Term.wk` and `Annot.wk` changed reduction behaviour
        - `Stlc.HasType.interp_wk1`; had to play with this for a bit
        - `Annot.stlc_ty_subst H.expr_regular`; `HC.stlc_ty_subst`
        - `HB.stlc_ty_subst0`; needed to add `HC.stlc_ty_subst0` to a `simp` set as well
- `rw` now detects more `rfl`; so had to remove some redundant `rfl` calls

# Other notes
- Ran out of memory re-running `Subst.lean`; seems the VSCode plugin is still leaking
- Things like `set_option maxHeartbeats 10000000` are _not_ a good sign
- In `Regular.lean`, it spins the CPU but memory seems to be fine
    - There's an unsolved goal: `case inr`. Must investigate
    - `HasType.denote` is a massive ~2000 line, very poorly written proof, so _somewhat_ to be
      expected...
    - `HasType.denote` takes ~2 min to compile in the IDE

# Improvements requested
- Small:
    - Highlight `stop` in red in VSCode plugin
- Big:
    - Cache branches of `induction`, `cases`, etc in tactic mode