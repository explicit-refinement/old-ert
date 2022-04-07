def Sparsity := List Bool


@[simp]
def Sparsity.dep: Sparsity -> Nat -> Bool
| [], n => true
| b::Hs, 0 => b
| b::Hs, Nat.succ n => dep Hs n

theorem Sparsity.dep_get? {Γ: Sparsity} {n b}
  : Γ.get? n = some b -> Γ.dep n = b
  := by {
    revert n;
    induction Γ with
    | nil => intro n H; cases H
    | cons H Γ I =>
      intro n Hn;
      cases n with
      | zero => simp [List.get?] at Hn; simp [Hn]
      | succ n => simp only [dep, I Hn]
  }

def Sparsity.wknth: Sparsity -> Nat -> Bool -> Sparsity
| H::Γ, Nat.succ n, b => H::(wknth Γ n b)
| [], Nat.succ n, b => true::(wknth [] n b)
| Γ, 0, b => b::Γ

@[simp]
def Sparsity.ix: Sparsity -> Nat -> Nat
| true::Hs, Nat.succ n => (ix Hs n) + 1
| false::Hs, Nat.succ n => ix Hs n
| _, n => n

@[simp]
def Sparsity.ix_inv: Sparsity -> Nat -> Nat
| true::Hs, Nat.succ n => (ix_inv Hs n) + 1
| false::Hs, n => (ix_inv Hs n) + 1
| _, n => n

def Sparsity.ix_inv_valid (Γ: Sparsity) {n: Nat}:
  Γ.dep n = true -> Γ.ix_inv (Γ.ix n) = n
  := by {
    revert n;
    induction Γ with
    | nil => intro n H; rfl
    | cons H Γ I =>
      intro n;
      cases n with
      | zero => 
        intro Hn;
        cases H with
        | true => rfl
        | false => simp [List.get?] at Hn
      | succ n =>
        intro Hn;
        cases H <;> simp [ix, ix_inv, I Hn] 
  }
