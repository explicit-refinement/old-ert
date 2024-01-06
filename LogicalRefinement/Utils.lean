import Std.Data.Nat.Init.Lemmas
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Order.LinearOrder

theorem function_splitting {f g: A -> B}: f = g /\ x = y -> f x = g y := by {
  intro ⟨Hf, Hxy⟩;
  rw [Hf]
  rw [Hxy]
}

theorem or_imp_decompose {A B C D: Prop}:
  (A -> C) ∧ (B -> D) -> A ∨ B -> C ∨ D
  := by {
    intro ⟨F, G⟩;
    intro H;
    cases H with
    | inl H => exact Or.inl (F H)
    | inr H => exact Or.inr (G H)
  }

theorem and_imp_decompose {A B C: Prop}: (A ∧ B -> C) = (A -> B -> C)
  := propext (Iff.intro (λF a b => F ⟨a, b⟩) (λF ⟨a, b⟩ => F a b))

theorem monorecursor
  :
  @Eq.rec A x F D y p =
  @Eq.rec (Type) (F x rfl) (λA _ => A) D (F y p) p'
  := by {
    cases p;
    cases p';
    simp
  }

theorem rec_to_cast
  :
  @Eq.rec A x F D y p =
  cast p' D
  := by {
    cases p;
    rfl
  }

theorem mp_to_cast
  :
  Eq.mp p D =
  cast p D
  := by {
    cases p;
    rfl
  }

theorem rec_to_cast'
  :
  @Eq.rec A x F D y p =
  cast (by cases p; rfl) D
  := by {
    cases p;
    rfl
  }

theorem cast_merge {A B C: Type}
  {p: A = B}
  {p': B = C}
  {x: A}
  : cast p' (cast p x) = cast (p.trans p') x
  := by {
    cases p;
    cases p';
    rfl
  }

theorem pair_mono_transport
  :
  @Eq.rec (Type) (Prod A B) (λA _ => A) (x, y) (Prod C D) Ppair =
  (
    @Eq.rec (Type) A (λA _ => A) x C PA,
    @Eq.rec (Type) B (λA _ => A) y D PB
  )
  := by {
    cases PA;
    cases PB;
    cases Ppair;
    rfl
  }

theorem cast_pair {A B C D a b} (pa: A = C) (pb: B = D)
  : cast (by rw [pa, pb]) (a, b) = (cast pa a, cast pb b)
  := by {
    cases pa;
    cases pb;
    rfl
  }

theorem cast_pair' {A B C D a b} (pa: A = C) (pb: B = D) (p)
  : cast p (a, b) = (cast pa a, cast pb b)
  := by {
    cases pa;
    cases pb;
    rfl
  }

theorem cast_some
  : cast p (some a) = some (cast p' a)
  := by {
    cases p';
    rfl
  }

theorem cast_none (p: A = B)
  : cast (by rw [p]) (@none A) = @none B
  := by {
    cases p;
    rfl
  }

theorem cast_none' (p: A = B) (q)
  : cast q (@none A) = @none B
  := by {
    cases p;
    rfl
  }

theorem cast_inl {A B C D: Type} {a: A} (p: A = C) (p': B = D)
  : cast (by rw [p, p']) (@Sum.inl A B a) = @Sum.inl C D (cast p a)
  := by {
    cases p;
    cases p';
    rfl
  }

theorem cast_inr {A B C D: Type} {b: B} (p: A = C) (p': B = D)
  : cast (by rw [p, p']) (@Sum.inr A B b) = @Sum.inr C D (cast p' b)
  := by {
    cases p;
    cases p';
    rfl
  }

theorem cast_inl' {A B C D: Type} {a: A} (p: A = C) (p': B = D) (p'')
  : cast p'' (@Sum.inl A B a) = @Sum.inl C D (cast p a)
  := by {
    cases p;
    cases p';
    rfl
  }

theorem cast_inr' {A B C D: Type} {b: B} (p: A = C) (p': B = D) (p'')
  : cast p'' (@Sum.inr A B b) = @Sum.inr C D (cast p' b)
  := by {
    cases p;
    cases p';
    rfl
  }

theorem cast_tri {B: A -> Type} {D: C -> Type}
  (f: (a: A) -> B a)
  (x: C)
  (p: C = A)
  (p': p ▸ B = D)
  : @cast
    (B (p ▸ x)) (D x)
    (by cases p; cases p'; rfl)
    (f (cast p x)) =
    (@cast ((a: A) -> B a) ((c: C) -> D c) (by cases p; cases p'; rfl) f) x
  := by {
    cases p;
    cases p';
    rfl
  }

theorem cast_tri' {A B C D}
  (x: A)
  (f: C -> D)
  (p: A = C)
  (p': B = D)
  : cast p'.symm (f (cast p x))
  = (@cast (C -> D) (A -> B) (by cases p; cases p'; rfl) f) x
  := by {
    cases p;
    cases p';
    rfl
  }

theorem cast_tri'' {A B C D}
  (x: A)
  (f: C -> D)
  (p: A = C)
  (p': B = D)
  : cast p' ((@cast (C -> D) (A -> B) (by cases p; cases p'; rfl) f) x)
  = f (cast p x)
  := by {
    cases p;
    cases p';
    rfl
  }

theorem cast_dist {A B C D}
  (x: A)
  (f: A -> B)
  (p: A = C)
  (p': B = D)
  : cast p' (f x) = (@cast (A -> B) (C -> D) (by rw [p, p']) f) (cast p x)
  := by cases p; cases p'; rfl

theorem rec_down
  {A: Type}
  {a: A}
  {M: (b: A) -> a = b -> Type}
  {D D': M a rfl}
  {b: A}
  {p p': a = b}
  (H: D = D'):
  @Eq.rec A a M D b p =
  @Eq.rec A a M D' b p'
  := by {
    cases H;
    rfl
  }

theorem equiv_prop_helper {P Q: Prop} {H: P = Q}: P -> Q := by {
  cases H;
  exact id
}

theorem equiv_prop_split {P Q R S: Prop}
  (q: Q = R) (p: P = Q) (r: R = S):
  P = S
  := by {
    cases p; cases q; cases r; rfl
  }

theorem equiv_and_split {P Q R: Prop}:
  (P -> Q = R) -> (P ∧ Q) = (P ∧ R)
  := by {
    intro H;
    apply propext;
    apply Iff.intro;
    . intro ⟨p, q⟩; rw [<-H p]; exact ⟨p, q⟩
    . intro ⟨p, r⟩; rw [H p]; exact ⟨p, r⟩
  }

theorem equiv_or_split {P Q R S: Prop}:
  (P = R) -> (Q = S) -> (P ∨ Q) = (R ∨ S)
  := by {
    intro H H';
    cases H; cases H'; rfl
  }

theorem cast_not_none_is_not_none {p: Option A = Option B} (p': A = B):
  (cast p a ≠ none) = (a ≠ none)
  := by {
    cases a with
    | some a =>
      apply propext;
      --TODO: report unused variable bug here
      apply Iff.intro <;> intro _
      . simp
      . rw [cast_some]; simp; exact p'
    | none =>
      rw [cast_none]
      apply propext; apply Iff.intro <;> intro _ <;> contradiction
      exact p'
  }

theorem equiv_arrow_helper {A B C D: Prop}
  : A = C -> B = D -> (A -> B) = (C -> D)
  := by {
    intro H H';
    cases H; cases H'; rfl
  }

theorem equiv_arrow_helper' {A B C D: Prop}
  : A = C -> (A -> B = D) -> (A -> B) = (C -> D)
  := by {
    intro H H';
    cases H;
    apply propext;
    apply Iff.intro;
    {
      intro H'' a;
      rw [<-H' a]
      exact H'' a
    }
    {
      intro H'' a;
      rw [H' a]
      exact H'' a
    }
  }

theorem cast_app
  (A: Type)
  (B: A -> Type)
  (B': A -> Type)
  (HB: B = B')
  (a: A)
  (f: (a: A) -> B a):
  (@cast ((a: A) -> B a) ((a: A) -> B' a) (by rw [HB]) f) a
  = cast (by rw [HB]) (f a)
  := by {
    cases HB; rfl
  }

theorem cast_gen {p: A = C} {q: B = C}:
  cast p x = cast q y ->
  ∀{C'}, ∀{p: A = C'}, ∀{q: B = C'}, cast p x = cast q y
  := by {
    cases p;
    cases q;
    intro H;
    cases H;
    intros;
    rfl
  }

theorem some_eq_helper:
  some x = some y -> x = y
  := by {
    intro H;
    cases H;
    rfl
  }

theorem cast_app_pull_in {A B C}
  (f: A -> B)
  (a: A)
  (H: (A -> B) = (A -> C))
  (H': B = C):
  (@cast (A -> B) (A -> C) H f) a
  = cast H' (f a)
  := by {
    cases H';
    rfl
  }

theorem cast_app_pull_in_dep
  (A: Type)
  (B C: A -> Type)
  (f: (a: A) -> B a)
  (a: A)
  (H: ((a: A) -> B a) = ((a: A) -> C a))
  (H')
  (H'': B = C):
  (@cast ((a: A) -> B a) ((a: A) -> C a) H f) a
  = cast H' (f a)
  := by {
    cases H'';
    rfl
  }

theorem cast_lam
  (A B C: Type)
  (f: A -> C)
  (b: B)
  (H: (A -> C) = (B -> C))
  (H': B = A):
  (cast H f) b = f (cast H' b)
  := by {
    cases H';
    rfl
  }

theorem cast_lam'
  (A B C D: Type)
  (f: A -> C)
  (b: B)
  (H: A = B)
  (H': C = D)
  (H'': (A -> C) = (B -> D)):
  (cast H'' f) b = cast H' (f (cast H.symm b))
  := by {
    cases H;
    cases H';
    rfl
  }

theorem cast_result
  (A B C: Type)
  (f: A -> B)
  (H: B = C):
  (λx => cast (by rw [H]) (f x)) = cast (by rw [H]) f
  := by {
    cases H;
    rfl
  }

theorem arrow_equivalence {A B C D: Prop}:
  A = B -> C = D -> (A -> C) = (B -> D)
  := by {
    intros;
    simp only [*]
  }

theorem existential_helper {A: Prop} {B C: A -> Prop}
  (H: ¬A ∨ (B = C)): (∃x: A, B x) = (∃x: A, C x)
  := by {
    apply propext;
    apply Iff.intro;
    {
      intro ⟨Ha, Hb⟩;
      cases H with
      | inl => contradiction
      | inr H => rw [<-H]; exact ⟨Ha, Hb⟩
    }
    {
      intro ⟨Ha, Hc⟩;
      cases H with
      | inl => contradiction
      | inr H => rw [H]; exact ⟨Ha, Hc⟩
    }
  }

theorem forall_helper {A: Type} {B C: A -> Prop}
  (H: ∀x: A, B x = C x): (∀x: A, B x) = (∀x: A, C x)
  := by {
    apply propext;
    apply Iff.intro;
    {
      intro Hf x;
      rw [<-H];
      exact Hf x
    }
    {
      intro Hf x;
      rw [H];
      exact Hf x
    }
  }

theorem existential_forall_helper {A: Type} {B C: A -> Prop}
  (H: ∀x: A, B x = C x): (∃x: A, B x) = (∃x: A, C x)
  := by {
    apply propext;
    apply Iff.intro;
    {
      intro ⟨x, Hb⟩;
      exists x;
      rw [<-H];
      exact Hb
    }
    {
      intro ⟨x, Hc⟩;
      exists x;
      rw [H];
      exact Hc
    }
  }

theorem forall_helper_dep {A B: Type} {F: A -> Prop} {G: B -> Prop}
  (HAB: A = B)
  (H: ∀x: A, F x = G (HAB ▸ x)): (∀x: A, F x) = (∀x: B, G x)
  := by {
    cases HAB;
    exact forall_helper H;
  }


theorem existential_forall_helper_dep {A B: Type} {C: A -> Prop} {D: B -> Prop}
  (HAB: A = B)
  (H: ∀x: A, C x = D (HAB ▸ x)): (∃x: A, C x) = (∃x: B, D x)
  := by {
    cases HAB;
    exact existential_forall_helper H;
  }

  theorem cast_app_prop
  (A B: Sort u)
  (f: A -> Prop)
  (b: B)
  (H: (A -> Prop) = (B -> Prop))
  (H': B = A):
  (cast H f) b
  = f (cast H' b)
  := by {
    cases H';
    rfl
  }

theorem cast_app_dep_first
  {A: Sort u} {B: A -> Sort v} {C: Sort w}
  (f: (a: A) -> B a -> C)
  (a a': A)
  (b: B a)
  (p: a = a')
  (p': B a = B a'):
  f a' (cast p' b) = f a b
  := by {
    cases p; cases p'; rfl
  }

theorem cast_app_dep_bin
  {A: Sort u} {B: A -> Sort v} {C: (a: A) -> B a -> Sort w}
  (f: (a: A) -> (b: B a) -> C a b)
  (a a': A)
  (b: B a)
  (p: a = a')
  (p': B a = B a')
  (p'': C a' (cast p' b) = C a b):
  cast p'' (f a' (cast p' b)) = f a b
  := by {
    cases p; cases p'; rfl
  }

theorem cast_app_dep_one
  {A: Sort u} {B: A -> Sort v} {C: Sort w}
  (f: (a: A) -> B a -> C)
  (a a': A)
  (b: B a)
  (b': B a')
  (pa: a = a')
  (pb: b' = cast (by rw [pa]) b):
  f a' b' = f a b
  := by {
    cases pa; cases pb; rfl
  }

theorem cast_app_dep_two
  {A: Sort u0}
  {B: A -> Sort u1}
  {C: (a: A) -> B a -> Sort u2}
  {R: Sort v}
  (f: (a: A) -> (b: B a) -> C a b -> R)
  (a a': A)
  (b: B a)
  (b': B a')
  (c: C a b)
  (c': C a' b')
  (pa: a = a')
  (pb: b' = cast (by rw [pa]) b)
  (pc: c' = cast (cast_app_dep_one C a a' b b' pa pb).symm c):
  f a' b' c' = f a b c
  := by {
    cases pa; cases pb; cases pc; rfl
  }

theorem cast_app_dep_three
  {A: Sort u0}
  {B: A -> Sort u1}
  {C: (a: A) -> B a -> Sort u2}
  {D: (a: A) -> (b: B a) -> (c: C a b) -> Sort u3}
  {R: Sort v}
  (f: (a: A) -> (b: B a) -> (c: C a b) -> D a b c -> R)
  (a a': A)
  (b: B a)
  (b': B a')
  (c: C a b)
  (c': C a' b')
  (d: D a b c)
  (d': D a' b' c')
  (pa: a = a')
  (pb: b' = cast (by rw [pa]) b)
  (pc: c' = cast (cast_app_dep_one C a a' b b' pa pb).symm c)
  (pd: d' = cast (cast_app_dep_two D a a' b b' c c' pa pb pc).symm d)
  :
  f a' b' c' d' = f a b c d
  := by {
    cases pa; cases pb; cases pc; cases pd; rfl
  }

theorem cast_app_dep_four
  {A: Sort u0}
  {B: A -> Sort u1}
  {C: (a: A) -> B a -> Sort u2}
  {D: (a: A) -> (b: B a) -> (c: C a b) -> Sort u3}
  {E: (a: A) -> (b: B a) -> (c: C a b) -> (d: D a b c) -> Sort u4}
  {R: Sort v}
  (f: (a: A) -> (b: B a) -> (c: C a b) -> (d: D a b c) -> E a b c d -> R)
  (a a': A)
  (b: B a)
  (b': B a')
  (c: C a b)
  (c': C a' b')
  (d: D a b c)
  (d': D a' b' c')
  (e: E a b c d)
  (e': E a' b' c' d')
  (pa: a = a')
  (pb: b' = cast (by rw [pa]) b)
  (pc: c' = cast (cast_app_dep_one C a a' b b' pa pb).symm c)
  (pd: d' = cast (cast_app_dep_two D a a' b b' c c' pa pb pc).symm d)
  (pe: e' = cast (cast_app_dep_three E a a' b b' c c' d d' pa pb pc pd).symm e)
  :
  f a' b' c' d' e' = f a b c d e
  := by {
    cases pa; cases pb; cases pc; cases pd; cases pe; rfl
  }

theorem cast_bind {A B A' B'}
  {H: Option B = Option B'}
  {H': Option A = Option A'}
  {H'': (A -> Option B) = (A' -> Option B')}
  (x: Option A)
  (f: A -> Option B)
  (p: A = A')
  (p': B = B')
  : cast H (Option.bind x f) =
  Option.bind (cast H' x) (cast H'' f)
  := by {
    cases p; cases p'; rfl
  }

theorem cast_fun_bind {A B A' B'}
  {H: B = B'}
  (x: Option A)
  (f: A -> Option B)
  (p: A = A')
  (p': B = B')
  : cast (by rw [H]) (Option.bind x f) =
  Option.bind x (cast (by rw [H]) f)
  := by {
    cases p; cases p'; rfl
  }

theorem cast_trans:
  (b = cast H a) = (cast H.symm b = a)
  := by {
    cases H;
    rfl
  }

theorem doublecast_self {A B} {a: A} (H: B = A):
  a = cast H (cast H.symm a)
  := by cases H; rfl

theorem cast_to_self {H: A = A} {a: A}: cast H a = a := rfl
