import LogicalRefinement.Utils
import LogicalRefinement.Wk
import LogicalRefinement.Untyped.Basic

@[simp] def Untyped.wk: Untyped -> Wk -> Untyped
  | var v, ρ => var (Wk.var ρ v)
  | const c, ρ => const c
  | unary k t, ρ => unary k (t.wk ρ)
  | let_bin k e, ρ => let_bin k (e.wk (ρ.liftn 2))
  | bin k l r, ρ => bin k (l.wk ρ) (r.wk ρ)
  | abs k A t, ρ => abs k (A.wk ρ) (t.wk ρ.lift)
  | tri k A l r, ρ => tri k (A.wk ρ) (l.wk ρ) (r.wk ρ)
  | cases k K d l r, ρ => 
    cases k (K.wk ρ.lift) (d.wk ρ) (l.wk ρ.lift) (r.wk ρ.lift)

@[simp] def Untyped.wk1 (u: Untyped) 
  := u.wk Wk.wk1

def Untyped.wk1_def {u: Untyped}: u.wk1 = u.wk Wk.wk1 := rfl

@[simp] def Untyped.lift1 (u: Untyped) := u.wk (Wk.lift Wk.id)

@[simp] def Untyped.wkn (u: Untyped) (n: Nat) 
  := u.wk (Wk.wkn n)

@[simp] def Untyped.wknth (u: Untyped) (n: Nat) 
  := u.wk (Wk.wknth n)

def Untyped.wknth_def {u: Untyped} {n}: u.wknth n = u.wk (Wk.wknth n) := rfl

@[simp] def Untyped.wk_coherent: {u: Untyped} -> {ρ σ: Wk} ->
  Wk.equiv ρ σ -> u.wk ρ = u.wk σ := by {
  intro u;
  induction u with
  | var v => intros ρ σ H; simp only [wk]; rw [H]
  | const c => simp
  | unary k t I => intros ρ σ H; simp [I H]
  | let_bin k e I => 
    intros ρ σ H;
    simp only [wk];
    simp only [I (@Wk.liftn_equiv 2 _ _ H)]
  | bin k l r Il Ir => intros ρ σ H; simp [Il H, Ir H]
  | abs k A s IHA IHs =>
    intros ρ σ H;
    simp only [wk];
    simp only [IHA H, IHs (Wk.lift_equiv H)]
  | tri k A l r IA Il Ir => intros ρ σ H; simp [IA H, Il H, Ir H]
  | cases k K d l r IK Id Il Ir => 
    intros ρ σ H; 
    simp only [wk];
    simp [
      IK (Wk.lift_equiv H), Id H, Il (Wk.lift_equiv H), Ir (Wk.lift_equiv H)
    ]
}

@[simp] def Untyped.wk_id {u: Untyped}: u.wk (Wk.id) = u := by {
  induction u;
  case var => simp
  repeat simp only [
    wk, Untyped.wk_coherent (Wk.liftn_id_equiv), 
    Untyped.wk_coherent Wk.lift_id_equiv,
  *]
}

def Untyped.wk_bounds {u: Untyped}: {n m: Nat} -> {ρ: Wk} ->
  wk_maps n m ρ -> fv u ≤ m -> fv (u.wk ρ) ≤ n := by {
    induction u with
    | var v => intros _ _ ρ Hm. apply Hm
    | const => intros. apply Nat.zero_le
    | unary k t IHt => 
      intros _ _ ρ Hm
      apply IHt Hm
    | let_bin k e IHe =>
      simp only [fv, Nat.le_sub_is_le_add]
      intros n m ρ Hm
      apply IHe
      apply wk_maps_liftn
      apply Hm
    | bin k l r IHl IHr =>
      simp only [fv, Nat.max_r_le_split]
      intros n m ρ Hm
      intro ⟨Hl, Hr⟩
      apply And.intro;
      case bin.left => apply IHl Hm Hl
      case bin.right => apply IHr Hm Hr
    | abs k A s IHA IHs =>
      simp only [fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
      intros n m ρ Hm
      intro ⟨HA, Hs⟩
      apply And.intro;
      case abs.left => apply IHA Hm HA
      case abs.right => 
        let Hm' := @wk_maps_liftn 1 n m ρ Hm
        apply IHs Hm' Hs
    | tri k A l r IHA IHl IHr =>
      simp only [fv, Nat.max_r_le_split]
      intros n m ρ Hm
      intro ⟨HA, Hl, Hr⟩
      apply And.intro;
      case left => apply IHA Hm HA
      case right =>
        apply And.intro;
        case left => apply IHl Hm Hl
        case right => apply IHr Hm Hr
    | cases k K d l r IK IHd IHl IHr => 
      simp only [fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
      intros n m ρ Hm
      intro ⟨HK, Hd, Hl, Hr⟩
      apply And.intro;
      case cases.left => apply IK (@wk_maps_liftn 1 n m ρ Hm) HK
      case cases.right => 
        apply And.intro;
        case left => apply IHd Hm Hd
        case right =>
          apply And.intro;
          case left => apply IHl (@wk_maps_liftn 1 n m ρ Hm) Hl
          case right => apply IHr (@wk_maps_liftn 1 n m ρ Hm) Hr
  }

def Untyped.fv_wk1: fv (wk1 u) ≤ fv u + 1 
  := by apply wk_bounds wk_maps_wk1; exact Nat.le_refl _

@[simp] def Untyped.wk_composes {u: Untyped}: 
  (σ ρ: Wk) -> (u.wk ρ).wk σ = u.wk (σ.comp ρ) 
  := by induction u <;> simp [*]

theorem Untyped.wk_wk1 {u: Untyped}: u.wk Wk.wk1 = u.wk1 
  := rfl
  
theorem Untyped.step_wk1 {u: Untyped}: u.wk ρ.step = (u.wk ρ).wk1 
  := by simp [<-Wk.step_is_comp_wk1]

theorem Untyped.lift_wk1 {u: Untyped}: u.wk1.wk ρ.lift = (u.wk ρ).wk1 
  := by simp