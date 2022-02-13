import LogicalRefinement.Utils
import LogicalRefinement.Wk
import LogicalRefinement.Untyped.Basic

@[simp] def RawUntyped.wk (ρ: RawWk): RawUntyped -> RawUntyped
  | var v => var (RawWk.var ρ v)
  | const c => const c
  | unary k t => unary k (wk ρ t)
  | let_bin k e => let_bin k (wk (RawWk.liftn 2 ρ) e)
  | bin k l r => bin k (wk ρ l) (wk ρ r)
  | abs k A t => abs k (wk ρ A) (wk (RawWk.lift ρ) t)
  | tri k A l r => tri k (wk ρ A) (wk ρ l) (wk ρ r)
  | cases k K d l r => cases k (wk (RawWk.lift ρ) K) (wk ρ d) (wk ρ l) (wk ρ r)

@[simp] def RawUntyped.wk1 (u: RawUntyped) := wk RawWk.wk1 u

@[simp] def RawUntyped.wkn (n: Nat) (u: RawUntyped) := wk (RawWk.wkn n) u

@[simp] def RawUntyped.wknth (n: Nat) (u: RawUntyped) := wk (RawWk.wknth n) u

@[simp] def RawUntyped.wk_coherent: {u: RawUntyped} -> {ρ σ: RawWk} ->
  RawWk.equiv ρ σ -> wk ρ u = wk σ u := by {
  intro u;
  induction u with
  | var v => intros ρ σ H; simp only [wk]; rw [H]
  | const c => simp
  | unary k t I => intros ρ σ H; simp [I H]
  | let_bin k e I => 
    intros ρ σ H;
    simp only [wk];
    simp only [I (@RawWk.liftn_equiv 2 _ _ H)]
  | bin k l r Il Ir => intros ρ σ H; simp [Il H, Ir H]
  | abs k A s IHA IHs =>
    intros ρ σ H;
    simp only [wk];
    simp only [IHA H, IHs (RawWk.lift_equiv H)]
  | tri k A l r IA Il Ir => intros ρ σ H; simp [IA H, Il H, Ir H]
  | cases k K d l r IK Id Il Ir => 
    intros ρ σ H; 
    simp only [wk];
    simp [IK (RawWk.lift_equiv H), Id H, Il H, Ir H]
}

@[simp] def RawUntyped.wk_id: wk (RawWk.id) u = u := by {
  induction u with
  | var v => simp
  | const c => simp
  | unary k t I => simp [I]
  | let_bin k e I =>
    simp only [wk]
    rw [RawUntyped.wk_coherent (RawWk.liftn_id_equiv)]
    rw [I]
  | bin k l r Il Ir => simp [Il, Ir]
  | abs k A s IHA IHs =>
    simp only [wk]
    rw [RawUntyped.wk_coherent RawWk.lift_id_equiv]
    rw [IHA, IHs]
  | tri k A l r IA Il Ir => simp [IA, Il, Ir]
  | cases k K d l r IK Id Il Ir => 
    simp only [wk]
    rw [RawUntyped.wk_coherent RawWk.lift_id_equiv]
    rw [IK, Id, Il, Ir]
}

def RawUntyped.wk_bounds {u: RawUntyped}: {n m: Nat} -> {ρ: RawWk} ->
  wk_maps n m ρ -> fv u ≤ m -> fv (wk ρ u) ≤ n := by {
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
          case left => apply IHl Hm Hl
          case right => apply IHr Hm Hr
  }

def RawUntyped.fv_wk1: fv (wk1 u) ≤ fv u + 1 := by {
  apply wk_bounds wk_maps_wk1;
  exact Nat.le_refl _
}

@[simp] def RawUntyped.wk_composes (u: RawUntyped): 
  (σ ρ: RawWk) -> wk σ (wk ρ u) = wk (RawWk.comp σ ρ) u := by {
  induction u with
  | var v => simp
  | const c => simp
  | unary k t I => simp [I]
  | let_bin k t I => simp [I]
  | bin k l r Il Ir => simp [Il, Ir]
  | abs k A t IA It => simp [IA, It] 
  | tri k A l r IA Il Ir => simp [IA, Il, Ir]
  | cases k K d l r IK Id Il Ir => simp [IK, Id, Il, Ir]
}

@[simp] def Untyped.wk (ρ: Wk n m) (u: Untyped m): Untyped n :=
  Untyped.mk (RawUntyped.wk ρ.val u.val) (RawUntyped.wk_bounds ρ.p u.p)

@[simp] def Untyped.wk_composes (σ: Wk n m) (ρ: Wk m l):
  wk σ (wk ρ u) = wk (Wk.comp σ ρ) u := by simp