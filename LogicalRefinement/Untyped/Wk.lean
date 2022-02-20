import LogicalRefinement.Utils
import LogicalRefinement.Wk
import LogicalRefinement.Untyped.Basic

@[simp] def RawUntyped.wk: RawUntyped -> RawWk -> RawUntyped
  | var v, ρ => var (RawWk.var ρ v)
  | const c, ρ => const c
  | unary k t, ρ => unary k (t.wk ρ)
  | let_bin k e, ρ => let_bin k (e.wk (ρ.liftn 2))
  | bin k l r, ρ => bin k (l.wk ρ) (r.wk ρ)
  | abs k A t, ρ => abs k (A.wk ρ) (t.wk ρ.lift)
  | tri k A l r, ρ => tri k (A.wk ρ) (l.wk ρ) (r.wk ρ)
  | cases k K d l r, ρ => cases k (K.wk ρ.lift) (d.wk ρ) (l.wk ρ) (r.wk ρ)

@[simp] def RawUntyped.wk1 (u: RawUntyped) 
  := u.wk RawWk.wk1

def RawUntyped.wk1_def {u: RawUntyped}: u.wk1 = u.wk RawWk.wk1 := rfl

@[simp] def RawUntyped.lift1 (u: RawUntyped) := u.wk (RawWk.lift RawWk.id)

@[simp] def RawUntyped.wkn (u: RawUntyped) (n: Nat) 
  := u.wk (RawWk.wkn n)

@[simp] def RawUntyped.wknth (u: RawUntyped) (n: Nat) 
  := u.wk (RawWk.wknth n)

def RawUntyped.wknth_def {u: RawUntyped} {n}: u.wknth n = u.wk (RawWk.wknth n) := rfl

@[simp] def RawUntyped.wk_coherent: {u: RawUntyped} -> {ρ σ: RawWk} ->
  RawWk.equiv ρ σ -> u.wk ρ = u.wk σ := by {
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

@[simp] def RawUntyped.wk_id {u: RawUntyped}: u.wk (RawWk.id) = u := by {
  induction u;
  case var => simp
  repeat simp only [
    wk, RawUntyped.wk_coherent (RawWk.liftn_id_equiv), 
    RawUntyped.wk_coherent RawWk.lift_id_equiv,
  *]
}

def RawUntyped.wk_bounds {u: RawUntyped}: {n m: Nat} -> {ρ: RawWk} ->
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
          case left => apply IHl Hm Hl
          case right => apply IHr Hm Hr
  }

def RawUntyped.fv_wk1: fv (wk1 u) ≤ fv u + 1 
  := by apply wk_bounds wk_maps_wk1; exact Nat.le_refl _

@[simp] def RawUntyped.wk_composes {u: RawUntyped}: 
  (σ ρ: RawWk) -> (u.wk ρ).wk σ = u.wk (σ.comp ρ) 
  := by induction u <;> simp [*]

theorem RawUntyped.wk_wk1 {u: RawUntyped}: u.wk RawWk.wk1 = u.wk1 
  := rfl 

@[simp] def Untyped.wk (u: Untyped m) (ρ: Wk n m): Untyped n :=
  Untyped.mk (u.val.wk ρ.val) (RawUntyped.wk_bounds ρ.p u.p)

@[simp] def Untyped.wk_composes {u: Untyped l} {σ: Wk n m} {ρ: Wk m l}:
  (u.wk ρ).wk σ = u.wk (σ.comp ρ) := by simp
  
theorem RawUntyped.step_wk1 {u: RawUntyped}: u.wk ρ.step = (u.wk ρ).wk1 
  := by simp [<-RawWk.step_is_comp_wk1]

theorem RawUntyped.lift_wk1 {u: RawUntyped}: u.wk1.wk ρ.lift = (u.wk ρ).wk1 
  := by simp