import LogicalRefinement.Utils
import LogicalRefinement.Wk
import LogicalRefinement.Untyped.Basic

@[simp] def Term.wk: Term -> Wk -> Term
  | var v, ρ => var (Wk.var ρ v)
  | const c, _ => const c
  | unary k t, ρ => unary k (t.wk ρ)
  | let_bin k P e e', ρ => let_bin k (P.wk ρ) (e.wk ρ) (e'.wk (ρ.liftn 2))
  | let_bin_beta k P l r e', ρ => let_bin_beta k (P.wk ρ) (l.wk ρ) (r.wk ρ) (e'.wk (ρ.liftn 2))
  | bin k l r, ρ => bin k (l.wk ρ) (r.wk ρ)
  | abs k A t, ρ => abs k (A.wk ρ) (t.wk ρ.lift)
  | tri k A l r, ρ => tri k (A.wk ρ) (l.wk ρ) (r.wk ρ)
  | cases k K d l r, ρ => 
    cases k (K.wk ρ) (d.wk ρ) (l.wk ρ.lift) (r.wk ρ.lift)
  | ir k x y P, ρ =>
    ir k (x.wk ρ) (y.wk ρ) (P.wk ρ.lift)
  | nr k K e z s, ρ =>
    nr k (K.wk ρ.lift) (e.wk ρ) (z.wk ρ) (s.wk (ρ.liftn 2))
  | nz k K z s, ρ =>
    nz k (K.wk ρ.lift) (z.wk ρ) (s.wk (ρ.liftn 2))

@[simp] def Term.wk1 (u: Term) 
  := u.wk Wk.wk1

-- wk1 based type formers
abbrev Term.arrow (A B: Term) := pi A (wk1 B)
abbrev Term.implies (φ ψ: Term) := dimplies φ ψ.wk1
abbrev Term.and (φ ψ: Term) := dand φ ψ.wk1
abbrev Term.const_arrow (A B: Term) := intersect A (wk1 B)
abbrev Term.assume_wf (φ A: Term) := assume φ (A.wk1)

abbrev Term.succ_nat (n: Term): Term := 
  Term.app (Term.arrow Term.nats Term.nats) Term.succ n

def Term.wk1_def {u: Term}: u.wk1 = u.wk Wk.wk1 := rfl

@[simp] def Term.lift1 (u: Term) := u.wk (Wk.lift Wk.id)

@[simp] def Term.wkn (u: Term) (n: Nat) 
  := u.wk (Wk.wkn n)

@[simp] def Term.wknth (u: Term) (n: Nat) 
  := u.wk (Wk.wknth n)

def Term.wknth_def {u: Term} {n}: u.wknth n = u.wk (Wk.wknth n) := rfl

@[simp] def Term.wk_coherent: {u: Term} -> {ρ σ: Wk} ->
  Wk.equiv ρ σ -> u.wk ρ = u.wk σ := by {
  intro u;
  induction u with
  | var v => intros ρ σ H; simp only [wk]; rw [H]
  | const c => simp
  | unary k t I => intros ρ σ H; simp [I H]
  | let_bin k P e e' IP Ie Ie' => 
    intros ρ σ H;
    simp only [wk];
    simp only [IP H, Ie H, Ie' (Wk.liftn_equiv H)]
  | let_bin_beta k P l r e' IP Il Ir Ie' => 
    intros ρ σ H;
    simp only [wk];
    simp only [IP H, Il H, Ir H, Ie' (Wk.liftn_equiv H)]
  | bin k l r Il Ir => intros ρ σ H; simp [Il H, Ir H]
  | abs k A s IHA IHs =>
    intros ρ σ H;
    simp only [wk];
    simp only [IHA H, IHs (Wk.lift_equiv H)]
  | tri k A l r IA Il Ir => intros ρ σ H; simp [IA H, Il H, Ir H]
  | ir k x y P Ix Iy IP => 
    intros ρ σ H;
    simp only [
      wk, Ix H, Iy H, IP (Wk.lift_equiv H)
    ]
  | cases k K d l r IK Id Il Ir => 
    intros ρ σ H;
    simp only [
      wk, IK H, Id H, Il (Wk.lift_equiv H), Ir (Wk.lift_equiv H)
    ]
  | nr k K e z s IK Ie Iz Is =>
    intros ρ σ H; 
    simp only [wk];
    simp only [
      Is (Wk.liftn_equiv H), IK (Wk.lift_equiv H), Ie H, Iz H
    ]
  | nz k K z s IK Iz Is =>
    intros ρ σ H; 
    simp only [wk];
    simp only [
      Is (Wk.liftn_equiv H), IK (Wk.lift_equiv H), Iz H
    ]
}

@[simp] def Term.wk_id {u: Term}: u.wk (Wk.id) = u := by {
  induction u;
  case var => simp
  repeat simp only [
    wk, Term.wk_coherent (Wk.liftn_id_equiv), 
    Term.wk_coherent Wk.lift_id_equiv,
  *]
}

def Term.wk_bounds {u: Term}: {n m: Nat} -> {ρ: Wk} ->
  ρ.maps n m -> fv u ≤ m -> fv (u.wk ρ) ≤ n := by {
    induction u with
    | var v => intros _ _ _ Hm. apply Hm
    | const => intros. apply Nat.zero_le
    | unary _ _ IHt => 
      intros _ _ ρ Hm
      apply IHt Hm
    | let_bin k P e e' IHP IHe IHe' =>
      simp only [fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
      intros n m ρ Hm
      intro ⟨HP, He, He'⟩
      apply And.intro
      apply IHP Hm HP
      apply And.intro
      apply IHe Hm He
      apply IHe'
      apply Wk.liftn_maps
      apply Hm
      apply He'
    | let_bin_beta k P l r e' IHP IHl IHr IHe' =>
      simp only [fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
      intros n m ρ Hm
      intro ⟨HP, Hl, Hr, He'⟩
      apply And.intro
      apply IHP Hm HP
      apply And.intro
      apply IHl Hm Hl
      apply And.intro
      apply IHr Hm Hr
      apply IHe'
      apply Wk.liftn_maps
      apply Hm
      apply He'
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
      case abs.left => exact IHA Hm HA
      case abs.right => 
        exact IHs (Wk.lift_maps Hm) Hs
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
    | ir k x y P Ix Iy IP => 
      simp only [fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
      intros n m ρ Hm
      intro ⟨Hx, Hy, HP⟩
      apply And.intro;
      case left => exact Ix Hm Hx
      case right => 
        apply And.intro;
        case left => exact Iy Hm Hy
        case right => apply IP (@Wk.liftn_maps ρ 1 n m Hm) HP
    | cases k K d l r IK IHd IHl IHr => 
      simp only [fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
      intros n m ρ Hm
      intro ⟨HK, Hd, Hl, Hr⟩
      apply And.intro;
      case cases.left => exact IK Hm HK
      case cases.right => 
        apply And.intro;
        case left => exact IHd Hm Hd
        case right =>
          apply And.intro;
          case left => apply IHl (@Wk.liftn_maps ρ 1 n m Hm) Hl
          case right => apply IHr (@Wk.liftn_maps ρ 1 n m Hm) Hr
    | nr k K e z s IK Ie Iz Is =>
      simp only [fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
      intros n m ρ Hm
      intro ⟨HK, He, Hz, Hs⟩
      apply And.intro;
      case left => apply IK (Wk.liftn_maps Hm) HK
      case right => 
        apply And.intro;
        case left => apply Ie Hm He
        case right =>
          apply And.intro;
          case left => apply Iz Hm Hz
          case right => apply Is (@Wk.liftn_maps ρ 2 n m Hm) Hs
    | nz k K z s IK Iz Is =>
      simp only [fv, Nat.max_r_le_split, Nat.le_sub_is_le_add]
      intros n m ρ Hm
      intro ⟨HK, Hz, Hs⟩
      apply And.intro;
      case left => apply IK (Wk.liftn_maps Hm) HK
      case right => 
        apply And.intro;
        case left => apply Iz Hm Hz
        case right => apply Is (@Wk.liftn_maps ρ 2 n m Hm) Hs
  }

def Term.fv_wk1: fv (wk1 u) ≤ fv u + 1 
  := by apply wk_bounds Wk.wk1_maps; exact Nat.le_refl _

@[simp] def Term.wk_composes {u: Term}: 
  (σ ρ: Wk) -> (u.wk ρ).wk σ = u.wk (σ.comp ρ) 
  := by induction u <;> simp [*]

theorem Term.wk_wk1 {u: Term}: u.wk Wk.wk1 = u.wk1 
  := rfl
  
theorem Term.step_wk1 {u: Term}: u.wk ρ.step = (u.wk ρ).wk1 
  := by simp [<-Wk.step_is_comp_wk1]

theorem Term.lift_wk1 {u: Term}: u.wk1.wk ρ.lift = (u.wk ρ).wk1 
  := by simp

theorem Term.wkn_wk1 {u: Term}: u.wkn (Nat.succ n) = (u.wkn n).wk1 := by {
  simp only [wkn, wk1, wk_composes, Wk.wkn, Wk.step_is_comp_wk1]
}