import HigherDimLFPPAS.Windows.Constants

/-!
# Deterministic scales and finite window selection

The quarter thresholds in the source are essential: if fewer than one quarter of a window is
in either tail, strictly more than half of its radii lie between the two thresholds.
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLFPPAS.Windows

open Finset

def winU (i : ℕ) : ℝ := (3 / 8 : ℝ) ^ i

def winV (i : ℕ) : ℝ := winU i / 2

theorem winU_pos (i : ℕ) : 0 < winU i := by
  unfold winU
  positivity

theorem winU_succ (i : ℕ) : winU (i + 1) = winU i * (3 / 8 : ℝ) := by
  simp [winU, pow_succ, mul_comm]

theorem winV_gt_nextU (i : ℕ) : winU (i + 1) < winV i := by
  rw [winU_succ]
  unfold winV
  nlinarith [winU_pos i]

theorem winU_antitone : Antitone winU := by
  intro i j hij
  induction hij with
  | refl => rfl
  | @step j hij ih =>
      rw [winU_succ]
      calc
        winU j * (3 / 8 : ℝ) ≤ winU j := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left (by norm_num : (3 / 8 : ℝ) ≤ 1) (le_of_lt (winU_pos j)))
        _ ≤ winU i := ih

/-- Every earlier output exponent is strictly above any later window's input exponent. -/
theorem winV_gt_winU_of_lt {i j : ℕ} (hij : i < j) : winV i > winU j := by
  have hle : i + 1 ≤ j := by omega
  have hmono := winU_antitone hle
  exact lt_of_le_of_lt hmono (winV_gt_nextU i)

/-- Integer lattice indices whose radii lie in the normalization window. -/
def winRadiusIndices (ε u : ℝ) : Set ℤ :=
  {k | ε ^ u ≤ (256 : ℝ) ^ (-k) ∧ (256 : ℝ) ^ (-k) ≤ ε ^ (u / 2)}

/-- Radii in the normalization window, exactly `{256^(-k) : k ∈ ℤ}` intersected with
`[ε^u, ε^(u/2)]`. -/
def winRadiusWindow (ε u : ℝ) : Set ℝ :=
  (fun k : ℤ => (256 : ℝ) ^ (-k)) '' winRadiusIndices ε u

/-- The continuous interval corresponding to the logarithmic width of one window. -/
def winIndexLower (ε u : ℝ) : ℝ := u * (-Real.log ε) / (2 * Real.log 256)

theorem winRadiusIndices_eq_Icc {ε u : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hu : 0 < u) :
    winRadiusIndices ε u = Set.Icc (⌈winIndexLower ε u⌉) (⌊2 * winIndexLower ε u⌋) := by
  ext k
  have hlog256 : 0 < Real.log (256 : ℝ) := Real.log_pos (by norm_num)
  simp only [winRadiusIndices, Set.mem_setOf_eq, Set.mem_Icc, Int.ceil_le, Int.le_floor]
  constructor
  · intro h
    have hlow := (Real.log_le_log_iff (Real.rpow_pos_of_pos hε0 u)
      (zpow_pos (show (0 : ℝ) < 256 by norm_num) (-k))).mpr h.1
    have hhigh := (Real.log_le_log_iff
      (zpow_pos (show (0 : ℝ) < 256 by norm_num) (-k))
      (Real.rpow_pos_of_pos hε0 (u / 2))).mpr h.2
    rw [Real.log_rpow hε0, Real.log_zpow] at hlow hhigh
    constructor
    · dsimp [winIndexLower]
      apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hlog256)).2
      push_cast at hhigh
      nlinarith [hhigh]
    · dsimp [winIndexLower]
      have heq : 2 * (u * (-Real.log ε) / (2 * Real.log 256)) =
          u * (-Real.log ε) / Real.log 256 := by field_simp <;> ring_nf
      rw [heq]
      apply (le_div_iff₀ hlog256).2
      push_cast at hlow
      nlinarith [hlow]
  · intro h
    constructor
    · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hε0 u)
        (zpow_pos (show (0 : ℝ) < 256 by norm_num) (-k))).mp
      rw [Real.log_rpow hε0, Real.log_zpow]
      dsimp [winIndexLower] at h
      push_cast at h
      have hk := h.2
      have hmul : (k : ℝ) * Real.log 256 ≤ u * (-Real.log ε) := by
        have hscaled : (k : ℝ) ≤ u * (-Real.log ε) / Real.log 256 := by
          have heq : 2 * (u * (-Real.log ε) / (2 * Real.log 256)) =
              u * (-Real.log ε) / Real.log 256 := by field_simp <;> ring_nf
          rw [heq] at hk
          nlinarith
        exact (le_div_iff₀ hlog256).1 hscaled
      push_cast at hk
      push_cast
      nlinarith [hmul]
    · apply (Real.log_le_log_iff
        (zpow_pos (show (0 : ℝ) < 256 by norm_num) (-k))
        (Real.rpow_pos_of_pos hε0 (u / 2))).mp
      rw [Real.log_zpow, Real.log_rpow hε0]
      dsimp [winIndexLower] at h
      have hk := h.1
      have hmul : u * (-Real.log ε) / 2 ≤ (k : ℝ) * Real.log 256 := by
        calc
          u * (-Real.log ε) / 2 =
              (u * (-Real.log ε) / (2 * Real.log 256)) * Real.log 256 := by
                field_simp <;> ring_nf
          _ ≤ (k : ℝ) * Real.log 256 :=
            mul_le_mul_of_nonneg_right hk hlog256.le
      push_cast at hk
      push_cast
      nlinarith [hmul]

/-- For sufficiently wide logarithmic windows, the lattice count is at least one eighth of
the logarithmic width. In the paper's variables this is `u log(ε⁻¹)/(16 log 256)`. -/
theorem winRadiusWindow_count_of_large {ε u : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hu : 0 < u) (hA : 2 ≤ winIndexLower ε u) :
    (winRadiusWindow ε u).ncard ≥ (winIndexLower ε u / 8) := by
  have hlog256 : 0 < Real.log (256 : ℝ) := Real.log_pos (by norm_num)
  have hinj : Function.Injective (fun k : ℤ => (256 : ℝ) ^ (-k)) := by
    intro k l hkl
    have hlogs := congrArg Real.log hkl
    rw [Real.log_zpow, Real.log_zpow] at hlogs
    have hcast : (k : ℝ) = l := by
      apply (mul_right_cancel₀ hlog256.ne')
      simpa using hlogs
    exact Int.cast_injective hcast
  have hceil : (winIndexLower ε u : ℝ) ≤ (⌈winIndexLower ε u⌉ : ℤ) := by
    exact_mod_cast Int.le_ceil _
  have hceil_lt : (⌈winIndexLower ε u⌉ : ℝ) < winIndexLower ε u + 1 :=
    Int.ceil_lt_add_one _
  have hfloor : 2 * winIndexLower ε u - 1 < (⌊2 * winIndexLower ε u⌋ : ℤ) :=
    Int.sub_one_lt_floor _
  have hfloor_le : (⌈winIndexLower ε u⌉ : ℤ) ≤ (⌊2 * winIndexLower ε u⌋ : ℤ) + 1 := by
    calc
      (⌈winIndexLower ε u⌉ : ℤ) ≤ (⌊winIndexLower ε u⌋ : ℤ) + 1 :=
        Int.ceil_le_floor_add_one _
      _ ≤ (⌊2 * winIndexLower ε u⌋ : ℤ) + 1 := by
        exact Int.add_le_add_right (Int.floor_mono (by linarith [hA])) 1
  have hcardInt : ((Finset.Icc (⌈winIndexLower ε u⌉) (⌊2 * winIndexLower ε u⌋)).card : ℤ) =
      (⌊2 * winIndexLower ε u⌋ : ℤ) + 1 - (⌈winIndexLower ε u⌉ : ℤ) :=
    Int.card_Icc_of_le _ _ hfloor_le
  have hcardReal : ((winRadiusWindow ε u).ncard : ℝ) =
      (⌊2 * winIndexLower ε u⌋ : ℝ) + 1 - (⌈winIndexLower ε u⌉ : ℝ) := by
    rw [winRadiusWindow, winRadiusIndices_eq_Icc hε0 hε1 hu,
      Set.ncard_image_of_injective _ hinj, Set.ncard_Icc]
    exact_mod_cast hcardInt
  have hcount : winIndexLower ε u - 1 < (winRadiusWindow ε u).ncard := by
    rw [hcardReal]
    have hfloor' : 2 * winIndexLower ε u - 1 < (⌊2 * winIndexLower ε u⌋ : ℝ) := by
      exact_mod_cast hfloor
    have hceil' : (⌈winIndexLower ε u⌉ : ℝ) < winIndexLower ε u + 1 := hceil_lt
    linarith
  have htarget : winIndexLower ε u / 8 ≤ winIndexLower ε u - 1 := by linarith
  exact le_of_lt (lt_of_le_of_lt htarget hcount)

/-- Explicit small-cutoff form of the window lattice count. -/
theorem winRadiusWindow_count {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (winRadiusWindow ε u).ncard ≥
        u * Real.log (ε⁻¹) / (16 * Real.log 256) := by
  let ε₀ := Real.exp (-(4 * Real.log 256 / u))
  have hlog256 : 0 < Real.log (256 : ℝ) := Real.log_pos (by norm_num)
  have hε₀pos : 0 < ε₀ := Real.exp_pos _
  have hε₀lt : ε₀ < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have : 0 < 4 * Real.log 256 / u := div_pos (by positivity) hu
    linarith
  refine ⟨ε₀, hε₀pos, hε₀lt, ?_⟩
  intro ε hε0 hεlt
  have hε1 : ε < 1 := lt_trans hεlt hε₀lt
  have hloglt : Real.log ε < -(4 * Real.log 256 / u) := by
    calc
      Real.log ε < Real.log ε₀ := Real.log_lt_log hε0 hεlt
      _ = -(4 * Real.log 256 / u) := by simp [ε₀]
  have hlarge : 2 ≤ winIndexLower ε u := by
    unfold winIndexLower
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log 256)).2
    have hmul : 4 * Real.log 256 < u * (-Real.log ε) := by
      have h := mul_lt_mul_of_pos_left hloglt hu
      have hcancel : u * (4 * Real.log 256 / u) = 4 * Real.log 256 := by
        field_simp <;> ring
      nlinarith [h, hcancel]
    nlinarith
  have hcount := winRadiusWindow_count_of_large hε0 hε1 hu hlarge
  have htarget : winIndexLower ε u / 8 = u * Real.log (ε⁻¹) / (16 * Real.log 256) := by
    unfold winIndexLower
    rw [Real.log_inv]
    ring
  rw [← htarget]
  exact hcount

/-- Earlier windows have strictly smaller radii than later windows. -/
theorem winRadiusWindow_order {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {i j : ℕ} (hij : i < j) {r s : ℝ}
    (hr : r ∈ winRadiusWindow ε (winU i))
    (hs : s ∈ winRadiusWindow ε (winU j)) : r < s := by
  rcases (Set.mem_image _ _ _).1 hr with ⟨k, hk, heq⟩
  rcases (Set.mem_image _ _ _).1 hs with ⟨l, hl, heq'⟩
  subst r
  subst s
  have hrupper := hk.2
  have hslower := hl.1
  have hexp : winU j < winU i / 2 := winV_gt_winU_of_lt hij
  have hp : ε ^ (winU i / 2) < ε ^ winU j := by
    rw [Real.rpow_lt_rpow_left_iff_of_base_lt_one hε0 hε1]
    exact hexp
  exact lt_of_le_of_lt hrupper (lt_of_lt_of_le hp hslower)

/-- Distinct normalization windows are disjoint. -/
theorem winRadiusWindow_disjoint {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (winRadiusWindow ε (winU i)) (winRadiusWindow ε (winU j)) := by
  classical
  rw [Set.disjoint_left]
  intro r hri hrj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (lt_irrefl r (winRadiusWindow_order hε0 hε1 h hri hrj))
  · exact (lt_irrefl r (winRadiusWindow_order hε0 hε1 h hrj hri))

/-- For a fixed window, the small-ratio tail. -/
def winLowRadii {α : Type*} [DecidableEq α] (s : Finset α) (c : α → ℝ) (m : ℝ) : Finset α :=
  s.filter (fun x => c x ≤ m)

/-- For a fixed window, the large-ratio tail. -/
def winHighRadii {α : Type*} [DecidableEq α] (s : Finset α) (c : α → ℝ) (m : ℝ) : Finset α :=
  s.filter (fun x => m ≤ c x)

/-- A window is low when at least one quarter of its radii are in the low tail. -/
def winIsLow {α : Type*} [DecidableEq α] (s : Finset α) (c : α → ℝ) (m : ℝ) : Prop :=
  s.card ≤ 4 * (winLowRadii s c m).card

/-- A window is high when at least one quarter of its radii are in the high tail. -/
def winIsHigh {α : Type*} [DecidableEq α] (s : Finset α) (c : α → ℝ) (m : ℝ) : Prop :=
  s.card ≤ 4 * (winHighRadii s c m).card

/-- Radii strictly between the lower and upper normalization thresholds. -/
def winMiddleRadii {α : Type*} [DecidableEq α]
    (s : Finset α) (c : α → ℝ) (mLo mHi : ℝ) : Finset α :=
  s.filter (fun x => mLo < c x ∧ c x < mHi)

theorem winMiddle_more_than_half {α : Type*} [DecidableEq α]
    (s : Finset α) (c : α → ℝ) {mLo mHi : ℝ} (hm : mLo < mHi)
    (hlo : 4 * (winLowRadii s c mLo).card < s.card)
    (hhi : 4 * (winHighRadii s c mHi).card < s.card) :
    2 * (winMiddleRadii s c mLo mHi).card > s.card := by
  classical
  let tail : α → Prop := fun x => c x ≤ mLo ∨ mHi ≤ c x
  have hmid : winMiddleRadii s c mLo mHi = s.filter (fun x => ¬ tail x) := by
    ext x
    simp only [winMiddleRadii, mem_filter]
    constructor
    · rintro ⟨hx, h₁, h₂⟩
      exact ⟨hx, not_or.mpr ⟨not_le_of_gt h₁, not_le_of_gt h₂⟩⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, lt_of_not_ge (fun hle => h (Or.inl hle)),
        lt_of_not_ge (fun hge => h (Or.inr hge))⟩
  have htail : (s.filter tail).card ≤ (winLowRadii s c mLo).card +
      (winHighRadii s c mHi).card := by
    calc
      _ ≤ (winLowRadii s c mLo ∪ winHighRadii s c mHi).card := Finset.card_le_card (by
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hx, h⟩
        rcases h with hlo | hhi
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx, hlo⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, hhi⟩)))
      _ ≤ (winLowRadii s c mLo).card + (winHighRadii s c mHi).card := Finset.card_union_le _ _
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) tail
  rw [← hmid] at hsplit
  omega

/-- A window is neither low nor high when both tails contain strictly fewer than one quarter
of its radii; consequently it has a strict majority in the middle interval. -/
theorem winNeither_middle_majority {α : Type*} [DecidableEq α]
    (s : Finset α) (c : α → ℝ) {mLo mHi : ℝ} (hm : mLo < mHi)
    (hlo : ¬ winIsLow s c mLo) (hhi : ¬ winIsHigh s c mHi) :
    2 * (winMiddleRadii s c mLo mHi).card > s.card := by
  apply winMiddle_more_than_half s c hm
  · simpa [winIsLow] using Nat.lt_of_not_ge hlo
  · simpa [winIsHigh] using Nat.lt_of_not_ge hhi

/-- If fewer than `N` of `3N` windows are low and fewer than `N` are high, at least `N`
windows are neither. -/
theorem winNeither_card {α : Type*} [DecidableEq α]
    (s : Finset α) (N : ℕ) (isLow isHigh : α → Prop)
    [DecidablePred isLow] [DecidablePred isHigh]
    (hcard : s.card = 3 * N)
    (hLow : (s.filter isLow).card < N) (hHigh : (s.filter isHigh).card < N) :
    N ≤ (s.filter (fun x => ¬ isLow x ∧ ¬ isHigh x)).card := by
  classical
  have hUnion : (s.filter (fun x => isLow x ∨ isHigh x)).card ≤
      (s.filter isLow).card + (s.filter isHigh).card := by
    calc
      _ ≤ (s.filter isLow ∪ s.filter isHigh).card := Finset.card_le_card (by
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hx, h⟩
        rcases h with h | h
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx, h⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, h⟩)))
      _ ≤ (s.filter isLow).card + (s.filter isHigh).card := Finset.card_union_le _ _
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun x => isLow x ∨ isHigh x)
  have hnotEq : (s.filter (fun x => ¬ isLow x ∧ ¬ isHigh x)).card =
      (s.filter (fun x => ¬ (isLow x ∨ isHigh x))).card := by
    congr 1
    ext x
    simp only [not_or]
  have hnot := hsplit
  rw [hnotEq]
  omega

end HigherDimLFPPAS.Windows
