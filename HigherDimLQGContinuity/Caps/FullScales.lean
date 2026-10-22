import HigherDimLQGContinuity.Caps.Cover
import Mathlib.Order.Interval.Finset.Floor

/-! The complete dyadic scale window. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HigherDimLQGContinuity

/-- Every dyadic scale in the exponential window `[e⁻²ⱽ,e⁻ⱽ]`. -/
def p4_fullScales (V : ℝ) : Finset ℕ :=
  Finset.Icc (Nat.ceil (V / Real.log 2)) (Nat.floor (2 * V / Real.log 2))

private theorem p4_log2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
private theorem p4_log2_le_one : Real.log (2 : ℝ) ≤ 1 := by
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- The finite interval really is the set of all dyadic radii in the window. -/
theorem p4_mem_fullScales_iff {V : ℝ} (hV : 0 ≤ V) (k : ℕ) :
    k ∈ p4_fullScales V ↔
      Real.exp (-2 * V) ≤ p4_radius k ∧ p4_radius k ≤ Real.exp (-V) := by
  have hlog := p4_log2_pos
  have hdiv : 0 ≤ 2 * V / Real.log 2 := by positivity
  have hmem : k ∈ p4_fullScales V ↔
      V / Real.log 2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * V / Real.log 2 := by
    unfold p4_fullScales
    simpa only [Finset.mem_Icc, Set.mem_Icc] using
      (Nat.cast_mem_Icc_iff (a := V / Real.log 2)
        (b := 2 * V / Real.log 2) (n := k) hdiv).symm
  rw [hmem]
  have hr : p4_radius k = Real.exp (-(k : ℝ) * Real.log 2) := by
    unfold p4_radius
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hr]
  constructor
  · rintro ⟨hklo, hkhi⟩
    constructor
    · apply Real.exp_le_exp.mpr
      have h := (le_div_iff₀ hlog).mp hkhi
      nlinarith
    · apply Real.exp_le_exp.mpr
      have h := (div_le_iff₀ hlog).mp hklo
      nlinarith
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_le_iff₀ hlog).mpr
      have h := Real.exp_le_exp.mp hhi
      nlinarith
    · apply (le_div_iff₀ hlog).mpr
      have h := Real.exp_le_exp.mp hlo
      nlinarith

/-- The full window has at least `V/log 2 - 1` distinct scales. -/
theorem p4_fullScales_card {V : ℝ} (hV : 1 ≤ V) :
    V / Real.log 2 - 1 ≤ ((p4_fullScales V).card : ℝ) := by
  let y : ℝ := V / Real.log 2
  have hlog := p4_log2_pos
  have hy : 1 ≤ y := by
    dsimp [y]
    apply (le_div_iff₀ hlog).mpr
    nlinarith [p4_log2_le_one]
  have hy0 : 0 ≤ y := by linarith
  have hceil : ((Nat.ceil y : ℕ) : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have hfloor : 2 * y < ((Nat.floor (2 * y) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hle : Nat.ceil y ≤ Nat.floor (2 * y) := by
    apply Nat.le_floor
    have : ((Nat.ceil y : ℕ) : ℝ) ≤ 2 * y := by linarith
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using this
  have hcard : (p4_fullScales V).card = Nat.floor (2 * y) + 1 - Nat.ceil y := by
    unfold p4_fullScales
    have heq : 2 * V / Real.log 2 = 2 * y := by dsimp [y]; ring
    rw [heq]
    exact Nat.card_Icc _ _
  have hsub : (((Nat.floor (2 * y) + 1 - Nat.ceil y : ℕ) : ℝ)) =
      (Nat.floor (2 * y) : ℝ) + 1 - (Nat.ceil y : ℝ) := by
    rw [Nat.cast_sub (by omega : Nat.ceil y ≤ Nat.floor (2 * y) + 1)]
    push_cast
    ring
  rw [hcard, hsub]
  linarith

end HigherDimLQGContinuity
