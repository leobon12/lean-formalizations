import Mathlib

/-!
# Explicit constants and recursion for Proposition 5.1

This file records the corrected constants from the MA2 audit and proves the elementary
real arithmetic used in the iteration.
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLFPPAS.Windows

open Filter Topology

/-- The scale parameters in Proposition 5.1. -/
def winT (δ : ℝ) : ℝ := δ / 4

def winEta (δ θ : ℝ) : ℝ := (1 - θ) * δ / 30

def winMMinus (δ : ℝ) : ℝ := 1 - winT δ

def winMPlus (δ : ℝ) : ℝ := (1 - winT δ)⁻¹

theorem winT_pos {δ : ℝ} (hδ : 0 < δ) : 0 < winT δ := by
  simp [winT, hδ]

theorem winT_lt_quarter {δ : ℝ} (hδ : δ < 1) : winT δ < 1 / 4 := by
  dsimp [winT]
  linarith

theorem winEta_pos {δ θ : ℝ} (hδ : 0 < δ) (hθ : θ < 1) : 0 < winEta δ θ := by
  unfold winEta
  positivity

theorem winMPlus_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : 0 < winMPlus δ := by
  unfold winMPlus winT
  exact inv_pos.2 (by linarith)

theorem winMPlus_lt_four_thirds {δ : ℝ} (hδ : δ < 1) : winMPlus δ < 4 / 3 := by
  unfold winMPlus winT
  have hden : 3 / 4 < 1 - δ / 4 := by linarith
  have hdenpos : 0 < 1 - δ / 4 := by linarith
  have := (inv_lt_inv₀ hdenpos (by norm_num : (0 : ℝ) < 3 / 4)).2 hden
  simpa using this

/-- The least positive number of iterations making the initial error smaller than `δ/16`. -/
theorem winIterations_exists {δ θ C₀ : ℝ} (hδ : 0 < δ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) : ∃ N : ℕ, 1 ≤ N ∧ θ ^ N * C₀ < δ / 16 ∧
      ∀ n : ℕ, 1 ≤ n → n < N → ¬ θ ^ n * C₀ < δ / 16 := by
  let p : ℕ → Prop := fun n => 1 ≤ n ∧ θ ^ n * C₀ < δ / 16
  have hex : ∃ n, p n := by
    have habs : |θ| < 1 := by rw [abs_of_pos hθ0]; exact hθ1
    have hpow : Tendsto (fun n : ℕ => θ ^ n * C₀) atTop (𝓝 0) := by
      simpa [mul_comm] using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs).const_mul C₀
    have hev := hpow.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 16))
    obtain ⟨n₀, hn₀⟩ := (eventually_atTop.1 hev)
    refine ⟨max n₀ 1, ?_, ?_⟩
    · exact le_max_right _ _
    · exact hn₀ _ (le_max_left _ _)
  let N := Nat.find hex
  have hspec := Nat.find_spec hex
  refine ⟨N, hspec.1, hspec.2, ?_⟩
  intro n hn₁ hnlt hsmall
  have hmin := Nat.find_min hex hnlt
  exact hmin (And.intro hn₁ hsmall)

/-- One application of the affine improvement map. -/
def winStep (θ η m C : ℝ) : ℝ := θ * C + (1 - θ + 3 * η) * m

/-- The `n`th iterate of the affine improvement map. -/
def winIter (θ η m C : ℝ) (n : ℕ) : ℝ :=
  Nat.rec C (fun _ c => winStep θ η m c) n

theorem winStep_monotone {θ η m : ℝ} (hθ : 0 ≤ θ) : Monotone (winStep θ η m) := by
  intro a b hab
  unfold winStep
  nlinarith

theorem winIter_closed {θ η m C : ℝ} (hθ : θ ≠ 1) (n : ℕ) :
    winIter θ η m C n = θ ^ n * C +
      m * (1 + 3 * η / (1 - θ)) * (1 - θ ^ n) := by
  induction n with
  | zero => simp [winIter]
  | succ n ih =>
      change winStep θ η m (winIter θ η m C n) = _
      rw [ih]
      unfold winStep
      field_simp
      <;> ring

theorem winIter_mono {θ η m C D : ℝ} (hθ : 0 ≤ θ) (n : ℕ) (hCD : C ≤ D) :
    winIter θ η m C n ≤ winIter θ η m D n := by
  induction n with
  | zero => simpa [winIter] using hCD
  | succ n ih =>
      change winStep θ η m (winIter θ η m C n) ≤ winStep θ η m (winIter θ η m D n)
      exact winStep_monotone hθ ih

theorem winStep_ge_of_ge {θ η m C : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hm : 0 ≤ m) (hCm : m ≤ C) : m ≤ winStep θ η m C := by
  unfold winStep
  have hprod : 0 ≤ θ * (C - m) := mul_nonneg hθ (sub_nonneg.mpr hCm)
  nlinarith

theorem winIter_ge {θ η m C : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hm : 0 ≤ m) (hCm : m ≤ C) (n : ℕ) : m ≤ winIter θ η m C n := by
  induction n with
  | zero => simpa [winIter] using hCm
  | succ n ih =>
      change m ≤ winStep θ η m (winIter θ η m C n)
      exact winStep_ge_of_ge hθ hη hm ih

theorem win_fixed_factor (δ θ : ℝ) (hθ : θ ≠ 1) :
    1 + 3 * winEta δ θ / (1 - θ) = 1 + δ / 10 := by
  unfold winEta
  field_simp
  <;> ring

theorem win_mplus_fixed_lt {δ θ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hθ : θ < 1) : winMPlus δ * (1 + δ / 10) < 1 + δ / 2 := by
  unfold winMPlus winT
  have hden : 0 < 1 - δ / 4 := by linarith
  have hdiv : (1 + δ / 10) / (1 - δ / 4) < 1 + δ / 2 := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  simpa [div_eq_mul_inv, mul_comm] using hdiv

theorem win_mminus_fixed_lt {δ θ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hθ : θ < 1) : winMMinus δ * (1 + δ / 10) < 1 - winT δ / 2 := by
  unfold winMMinus winT
  nlinarith

theorem win_lambda_minus_lt {δ θ C₀ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₀ : 2 ≤ C₀) (N : ℕ)
    (hN : θ ^ N * C₀ < δ / 16) :
    winIter θ (winEta δ θ) (winMMinus δ) C₀ N < 1 - winT δ / 4 := by
  rw [winIter_closed (by linarith : θ ≠ 1)]
  rw [win_fixed_factor δ θ (by linarith : θ ≠ 1)]
  have hfac := win_mminus_fixed_lt hδ hδ1 hθ1
  have hNpos : 0 ≤ θ ^ N := pow_nonneg (le_of_lt hθ0) N
  unfold winMMinus winT at hfac ⊢
  nlinarith

theorem win_lambda_plus_lt {δ θ C₀ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC₀ : 2 ≤ C₀) (N : ℕ)
    (hN : θ ^ N * C₀ < δ / 16) :
    winIter θ (winEta δ θ) (winMPlus δ) C₀ N < 1 + δ := by
  rw [winIter_closed (by linarith : θ ≠ 1)]
  rw [win_fixed_factor δ θ (by linarith : θ ≠ 1)]
  have hfac := win_mplus_fixed_lt hδ hδ1 hθ1
  have hNpos : 0 ≤ θ ^ N := pow_nonneg (le_of_lt hθ0) N
  unfold winMPlus winT at hfac ⊢
  nlinarith

end HigherDimLFPPAS.Windows
