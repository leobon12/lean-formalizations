import HigherDimLQGMetric.Sharp.W2Gaussian
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Power choice for superpolynomial upper tails. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Filter
open scoped Topology

/-- Choose a Gaussian cutoff whose grid tail beats the metric coefficient. -/
theorem w2_choose_gaussian_exponent (d : ℕ) {ξ p : ℝ} (hξ : 0 < ξ) (hp : 0 < p) :
    ∃ M : ℝ, 0 < M ∧
      2 * (2 + ξ * Real.sqrt M) * p ≤ M / 8 - (3 * d + 2) := by
  let T : ℝ := 32 * (p * ξ + p + 3 * d + 4)
  have hdim : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hT : 32 ≤ T := by dsimp [T]; nlinarith only [mul_pos hp hξ, hp, hdim]
  have hT0 : 0 < T := by linarith only [hT]
  have hpxi : p * ξ ≤ T / 32 := by dsimp [T]; nlinarith only [hp, hdim]
  have hpT : p ≤ T / 32 := by dsimp [T]; nlinarith only [mul_pos hp hξ, hdim]
  have hdT : 3 * (d : ℝ) + 2 ≤ T / 32 := by
    dsimp [T]; nlinarith only [mul_pos hp hξ, hp, hdim]
  have hpxiT := mul_le_mul_of_nonneg_right hpxi hT0.le
  have hTsq := mul_le_mul_of_nonneg_right hT hT0.le
  refine ⟨T ^ 2, sq_pos_of_pos hT0, ?_⟩
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hT0]
  nlinarith only [hpxiT, hTsq, hpT, hdT]

/-- For large `A`, a single epsilon makes both the deterministic coefficient and
the bad-event probability bounded by the desired powers of `A`. -/
theorem w2_power_choice {a b p B ε₀ : ℝ} (ha : 0 < a)
    (hb : 2 * a * p ≤ b) (hB : 1 ≤ B) (hε₀ : 0 < ε₀) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      let ε := A ^ (-(1 / (2 * a)))
      ε ∈ Set.Ioo 0 ε₀ ∧ B * ε ^ (-a) ≤ A ∧ ε ^ b ≤ A ^ (-p) := by
  have htwoa : 0 < 2 * a := by positivity
  have htend : Tendsto (fun A : ℝ => A ^ (-(1 / (2 * a)))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (div_pos one_pos htwoa)
  obtain ⟨Aε, hAε⟩ := Filter.eventually_atTop.1
    (htend.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Set.Iio ε₀ from hε₀)))
  let A₀ : ℝ := max 1 (max (B ^ 2) Aε)
  have hA₀ : 1 ≤ A₀ := le_max_left _ _
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := hA₀.trans hA
  have hA0 : 0 < A := by linarith only [hA1]
  have hAB : B ^ 2 ≤ A := (le_max_left _ _).trans ((le_max_right _ _).trans hA)
  have hAe : Aε ≤ A := (le_max_right _ _).trans ((le_max_right _ _).trans hA)
  let ε : ℝ := A ^ (-(1 / (2 * a)))
  have hε : 0 < ε := Real.rpow_pos_of_pos hA0 _
  have hε₀' : ε < ε₀ := hAε A hAe
  have hpow : ε ^ (-a) = A ^ (1 / 2 : ℝ) := by
    dsimp [ε]
    rw [← Real.rpow_mul hA0.le]
    congr 1
    field_simp
  have hBroot : B ≤ A ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    calc
      B = Real.sqrt (B ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith only [hB])]
      _ ≤ Real.sqrt A := Real.sqrt_le_sqrt hAB
  have hBA : B * ε ^ (-a) ≤ A := by
    rw [hpow, ← Real.sqrt_eq_rpow]
    calc
      B * Real.sqrt A ≤ Real.sqrt A * Real.sqrt A :=
        mul_le_mul_of_nonneg_right (by simpa only [Real.sqrt_eq_rpow] using hBroot)
          (Real.sqrt_nonneg _)
      _ = A := Real.mul_self_sqrt hA0.le
  have hexp : -(1 / (2 * a)) * b ≤ -p := by
    have hdiv : p ≤ b / (2 * a) :=
      (le_div_iff₀ htwoa).2 (by nlinarith only [hb])
    have hneg := neg_le_neg hdiv
    have heq : -(1 / (2 * a)) * b = -(b / (2 * a)) := by ring
    rw [heq]
    exact hneg
  have htail : ε ^ b ≤ A ^ (-p) := by
    dsimp [ε]
    rw [← Real.rpow_mul hA0.le]
    exact Real.rpow_le_rpow_of_exponent_le hA1 hexp
  exact ⟨⟨hε, hε₀'⟩, hBA, htail⟩

/-- Absorb the number of chain spheres into the same epsilon power as the
Gaussian fluctuation. -/
theorem w2_chain_coefficient {Λ C 𝕣 ε u S : ℝ}
    (_hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (h𝕣 : 0 < 𝕣)
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hS : 0 ≤ S) :
    (2 * (𝕣 * Λ) / (ε ^ 2 * 𝕣) + 2) * (C * S * ε ^ (-u)) ≤
      ((2 * Λ + 2) * C * ε ^ (-(2 + u))) * S := by
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := hε.2
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε0
  have hε2one : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1.le
  have hcoef : 2 * (𝕣 * Λ) / (ε ^ 2 * 𝕣) + 2 ≤
      (2 * Λ + 2) * (ε ^ 2)⁻¹ := by
    have he : 2 * (𝕣 * Λ) / (ε ^ 2 * 𝕣) = 2 * Λ / ε ^ 2 := by
      field_simp
    rw [he]
    have hrec : 1 ≤ (ε ^ 2)⁻¹ := one_le_inv_iff₀.mpr ⟨hε2, hε2one⟩
    rw [div_eq_mul_inv]
    nlinarith only [hrec, _hΛ]
  have hpow : ε ^ (-(2 + u)) = (ε ^ 2)⁻¹ * ε ^ (-u) := by
    rw [show -(2 + u) = (-2 : ℝ) + (-u) by ring, Real.rpow_add hε0,
      Real.rpow_neg hε0.le]
    norm_num [Real.rpow_natCast]
  rw [hpow]
  have hpos : 0 ≤ C * S * ε ^ (-u) := by positivity
  calc
    (2 * (𝕣 * Λ) / (ε ^ 2 * 𝕣) + 2) * (C * S * ε ^ (-u)) ≤
        ((2 * Λ + 2) * (ε ^ 2)⁻¹) * (C * S * ε ^ (-u)) :=
      mul_le_mul_of_nonneg_right hcoef hpos
    _ = ((2 * Λ + 2) * C * ((ε ^ 2)⁻¹ * ε ^ (-u))) * S := by ring

end HigherDimLQGMetric
