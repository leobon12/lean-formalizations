import Mathlib

set_option autoImplicit false
noncomputable section
open Filter Topology Set
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small

/-- The sequential compactness reduction in the last two lines of
Proposition 4.3. The values can be failure probabilities. -/
theorem uniform_small_scale_of_sequential
    (K : Set ℂ) (hK : IsCompact K)
    (F : ℂ → ℝ → ℝ≥0∞)
    (hseq : ∀ (r : ℕ → ℝ) (z : ℕ → ℂ) (zlim : ℂ),
      (∀ n, 0 < r n) → Tendsto r atTop (𝓝 0) →
      (∀ n, z n ∈ K) → Tendsto z atTop (𝓝 zlim) →
      Tendsto (fun n => F (z n) (r n)) atTop (𝓝 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ z ∈ K, ∀ r : ℝ, 0 < r → r < δ → F z r < ε := by
  intro ε hε
  by_contra h
  push Not at h
  have hchoose : ∀ n : ℕ, ∃ z : ℂ, ∃ r : ℝ,
      z ∈ K ∧ 0 < r ∧ r < (1 : ℝ) / (n + 1) ∧ ε ≤ F z r := by
    intro n
    obtain ⟨z, hz, r, hr, hrsmall, hF⟩ :=
      h ((1 : ℝ) / (n + 1)) (by positivity)
    exact ⟨z, r, hz, hr, hrsmall, hF⟩
  choose z r hz hr hrsmall hF using hchoose
  obtain ⟨zlim, -, ψ, hψ, hzconv⟩ := hK.tendsto_subseq hz
  have hrtend : Tendsto r atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      (Eventually.of_forall fun n => (hr n).le)
      (Eventually.of_forall fun n => (hrsmall n).le)
  have hzero := hseq (r ∘ ψ) (z ∘ ψ) zlim
    (fun n => hr (ψ n))
    (hrtend.comp hψ.tendsto_atTop)
    (fun n => hz (ψ n)) hzconv
  have hlimit : ε ≤ (0 : ℝ≥0∞) :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hzero
      (fun n => hF (ψ n))
  exact (not_le_of_gt hε) hlimit


end SupercriticalConformalCovariance.Small
