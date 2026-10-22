import HigherDimLQGContinuity.MomentsW1.BadScaleIndep

/-! # Peierls estimate for the three fine-field failures -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLQGMetric.DGZ

/-- The closed-site Peierls bound on the enlarged finite region. -/
theorem wnGood_smallClusters_prob {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (ξ : ℝ) {R : ℝ} (hR : 1 ≤ R) {q : ℝ≥0∞}
    (hq0 : 0 < q) (hq1 : q < 1) {k n : ℕ} (hkn : k ≤ n)
    {θ : ℝ≥0∞} (hθ1 : θ ≤ 1)
    (hεθ : 2 * (d : ℝ≥0∞) * (1 - q) ≤
      θ ^ ((⌈2 * (2 + ρ)⌉₊ + 1) ^ d))
    (h3 : (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹) (D : ℕ) :
    ∃ N : ℕ,
      P {ω | ¬ SmallClusters (wnGood P H ξ R q k n ω) D} ≤
        (2 * (N : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ (D / 2) ∧
      (∀ x ∈ wnRegion (d := d) R k, WithinInf (N : ℤ) x 0) ∧
      (N : ℝ) ≤ (R + 4) * (2 : ℝ) ^ k := by
  obtain ⟨N, hN, hNle⟩ := wnRegion_bounded_le (d := d) hR k
  refine ⟨N, ?_, hN, hNle⟩
  change P {ω | ¬ SmallClusters {x | ω ∉ wnClosed P H ξ R q k n x} D} ≤ _
  apply measure_not_smallClusters_le P (wnClosed P H ξ R q k n)
    ⌈2 * (2 + ρ)⌉₊ (2 * d * (1 - q)) θ
    (wnClosed_prob hκ hH ξ R hq0 hq1 hkn)
    (wnClosed_productBound hκ hH hρ ξ R q hkn)
    hθ1 hεθ h3 N D
  intro x ω hx
  exact hN x hx.1

/-- The rough-site Peierls bound, with the same dependence range. -/
theorem wnNice_smallClusters_prob {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (ξ : ℝ) {R : ℝ} (hR : 1 ≤ R) {q : ℝ≥0∞}
    (hq0 : 0 < q) (hq1 : q < 1) {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    {θ : ℝ≥0∞} (hθ1 : θ ≤ 1)
    (hεθ : (1 + 3 ^ d) * (2 * (d : ℝ≥0∞) * (1 - q)) ≤
      θ ^ ((⌈2 * (2 + ρ)⌉₊ + 1) ^ d))
    (h3 : (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹) (D : ℕ) :
    ∃ N : ℕ,
      P {ω | ¬ SmallClusters (wnNice
        (wnGood P H ξ R q (k - 1) n ω) (wnGood P H ξ R q k n ω)) D} ≤
        (2 * (N : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ (D / 2) ∧
      (∀ y, wnRough P H ξ R q k n y ≠ ∅ → WithinInf (N : ℤ) y 0) ∧
      (N : ℝ) ≤ 3 * (R + 4) * (2 : ℝ) ^ k := by
  obtain ⟨N, hN, hNle⟩ := wnRough_support_bounded_le P H ξ hR q k n
  refine ⟨N, ?_, hN, hNle⟩
  have hraw := measure_not_smallClusters_le P (wnRough P H ξ R q k n)
    ⌈2 * (2 + ρ)⌉₊ ((1 + 3 ^ d) * (2 * d * (1 - q))) θ
    (wnRough_prob hκ hH ξ R hq0 hq1 hkn)
    (wnRough_productBound hκ hH hρ ξ R q hk hkn)
    hθ1 hεθ h3 N D (fun y ω hy => hN y (Set.nonempty_iff_ne_empty.mp ⟨ω, hy⟩))
  convert hraw using 1
  congr 1
  ext ω
  have heq : wnNice (wnGood P H ξ R q (k - 1) n ω)
      (wnGood P H ξ R q k n ω) = {y | ω ∉ wnRough P H ξ R q k n y} := by
    ext y
    simp [wnRough]
  simp only [Set.mem_ofPred_eq, heq]

end HigherDimLQGContinuity
