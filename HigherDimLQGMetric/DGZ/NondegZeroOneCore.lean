import HigherDimLQGMetric.DGZ.NondegEventuallyMeasure

/-! Zero-one law for a joint limit whose two distance-zero sets are bounded. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_zeroOne_limitLaw_of_bounded
    {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ))
    (hb₁ : ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)),
      s ∈ nd_boundedZeroEvent rGrid r)
    (hb₂ : ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)),
      s ∈ nd_boundedZeroEvent rGrid (2 * r)) :
    (μ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) = 0 ∨
      (μ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) = 1 := by
  let ν : Measure (nd_Joint d rGrid) := μ
  let Z := nd_positiveCrossEvent (d := d) rGrid r
  have hd : 0 < d := by have := h.dim; omega
  have hpseudo := nd_ae_pseudoSet_of_tendsto h hH hq0 hq1 rGrid ns hlim
  have hi₁ := nd_ae_exists_selectedIndex_of_tendsto h hH hq0 hq1
    rGrid r hrGrid hr ns hlim hb₁
  have hi₂ := nd_ae_exists_selectedIndex_of_tendsto h hH hq0 hq1
    rGrid (2 * r) hrGrid (mul_pos (by norm_num) hr) ns hlim hb₂
  have hev : ∀ᵐ s ∂ν, s ∈ Z →
      ∀ᶠ j : ℕ in atTop, s ∈ nd_sepPairEvent rGrid r j := by
    filter_upwards [hpseudo, hb₁, hb₂, hi₁, hi₂] with
      s hs hsB₁ hsB₂ hsI₁ hsI₂ hsZ
    exact nd_eventually_mem_sepPairEvent hd hrGrid hr s hs
      hsB₁ hsB₂ hsI₁ hsI₂ hsZ
  have hsq : ν Z ≤ ν Z * ν Z :=
    nd_measure_le_of_ae_eventually ν Z (nd_sepPairEvent rGrid r)
      (ν Z * ν Z) hev
      (fun j => nd_sepPairEvent_measure_le_square h hH hq0 hq1
        rGrid r hrGrid hr ns hns hlim j)
  have hle : ν Z ≤ 1 := prob_le_one
  by_cases hz : ν Z = 0
  · exact Or.inl hz
  · right
    have hfin : ν Z ≠ ∞ := ne_top_of_le_ne_top (by simp) hle
    have hone : 1 ≤ ν Z :=
      (ENNReal.mul_le_mul_iff_left hz hfin).mp (by simpa using hsq)
    exact le_antisymm hle hone

end HigherDimLQGMetric.DGZ
