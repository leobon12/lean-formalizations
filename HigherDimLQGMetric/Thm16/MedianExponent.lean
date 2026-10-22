import HigherDimLQGMetric.Thm16.LogComparison
import HigherDimLQGMetric.Main.ExponentBridge
import HigherDimLQGMetric.LfppTight.MedianPos
import HigherDimLQGMetric.DGZ.AdapterBasics

/-! The real-cutoff adapter exponent transfers across fixed median bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN)

theorem l9c_aEps_exponent_of_median_bounds {d : ℕ} (hd : 3 ≤ d)
    {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W)
    (G : ℝ → Rd d → Ω → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (G ε))
    {m M ε₀ : ℝ} (hm : 0 < m) (hε₀ : 0 < ε₀)
    (hcomp : ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      m * DGZ.aHat P G ξ ε ≤ aEps κ ξ ε ∧
        aEps κ ξ ε ≤ M * DGZ.aHat P G ξ ε) :
    Tendsto (fun ε => Real.log (aEps κ ξ ε) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - ξ * distExp d ξ)) := by
  have hd2 : 2 ≤ d := by omega
  let β : ℝ := ξ * (distExp d ξ - Real.sqrt (2 * d)) / 2
  have hβ0 : 0 < β := by dsimp [β]; positivity
  have hβ : β < ξ * (distExp d ξ - Real.sqrt (2 * d)) := by
    dsimp [β]
    have hpos : 0 < ξ * (distExp d ξ - Real.sqrt (2 * d)) :=
      mul_pos hξ (sub_pos.mpr hsub)
    linarith
  have hDGZ := l10a_dgzHyp hd2 hκ hξ hsub
  have hAhat : Tendsto (fun ε => Real.log (DGZ.aHat P G ξ ε) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - ξ * distExp d ξ)) :=
    (hB2 d κ ξ (distExp d ξ) hDGZ β hβ0 hβ Ω P W G hW hG).2.2.2
  have hp : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < aEps κ ξ ε ∧ 0 < DGZ.aHat P G ξ ε := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 from Iio_mem_nhds (by norm_num))]
      with ε hε hε1
    exact ⟨l6a_aEps_pos hd2 κ hκ ξ hε,
      DGZ.aHat_pos (by omega : 0 < d) hW (hG ε ⟨hε, hε1⟩) ξ⟩
  have hc : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      m * DGZ.aHat P G ξ ε ≤ aEps κ ξ ε ∧
        aEps κ ξ ε ≤ M * DGZ.aHat P G ξ ε := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ ε : ℝ in 𝓝 0, ε < ε₀ from Iio_mem_nhds hε₀)]
      with ε hε hε0
    exact hcomp ε ⟨hε, hε0⟩
  exact l9c_exponent_of_comparable hm hp hc hAhat

end HigherDimLQGMetric
