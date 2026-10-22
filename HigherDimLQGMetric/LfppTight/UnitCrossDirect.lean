import HigherDimLQGMetric.LfppTight.CoupledUnitCross
import HigherDimLQGMetric.LfppTight.CrossCenteredLaw
import HigherDimLFPP.Field.Exists

/-! Unit-scale crossing for a normalized LGF, directly from the DGZ adapter. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_unitCross_normalized_direct (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {p C : ℝ} (hp : p < 1) (hC : 0 < C) :
    ∃ b ε₀ : ℝ, 0 < b ∧ b ≤ 1 / 4 ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        ENNReal.ofReal p ≤ P {ω |
          supPairs (lfppDist κ ξ ε (h ω)) (ball (0 : Rd d) b) ≤
            ENNReal.ofReal C⁻¹ * infPairs
              (lfppDist κ ξ ε (h ω)) (sphere 0 b) (sphere 0 1)} := by
  obtain ⟨_, hExists⟩ := HigherDimLFPP.field_exists_impl d
    (by have := hDGZ.dim; omega : 1 ≤ d)
  obtain ⟨Ω', _, P', W, G, hP', hW, hG⟩ := hExists κ hDGZ.kernel
  letI : IsProbabilityMeasure P' := hP'
  obtain ⟨Ψ, hΨc, hΨm, hlaw⟩ := l6a_cross_coupled_law hL1e
    hDGZ.dim hDGZ.kernel ξ P h hh P' W hW G hG
  obtain ⟨b, ε₀, hb, hb4, hε₀, hεhalf, hcross⟩ := l6a_coupled_unitCross
    hDGZ hAdapter P' W hW G hG Ψ hΨc hΨm hp hC
  refine ⟨b, ε₀, hb, hb4, hε₀, hεhalf, ?_⟩
  intro ε hε
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨hε.1, (hε.2.trans_le hεhalf).trans (by norm_num)⟩
  rw [hlaw ε hε1 (ball 0 b) (sphere 0 b) (sphere 0 1) C⁻¹]
  exact hcross ε hε

end HigherDimLQGMetric
