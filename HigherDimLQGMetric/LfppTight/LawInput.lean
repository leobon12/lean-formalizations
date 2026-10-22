import HigherDimLQGMetric.LfppTight.FieldContinuity
import HigherDimLQGMetric.LfppTight.MetricLawMeas
import HigherDimLQGMetric.LfppTight.MedianPos
import HigherDimLQGMetric.Main.LFPPMedian
import HigherDimLQGMetric.Limits.LengthLFPP

/-!
# Measurable normalized LFPP laws for the full input class
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_aemeasurable_normalized_lfpp {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusBddCont h P) :
    AEMeasurable (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ •
      lfppDist κ ξ ε (h ω))) P := by
  let H : Rd d → Ω → ℝ := fun z ω => convMollify κ ε (h ω) z
  have hm : ∀ z, AEMeasurable (H z) P := by
    intro z
    exact ((l10a_measurable_convMollify_apply κ ε z).comp hh.measurable).aemeasurable
  have hc : ∀ᵐ ω ∂P, Continuous fun z => H z ω :=
    l6a_ae_continuous_convMollify hd κ hκ P h hh hε
  exact l6a_aemeasurable_lfppMetricLaw P ξ (aEps κ ξ ε)⁻¹ H hm hc

/-- Every positive-cutoff prelimit under the full input class is a continuous
length metric almost surely. -/
theorem l6a_ae_prelimit_length {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusBddCont h P) :
    ∀ᵐ ω ∂P, IsContLengthFn
      (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) := by
  have ha := l6a_aEps_pos hd κ hκ ξ hε
  filter_upwards [l6a_ae_continuous_convMollify hd κ hκ P h hh hε]
    with ω hω
  exact l6c_scaled_lfpp_isContLengthFn κ ξ ε (aEps κ ξ ε) (h ω) hω ha

/-- The positivity, measurability and prelimit metric portions of `L6a_tight`.
The remaining portions concern tightness and the support of limit laws. -/
theorem l6a_basic {d : ℕ} (ξ : ℝ) (κ : Rd d → ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusBddCont h P) :
    (∀ ε ∈ Set.Ioo (0 : ℝ) 1, 0 < aEps κ ξ ε) ∧
    (∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      AEMeasurable (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ •
        lfppDist κ ξ ε (h ω))) P) ∧
    (∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      ∀ᵐ ω ∂P, IsContLengthFn
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))) := by
  obtain ⟨Q, hQ, _⟩ := hB2
  exact ⟨fun ε hε => l6a_aEps_pos hQ.dim κ hQ.kernel ξ hε.1,
    fun ε hε => l6a_aemeasurable_normalized_lfpp hQ.dim κ hQ.kernel ξ hε.1 P h hh,
    fun ε hε => l6a_ae_prelimit_length hQ.dim κ hQ.kernel ξ hε.1 P h hh⟩

end HigherDimLQGMetric
