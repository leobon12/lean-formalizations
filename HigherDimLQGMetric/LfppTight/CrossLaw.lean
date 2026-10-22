import HigherDimLQGMetric.LfppTight.CrossUnitLFPP
import HigherDimLQGMetric.LfppTight.LawInput

/-! Crossing probabilities of normalized LFPP depend only on the LGF law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_cross_normalized_law_eq {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h g : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (hg : IsNormalizedLGF g P) (hlaw : P.map g = P.map h)
    (b c : ℝ) :
    P {ω | supPairs
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (g ω)))
        (ball (0 : Rd d) b) ≤
      ENNReal.ofReal c * infPairs
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (g ω)))
        (sphere 0 b) (sphere 0 1)} =
    P {ω | supPairs
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))
        (ball (0 : Rd d) b) ≤
      ENNReal.ofReal c * infPairs
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))
        (sphere 0 b) (sphere 0 1)} := by
  let F : DistRd d → C(Rd d × Rd d, ℝ) := fun v =>
    toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε v)
  let S : Set C(Rd d × Rd d, ℝ) :=
    {D | supPairs D (ball (0 : Rd d) b) ≤
      ENNReal.ofReal c * infPairs D (sphere 0 b) (sphere 0 1)}
  have hS : MeasurableSet S := l6a_measurableSet_cross _ _ _ c
  have hcanon : P.map h = normLGFLaw d :=
    (normLGFLaw_spec_holds d hd).2.2 (P.map h) inferInstance hh.map_id
  have hF : AEMeasurable F (P.map h) := by
    rw [hcanon]
    letI : IsProbabilityMeasure (normLGFLaw d) :=
      (normLGFLaw_spec_holds d hd).1
    exact l6a_aemeasurable_normalized_lfpp hd κ hκ ξ hε
      (normLGFLaw d) id (normLGFLaw_spec_holds d hd).2.1.1.isLGFPlusBddCont
  have hF' : AEMeasurable F (P.map g) := hlaw ▸ hF
  have hmG : AEMeasurable (F ∘ g) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ hε P g hg.1.isLGFPlusBddCont
  have hmH : AEMeasurable (F ∘ h) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ hε P h hh.1.isLGFPlusBddCont
  have hmap : P.map (F ∘ g) = P.map (F ∘ h) := by
    rw [← AEMeasurable.map_map_of_aemeasurable hF' hg.1.measurable.aemeasurable,
      ← AEMeasurable.map_map_of_aemeasurable hF hh.1.measurable.aemeasurable,
      hlaw]
  change P ((F ∘ g) ⁻¹' S) = P ((F ∘ h) ⁻¹' S)
  rw [← Measure.map_apply_of_aemeasurable hmG hS,
    ← Measure.map_apply_of_aemeasurable hmH hS, hmap]

end HigherDimLQGMetric
