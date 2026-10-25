import SupercriticalLQGUniqueness.B2.PfeAxioms.CanonicalFieldScaleLaw

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.DDDF LQGMetric.DFGPS
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem map_normalized_crossLenIn_fieldScale
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (δ : Ioo (0 : ℝ) 1)
    (U : TopologicalSpace.Opens ℂ) (hUc : IsConnected (U : Set ℂ))
    (x y : ℂ) (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    {r : ℝ} (hr : 0 < r) :
    P.map (fun ω =>
      ENNReal.ofReal ((m ⟨(δ : ℝ), δ.property.1⟩ : ℝ)⁻¹) *
        crossLenIn (ξ : ℝ) (heatMollify (δ : ℝ) (fieldScale r (h ω)))
          U {x} {y}) =
    P.map (fun ω =>
      ENNReal.ofReal ((m ⟨(δ : ℝ), δ.property.1⟩ : ℝ)⁻¹) *
        crossLenIn (ξ : ℝ) (heatMollify (δ : ℝ) (h ω))
          U {x} {y}) := by
  exact map_canonical_observable_fieldScale P h hh _
    (aemeasurable_canonical_normalized_crossLenIn hS ξ Q hQ m hm
      δ U hUc x y hx hy hxy) hr

end SupercriticalLQGUniqueness.B2.PfeAxioms
