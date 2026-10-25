import SupercriticalLQGUniqueness.B2.PfeAxioms.LFPPSetConstant
import SupercriticalLQGUniqueness.B2.Iface.Statements
import LQGMetric.Papers.DFGPS.L2_6Law

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.DFGPS

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_crossLenIn_fieldScale
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (U A B : Set ℂ) :
    ∀ᵐ ω ∂P,
      crossLenIn ξ (heatMollify (ε / r) (fieldScale r (h ω))) U A B =
        ENNReal.ofReal (r⁻¹ * Real.exp (-ξ * circleAvg (h ω) r 0)) *
          crossLenIn ξ (heatMollify ε (h ω))
            ((fun z => (r : ℂ) * z) '' U)
            ((fun z => (r : ℂ) * z) '' A)
            ((fun z => (r : ℂ) * z) '' B) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hεr : ε / r ≠ 0 := div_ne_zero hε.ne' hr0
  have hAff := ae_heatMollify_affineComp hh.1 hε.ne' hr
  have hConv := (hh.1.affineComp hr 0).ae_tendstoLocallyUniformly_heatMollify
    (ε / r) hεr
  filter_upwards [hAff, hConv] with ω hA hC
  have hφ : ∀ z : ℂ,
      heatMollify (ε / r) (fieldScale r (h ω)) z =
        heatMollify ε (h ω) ((r : ℂ) * z) - circleAvg (h ω) r 0 := by
    intro z
    change heatMollify (ε / r)
      (addConst (affineComp r 0 (h ω)) (-circleAvg (h ω) r 0)) z = _
    rw [heatMollify_addConst_of_tendsto hεr
      ((tendstoLocallyUniformlyOn_univ.2 hC.1).tendsto_at (mem_univ z))]
    rw [hA z]
    ring
  let φ : ℂ → ℝ := fun z => heatMollify ε (h ω) ((r : ℂ) * z)
  let c : ℝ := circleAvg (h ω) r 0
  have hleft : crossLenIn ξ (heatMollify (ε / r) (fieldScale r (h ω))) U A B =
      ENNReal.ofReal (Real.exp (-ξ * c)) * crossLenIn ξ φ U A B := by
    have heq : heatMollify (ε / r) (fieldScale r (h ω)) = fun z => φ z + (-c) := by
      funext z
      simpa only [φ, c, sub_eq_add_neg] using hφ z
    rw [heq, crossLenIn_add_const]
    congr 1
    congr 1
    ring
  rw [hleft, crossLenIn_image_mul ξ (heatMollify ε (h ω)) U A B hr]
  change ENNReal.ofReal (Real.exp (-ξ * c)) * crossLenIn ξ φ U A B =
    ENNReal.ofReal (r⁻¹ * Real.exp (-ξ * c)) *
      (ENNReal.ofReal r * crossLenIn ξ φ U A B)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have he : r⁻¹ * Real.exp (-ξ * c) * r = Real.exp (-ξ * c) := by
    field_simp
  rw [he]

end SupercriticalLQGUniqueness.B2.PfeAxioms
