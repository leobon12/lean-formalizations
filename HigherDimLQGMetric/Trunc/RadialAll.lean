import HigherDimLQGMetric.Trunc.RadialCont
import HigherDimLQGMetric.ConvField.RadialAll

/-! One almost sure event for every truncated radial pairing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

set_option maxHeartbeats 1000000 in
theorem l2c_ae_trunc_radial_all (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ), 0 < ε → ∀ z : Rd d,
      truncMollify κ ε (h ω) z =
        ((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
            l2c_axisFactor κ (Real.log ε / 2) r * sphereAvg (h ω) r z := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (ℝ × Rd d)
  let _ : Countable S := hSc.to_subtype
  have hfix : ∀ᵐ ω ∂P, ∀ p : S,
      truncMollify κ (Real.exp (2 * p.1.1)) (h ω) p.1.2 =
        ((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
            l2c_axisFactor κ p.1.1 r * sphereAvg (h ω) r p.1.2 := by
    apply ae_all_iff.mpr
    intro p
    filter_upwards [l2c_ae_trunc_radial hd hκ hh.1
      (ε := Real.exp (2 * p.1.1)) (Real.exp_pos _) p.1.2]
      with ω hw
    simpa only [l2c_axisFactor, l2c_sqrt_exp_two,
      show Real.log (Real.exp (2 * p.1.1)) / 2 = p.1.1 by
        rw [Real.log_exp]; ring] using hw
  filter_upwards [hfix, hh.1.ae_continuousOn_sphereAvg hd,
    l2b_ae_growth_all hd hh] with ω hfix hcont hgrowth
  intro ε hε z
  let lhs : ℝ × Rd d → ℝ := fun p =>
    truncMollify κ (Real.exp (2 * p.1)) (h ω) p.2
  let rhs : ℝ × Rd d → ℝ := fun p =>
    ((volume : Measure (Rd d)).toSphere univ).toReal *
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        l2c_axisFactor κ p.1 r * sphereAvg (h ω) r p.2
  have hlhs : Continuous lhs :=
    (h ω).continuous.comp (l2c_continuous_truncTest_exp hd hκ)
  have hrhs : Continuous rhs :=
    continuous_const.mul (l2c_continuous_trunc_radial_integral hd hκ (h ω)
      hcont.2 hgrowth)
  have heq : lhs = rhs := Continuous.ext_on hSd hlhs hrhs (by
    intro p hp
    exact hfix ⟨p, hp⟩)
  have hp := congrFun heq (Real.log ε / 2, z)
  have hscale : Real.exp (2 * (Real.log ε / 2)) = ε := by
    rw [show 2 * (Real.log ε / 2) = Real.log ε by ring, Real.exp_log hε]
  simpa only [lhs, rhs, hscale] using hp

end HigherDimLQGMetric
