import HigherDimLQGMetric.LfppTight.LogEnergyQuant
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.IntegralConvolution

/-! The convolution of a linearly growing measure with any finite measure retains linear growth. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_conv_smallBall {d : ℕ}
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A : ℝ} (hA : 0 ≤ A)
    (hμ : ∀ z : Rd d, ∀ s > 0, μ.real (closedBall z s) ≤ A * s)
    (z : Rd d) (s : ℝ) (hs : 0 < s) :
    (Measure.conv μ ν).real (closedBall z s) ≤ A * ν.real univ * s := by
  have hset : MeasurableSet (closedBall z s) := isClosed_closedBall.measurableSet
  have heq : (Measure.conv μ ν) (closedBall z s) =
      ∫⁻ a, μ (closedBall (z - a) s) ∂ν := by
    rw [Measure.conv_comm μ ν, Measure.conv, Measure.map_apply (by fun_prop) hset]
    have hs' : MeasurableSet
        ((fun p : Rd d × Rd d => p.1 + p.2) ⁻¹' closedBall z s) :=
      hset.preimage (by fun_prop)
    rw [Measure.prod_apply hs']
    congr 1
    funext a
    congr 1
    ext x
    simp only [mem_preimage, mem_closedBall, dist_eq_norm]
    abel
  have hpt (a : Rd d) : μ (closedBall (z - a) s) ≤ ENNReal.ofReal (A * s) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hμ (z - a) s hs)
  have hle : (Measure.conv μ ν) (closedBall z s) ≤
      ENNReal.ofReal (A * s) * ν univ := by
    rw [heq]
    calc
      (∫⁻ a, μ (closedBall (z - a) s) ∂ν) ≤
          ∫⁻ _a, ENNReal.ofReal (A * s) ∂ν := lintegral_mono hpt
      _ = ENNReal.ofReal (A * s) * ν univ := lintegral_const _
  have hnonneg : 0 ≤ A * ν.real univ * s := by positivity
  have hreal : (Measure.conv μ ν) (closedBall z s) ≤
      ENNReal.ofReal (A * ν.real univ * s) := by
    calc
      _ ≤ ENNReal.ofReal (A * s) * ν univ := hle
      _ = ENNReal.ofReal (A * s * ν.real univ) := by
        rw [← ofReal_measureReal, ENNReal.ofReal_mul (mul_nonneg hA hs.le)]
      _ = ENNReal.ofReal (A * ν.real univ * s) := by
        congr 1
        ring
  apply (ENNReal.ofReal_le_ofReal_iff hnonneg).1
  rw [ofReal_measureReal]
  exact hreal

private theorem logWeight_add_le {d : ℕ} (x y : Rd d) :
    Real.log (2 + ‖x + y‖) ≤
      Real.log (2 + ‖x‖) + Real.log (2 + ‖y‖) := by
  have hnorm : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
  have hmul : 2 + ‖x + y‖ ≤ (2 + ‖x‖) * (2 + ‖y‖) := by
    nlinarith [norm_nonneg x, norm_nonneg y,
      mul_nonneg (norm_nonneg x) (norm_nonneg y)]
  rw [← Real.log_mul (by positivity : 2 + ‖x‖ ≠ 0)
    (by positivity : 2 + ‖y‖ ≠ 0)]
  exact Real.log_le_log (by positivity) hmul

/-- A logarithmic moment survives convolution, with a quantitative bound. -/
theorem l6a_conv_logMoment {d : ℕ}
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun x : Rd d => Real.log (2 + ‖x‖)) μ)
    (hν : Integrable (fun x : Rd d => Real.log (2 + ‖x‖)) ν) :
    Integrable (fun x : Rd d => Real.log (2 + ‖x‖)) (Measure.conv μ ν) ∧
      (∫ x : Rd d, Real.log (2 + ‖x‖) ∂(Measure.conv μ ν)) ≤
        ν.real univ * (∫ x : Rd d, Real.log (2 + ‖x‖) ∂μ) +
          μ.real univ * (∫ x : Rd d, Real.log (2 + ‖x‖) ∂ν) := by
  let W : Rd d → ℝ := fun x => Real.log (2 + ‖x‖)
  have hWm : Measurable W := by dsimp [W]; fun_prop
  have hprod : Integrable (fun p : Rd d × Rd d => W (p.1 + p.2)) (μ.prod ν) := by
    apply ((hμ.comp_fst ν).add (hν.comp_snd μ)).mono'
    · exact (hWm.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable
    · apply ae_of_all
      intro p
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg
        (by nlinarith [norm_nonneg (p.1 + p.2)]))]
      exact logWeight_add_le p.1 p.2
  have hconv : Integrable W (Measure.conv μ ν) := by
    change Integrable W ((μ.prod ν).map fun p : Rd d × Rd d => p.1 + p.2)
    exact (integrable_map_measure hWm.aestronglyMeasurable
      (measurable_fst.add measurable_snd).aemeasurable).2 hprod
  refine ⟨hconv, ?_⟩
  have heq : (∫ x : Rd d, W x ∂(Measure.conv μ ν)) =
      ∫ p : Rd d × Rd d, W (p.1 + p.2) ∂(μ.prod ν) := by
    change (∫ x, W x ∂((μ.prod ν).map fun p : Rd d × Rd d => p.1 + p.2)) = _
    exact integral_map (measurable_fst.add measurable_snd).aemeasurable
      hconv.aestronglyMeasurable
  rw [show (∫ x : Rd d, Real.log (2 + ‖x‖) ∂(Measure.conv μ ν)) =
    ∫ x : Rd d, W x ∂(Measure.conv μ ν) from rfl, heq]
  calc
    (∫ p : Rd d × Rd d, W (p.1 + p.2) ∂(μ.prod ν)) ≤
        ∫ p : Rd d × Rd d, W p.1 + W p.2 ∂(μ.prod ν) :=
      integral_mono hprod ((hμ.comp_fst ν).add (hν.comp_snd μ))
        (fun p => logWeight_add_le p.1 p.2)
    _ = ν.real univ * (∫ x : Rd d, W x ∂μ) +
        μ.real univ * (∫ x : Rd d, W x ∂ν) := by
      rw [integral_add (hμ.comp_fst ν) (hν.comp_snd μ)]
      change (∫ p : Rd d × Rd d, W p.1 ∂(μ.prod ν)) +
        (∫ p : Rd d × Rd d, W p.2 ∂(μ.prod ν)) = _
      rw [integral_fun_fst, integral_fun_snd]
      simp only [smul_eq_mul]

end HigherDimLQGMetric
