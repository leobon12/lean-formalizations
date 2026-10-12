import MeshOnly.MeshOnlyClockSteps
import MeshOnly.MeshOnlyClockPoisson
import BouRabeeGwynne.FiniteDirichlet

/-! Mean-value preservation and the clock bound at an independent Poisson
horizon, directly for the actual absorbed finite walk. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
variable (N : FiniteConductanceNetwork V)

theorem integral_uniformizedNStepPMF_of_harmonic (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) (f : V → ℝ)
    (hf : ∀ v ∈ S, N.laplacian f v = 0) (n : ℕ) (v : V) :
    (∫ w, f w ∂(N.uniformizedNStepPMF m hm S n v).toMeasure) = f v := by
  have hup := N.integral_uniformizedNStepPMF_le_of_generator_le m hm S f
    (b := 0) le_rfl (by intro w hw; simp [massGenerator, hf w hw]) n v
  have hlo := N.integral_uniformizedNStepPMF_le_of_generator_le m hm S (-f)
    (b := 0) le_rfl (by intro w hw; simp [massGenerator, N.laplacian_neg, hf w hw]) n v
  simp only [zero_div, mul_zero, add_zero, Pi.neg_apply, integral_neg] at hup hlo
  linarith

theorem integral_uniformizedPoisson_le (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) (f : V → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ v ∈ S, N.massGenerator m f v ≤ b) (v : V) (r : ℝ≥0) :
    (∫ w, f w ∂((poissonMeasure r).toPMF.bind
      (fun n => N.uniformizedNStepPMF m hm S n v)).toMeasure) ≤
      f v + (r : ℝ) * (b / N.uniformizationRate m) := by
  exact MeshOnlyClock.integral_poisson_bind_le r _ f _ _
    (fun n => N.integral_uniformizedNStepPMF_le_of_generator_le m hm S f hb hf n v)

/-- No limit as the exit time goes to infinity is needed: harmonicity preserves
the mean at each independent Poisson horizon. -/
theorem integral_uniformizedPoisson_of_harmonic (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) (f : V → ℝ)
    (hf : ∀ v ∈ S, N.laplacian f v = 0) (v : V) (r : ℝ≥0) :
    (∫ w, f w ∂((poissonMeasure r).toPMF.bind
      (fun n => N.uniformizedNStepPMF m hm S n v)).toMeasure) = f v := by
  have hup := N.integral_uniformizedPoisson_le m hm S f
    (b := 0) le_rfl (by intro w hw; simp [massGenerator, hf w hw]) v r
  have hlo := N.integral_uniformizedPoisson_le m hm S (-f)
    (b := 0) le_rfl (by intro w hw; simp [massGenerator, N.laplacian_neg, hf w hw]) v r
  simp only [zero_div, mul_zero, add_zero, Pi.neg_apply, integral_neg] at hup hlo
  linarith

end BouRabeeGwynne.FiniteConductanceNetwork
