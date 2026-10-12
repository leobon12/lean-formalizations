import MeshOnly.MeshOnlyClockMoments
import MeshOnly.MeshOnlyClockSupport

/-! The local clock inequality for the same finite-time law as Proposition 3.1.
The geometric corrected-square identity and weight oscillation are explicit
inputs to this probabilistic step. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option backward.isDefEq.respectTransparency false

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
variable (N : FiniteConductanceNetwork V)

theorem poissonizedUniformizedLaw_integral_le (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) (f : V → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ v ∈ S, N.massGenerator m f v ≤ b) (v : V) (t : ℝ≥0) :
    (∫ w, f w ∂N.poissonizedUniformizedLaw m hm S v t) ≤ f v + b * (t : ℝ) := by
  let r : ℝ≥0 := NNReal.mk ((t : ℝ) * N.uniformizationRate m)
    (mul_nonneg t.coe_nonneg (N.uniformizationRate_pos m hm).le)
  have h := N.integral_uniformizedPoisson_le m hm S f hb hf v r
  have hrate : N.uniformizationRate m ≠ 0 := (N.uniformizationRate_pos m hm).ne'
  have hscale : (r : ℝ) * (b / N.uniformizationRate m) = b * (t : ℝ) := by
    simp only [r, NNReal.coe_mk]
    field_simp
    <;> ring
  rw [hscale] at h
  exact h

theorem poissonizedUniformizedLaw_integral_of_harmonic (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) (f : V → ℝ)
    (hf : ∀ v ∈ S, N.laplacian f v = 0) (v : V) (t : ℝ≥0) :
    (∫ w, f w ∂N.poissonizedUniformizedLaw m hm S v t) = f v := by
  exact N.integral_uniformizedPoisson_of_harmonic m hm S f hf v _

/-- Applying the drift estimate to squared distance minus the local power
weight gives the crossing bound. In the tiling application q is squared
distance from v, b=2d, and A=2ε(r+2ε). -/
theorem poissonizedUniformizedLaw_crossing_le (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) (q ω : V → ℝ) {v : V} (hqv : q v = 0)
    (hq : ∀ w, 0 ≤ q w) {b A r : ℝ} (hb : 0 ≤ b) (hr : 0 < r)
    (hgen : ∀ w ∈ S, N.massGenerator m (q - ω) w ≤ b) (t : ℝ≥0)
    (hω : ∀ᵐ w ∂N.poissonizedUniformizedLaw m hm S v t, ω w - ω v ≤ A) :
    (N.poissonizedUniformizedLaw m hm S v t {w | r ^ 2 ≤ q w}).toReal ≤
      (b * (t : ℝ) + A) / r ^ 2 := by
  let μ := N.poissonizedUniformizedLaw m hm S v t
  have hphi := N.poissonizedUniformizedLaw_integral_le m hm S (q - ω) hb hgen v t
  change (∫ w, q w - ω w ∂μ) ≤ q v - ω v + b * (t : ℝ) at hphi
  rw [integral_sub Integrable.of_finite Integrable.of_finite, hqv, zero_sub] at hphi
  have hwmean : (∫ w, ω w ∂μ) ≤ ω v + A := by
    calc
      _ ≤ ∫ _ : V, ω v + A ∂μ := by
        apply integral_mono_ae Integrable.of_finite Integrable.of_finite
        filter_upwards [hω] with w hw
        linarith
      _ = _ := by simp [μ]
  have hmoment : (∫ w, q w ∂μ) ≤ b * (t : ℝ) + A := by linarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Filter.Eventually.of_forall hq) Integrable.of_finite (r ^ 2)
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  change (μ {w | r ^ 2 ≤ q w}).toReal * r ^ 2 ≤ _
  simpa only [Measure.real, mul_comm] using hmarkov.trans hmoment

end BouRabeeGwynne.FiniteConductanceNetwork
