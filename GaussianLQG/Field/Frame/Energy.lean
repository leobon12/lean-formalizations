import GaussianLQG.Field.Frame.Heat

/-!
# The heat-kernel representation of the energy (blueprint Appendix B, `lem:kappa`)

For regular `μ, ν` put `μ° = μ − μ(ℂ) σ`, `ν° = ν − ν(ℂ) σ` (`σ` the uniform measure on `∂𝔻`). The
function `framePsi μ ν t = π ∬ p_t(u, v) μ°(du) ν°(dv)`, expanded into four products of positive
measures, is integrable on `(0, ∞)` and

`∫_0^∞ framePsi μ ν t dt = ∬ −log|u − v| μ°(du) ν°(dv) = energy μ ν`

(`integrableOn_framePsi`, `integral_framePsi`). The second equality uses
`∫ log|u − v| σ(dv) = log⁺|u|` and `∫ log⁺|v| σ(dv) = 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG
namespace WNFrame

open LQGMetric

/-- `P_t(m) = ∬ p_t(u, v) m(du, dv)`. -/
def heatPair (t : ℝ) (m : Measure (ℂ × ℂ)) : ℝ := ∫ p, heatKernel t p.1 p.2 ∂m

/-- `L(m) = ∬ log|u − v| m(du, dv)`. -/
def logPair (m : Measure (ℂ × ℂ)) : ℝ := ∫ p, Real.log ‖p.1 - p.2‖ ∂m

/-- `π ∬ p_t d(μ° ⊗ ν°)`, expanded. -/
def framePsi (μ ν : Measure ℂ) (t : ℝ) : ℝ :=
  Real.pi * (heatPair t (μ.prod ν) - ν.real univ * heatPair t (μ.prod (circleMeasure 0 1)) -
    μ.real univ * heatPair t ((circleMeasure 0 1).prod ν) +
    μ.real univ * ν.real univ * heatPair t ((circleMeasure 0 1).prod (circleMeasure 0 1)))

lemma real_prod_univ (μ ν : Measure ℂ) [SFinite ν] :
    (μ.prod ν).real univ = μ.real univ * ν.real univ := by
  simp only [measureReal_def]
  rw [← univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]

lemma ae_circleMeasure_norm_le : ∀ᵐ u ∂(circleMeasure 0 1), ‖u‖ ≤ (1 : ℝ) := by
  filter_upwards [ae_circleMeasure_mem_sphere 0 1] with u hu
  simp only [Metric.mem_sphere, dist_zero_right, abs_one] at hu
  exact hu.le

lemma integrable_posLog_norm {α : Measure ℂ} [IsFiniteMeasure α] {R : ℝ}
    (hα : ∀ᵐ u ∂α, ‖u‖ ≤ R) : Integrable (fun u => Real.posLog ‖u‖) α := by
  refine Integrable.mono' (integrable_const R) (by fun_prop : Measurable fun u : ℂ =>
    Real.posLog ‖u‖).aestronglyMeasurable ?_
  filter_upwards [hα] with u hu
  rw [Real.norm_of_nonneg Real.posLog_nonneg]
  exact (Real.posLog_le_abs _).trans (by rwa [abs_norm])

/-- The integrability and Frullani identity for `framePsi`, as a balanced combination of four
products. -/
theorem framePsi_frullani {μ ν : Measure ℂ} (hμ : IsRegular μ) (hν : IsRegular ν) :
    IntegrableOn (framePsi μ ν) (Ioi 0) ∧
      ∫ t in Ioi 0, framePsi μ ν t = -(logPair (μ.prod ν) -
        ν.real univ * logPair (μ.prod (circleMeasure 0 1)) -
        μ.real univ * logPair ((circleMeasure 0 1).prod ν) +
        μ.real univ * ν.real univ *
          logPair ((circleMeasure 0 1).prod (circleMeasure 0 1))) := by
  have := hμ.1
  have := hν.1
  obtain ⟨Rμ, -, hRμ⟩ := exists_ae_norm_le_of_isRegular hμ
  obtain ⟨Rν, -, hRν⟩ := exists_ae_norm_le_of_isRegular hν
  set σ : Measure ℂ := circleMeasure 0 1 with hσ
  have hσ1 : σ.real univ = 1 := circleMeasure_real_univ 0 1
  have hσa : ∀ u, σ {u} = 0 := circleMeasure_singleton 0 one_ne_zero
  set m : Fin 4 → Measure (ℂ × ℂ) := ![μ.prod ν, μ.prod σ, σ.prod ν, σ.prod σ] with hm
  set c : Fin 4 → ℝ := ![1, -ν.real univ, -μ.real univ, μ.real univ * ν.real univ] with hc
  have hfin : ∀ i, IsFiniteMeasure (m i) := fun i => by
    fin_cases i
    exacts [(inferInstance : IsFiniteMeasure (μ.prod ν)),
      (inferInstance : IsFiniteMeasure (μ.prod σ)), (inferInstance : IsFiniteMeasure (σ.prod ν)),
      (inferInstance : IsFiniteMeasure (σ.prod σ))]
  have hpos : ∀ i ∈ (Finset.univ : Finset (Fin 4)), ∀ᵐ p ∂(m i), 0 < ‖p.1 - p.2‖ := by
    intro i _
    fin_cases i
    · exact ae_dist_pos_of_left hμ.measure_singleton
    · exact ae_dist_pos_of_right hσa
    · exact ae_dist_pos_of_left hσa
    · exact ae_dist_pos_of_right hσa
  have hlog : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (m i) := by
    intro i _
    fin_cases i
    · exact integrable_log_dist_of_isRegular_left hμ hRν
    · exact integrable_log_dist_circle_right hRμ
    · exact integrable_log_dist_circle_left hRν
    · exact integrable_log_dist_circle_right ae_circleMeasure_norm_le
  have hmass : ∑ i ∈ (Finset.univ : Finset (Fin 4)), c i * (m i).real univ = 0 := by
    simp only [Fin.sum_univ_four, hm, hc, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      real_prod_univ, hσ1]
    ring
  obtain ⟨hI, hE⟩ := frullani_comb Finset.univ m hfin c hpos hlog hmass
  have e : framePsi μ ν = fun t => Real.pi *
      ∑ i ∈ (Finset.univ : Finset (Fin 4)), c i * ∫ p, heatKernel t p.1 p.2 ∂(m i) := by
    funext t
    simp only [framePsi, heatPair, Fin.sum_univ_four, hm, hc, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  refine ⟨e ▸ hI, ?_⟩
  rw [e, hE]
  simp only [logPair, Fin.sum_univ_four, hm, hc, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- `L(μ ⊗ σ) = ∫ log⁺|u| μ(du)`. -/
lemma logPair_prod_circle {α : Measure ℂ} [IsFiniteMeasure α] {R : ℝ}
    (hα : ∀ᵐ u ∂α, ‖u‖ ≤ R) :
    logPair (α.prod (circleMeasure 0 1)) = ∫ u, Real.posLog ‖u‖ ∂α := by
  unfold logPair
  rw [integral_prod _ (integrable_log_dist_circle_right hα)]
  simp only [integral_log_norm_sub_circleMeasure]

/-- `L(σ ⊗ ν) = ∫ log⁺|v| ν(dv)`. -/
lemma logPair_circle_prod {β : Measure ℂ} [IsFiniteMeasure β] {R : ℝ}
    (hβ : ∀ᵐ v ∂β, ‖v‖ ≤ R) :
    logPair ((circleMeasure 0 1).prod β) = ∫ v, Real.posLog ‖v‖ ∂β := by
  unfold logPair
  rw [integral_prod_symm _ (integrable_log_dist_circle_left hβ)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  have e : (fun u : ℂ => Real.log ‖u - v‖) = fun u => Real.log ‖v - u‖ := by
    funext u; rw [norm_sub_rev]
  rw [e, integral_log_norm_sub_circleMeasure]

/-- `L(σ ⊗ σ) = 0`. -/
lemma logPair_circle_circle :
    logPair ((circleMeasure 0 1).prod (circleMeasure 0 1)) = 0 := by
  rw [logPair_prod_circle ae_circleMeasure_norm_le]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_circleMeasure_mem_sphere 0 1] with u hu
  simp only [Metric.mem_sphere, dist_zero_right, abs_one] at hu
  simp [hu]

/-- The energy in terms of `L(μ ⊗ ν)` and the one-variable terms. -/
theorem energy_eq_logPair {μ ν : Measure ℂ} (hμ : IsRegular μ) (hν : IsRegular ν) :
    energy μ ν = -logPair (μ.prod ν) + ν.real univ * ∫ u, Real.posLog ‖u‖ ∂μ +
      μ.real univ * ∫ v, Real.posLog ‖v‖ ∂ν := by
  have := hμ.1
  have := hν.1
  obtain ⟨Rμ, -, hRμ⟩ := exists_ae_norm_le_of_isRegular hμ
  obtain ⟨Rν, -, hRν⟩ := exists_ae_norm_le_of_isRegular hν
  have hL := integrable_log_dist_of_isRegular_left hμ hRν
  have hpμ := integrable_posLog_norm hRμ
  have hpν := integrable_posLog_norm hRν
  have hG : ∀ z w : ℂ, kernelG z w = -Real.log ‖z - w‖ + Real.posLog ‖z‖ + Real.posLog ‖w‖ :=
    fun z w => by
      unfold kernelG
      rw [Real.posLog_eq_log_max_one (norm_nonneg z), Real.posLog_eq_log_max_one (norm_nonneg w)]
  have hinner : ∀ᵐ z ∂μ, ∫ w, kernelG z w ∂ν =
      -∫ w, Real.log ‖z - w‖ ∂ν + ν.real univ * Real.posLog ‖z‖ +
        ∫ w, Real.posLog ‖w‖ ∂ν := by
    filter_upwards [hL.prod_right_ae] with z hz
    simp only [hG]
    have i0 : Integrable (fun w => -Real.log ‖z - w‖) ν := hz.neg
    have i1 : Integrable (fun w => -Real.log ‖z - w‖ + Real.posLog ‖z‖) ν :=
      i0.add (integrable_const _)
    rw [integral_add i1 hpν, integral_add i0 (integrable_const _), integral_neg, integral_const,
      smul_eq_mul]
  unfold energy
  rw [integral_congr_ae hinner]
  have h1 : Integrable (fun z => ∫ w, Real.log ‖z - w‖ ∂ν) μ := hL.integral_prod_left
  have j0 : Integrable (fun z => -∫ w, Real.log ‖z - w‖ ∂ν) μ := h1.neg
  have j1 : Integrable (fun z => ν.real univ * Real.posLog ‖z‖) μ := hpμ.const_mul _
  have j2 : Integrable (fun z => -∫ w, Real.log ‖z - w‖ ∂ν + ν.real univ * Real.posLog ‖z‖) μ :=
    j0.add j1
  rw [integral_add j2 (integrable_const _), integral_add j0 j1, integral_neg, integral_const_mul,
    integral_const, smul_eq_mul]
  unfold logPair
  rw [integral_prod _ hL]

/-- **The heat-kernel representation of the energy.** -/
theorem integral_framePsi {μ ν : Measure ℂ} (hμ : IsRegular μ) (hν : IsRegular ν) :
    ∫ t in Ioi 0, framePsi μ ν t = energy μ ν := by
  have := hμ.1
  have := hν.1
  obtain ⟨Rμ, -, hRμ⟩ := exists_ae_norm_le_of_isRegular hμ
  obtain ⟨Rν, -, hRν⟩ := exists_ae_norm_le_of_isRegular hν
  rw [(framePsi_frullani hμ hν).2, energy_eq_logPair hμ hν, logPair_prod_circle hRμ,
    logPair_circle_prod hRν, logPair_circle_circle]
  ring

theorem integrableOn_framePsi {μ ν : Measure ℂ} (hμ : IsRegular μ) (hν : IsRegular ν) :
    IntegrableOn (framePsi μ ν) (Ioi 0) :=
  (framePsi_frullani hμ hν).1

end WNFrame
end GaussianLQG
