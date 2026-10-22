import HigherDimLQGMetric.ConvField.KernelUniform
import HigherDimLQGMetric.ConvField.RadialWeightIntegrable

/-! Integrability of the common radial decay envelope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

def l2b_decayEnvelope (d : ℕ) (r : ℝ) : ℝ :=
  (1 + max r 0) ^ (-((d : ℝ) + 1))

theorem l2b_continuous_decayEnvelope (d : ℕ) : Continuous (l2b_decayEnvelope d) := by
  exact (continuous_const.add (continuous_id.sup continuous_const)).rpow_const
    (fun r => Or.inl (by
      change 1 + max r 0 ≠ 0
      have := le_max_right r (0 : ℝ)
      linarith))

theorem l2b_log_two_add_norm_le {d : ℕ} (x : Rd d) :
    Real.log (2 + ‖x‖) ≤ 4 * (1 + ‖x‖) ^ ((1 / 2 : ℝ)) := by
  have h := Real.log_le_rpow_div (x := 2 + ‖x‖) (by positivity)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hp : (2 + ‖x‖) ^ ((1 / 2 : ℝ)) ≤
      2 * (1 + ‖x‖) ^ ((1 / 2 : ℝ)) := by
    have hle : 2 + ‖x‖ ≤ 4 * (1 + ‖x‖) := by nlinarith [norm_nonneg x]
    have hr := Real.rpow_le_rpow (by positivity : 0 ≤ 2 + ‖x‖) hle
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
      (by positivity : 0 ≤ 1 + ‖x‖)] at hr
    norm_num at hr ⊢
    exact hr
  calc
    Real.log (2 + ‖x‖) ≤ (2 + ‖x‖) ^ ((1 / 2 : ℝ)) / (1 / 2 : ℝ) := h
    _ = 2 * (2 + ‖x‖) ^ ((1 / 2 : ℝ)) := by ring
    _ ≤ 4 * (1 + ‖x‖) ^ ((1 / 2 : ℝ)) := by linarith

theorem l2b_integrable_log_decayEnvelope (d : ℕ) :
    Integrable (fun x : Rd d =>
      Real.log (2 + ‖x‖) * l2b_decayEnvelope d ‖x‖) := by
  have hbase : Integrable (fun x : Rd d =>
      4 * (1 + ‖x‖) ^ (-((d : ℝ) + 1 / 2))) := by
    have hi : Integrable (fun x : Rd d =>
        (1 + ‖x‖) ^ (-((d : ℝ) + 1 / 2))) := by
      apply integrable_one_add_norm (μ := volume)
      simp only [finrank_euclideanSpace_fin]
      norm_num
    exact hi.const_mul 4
  apply hbase.mono'
  · have hlogc : Continuous (fun x : Rd d => Real.log (2 + ‖x‖)) :=
      Continuous.log (by fun_prop) (by intro x; positivity)
    exact (hlogc.mul ((l2b_continuous_decayEnvelope d).comp continuous_norm)).aestronglyMeasurable
  · filter_upwards with x
    have hlog : 0 ≤ Real.log (2 + ‖x‖) :=
      Real.log_nonneg (by nlinarith [norm_nonneg x])
    have hr : 0 < 1 + ‖x‖ := by positivity
    simp only [l2b_decayEnvelope, max_eq_left (norm_nonneg x)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    change Real.log (2 + ‖x‖) * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) ≤ _
    calc
      _ ≤ (4 * (1 + ‖x‖) ^ ((1 / 2 : ℝ))) *
          (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
            gcongr
            exact l2b_log_two_add_norm_le x
      _ = 4 * (1 + ‖x‖) ^ (-((d : ℝ) + 1 / 2)) := by
        rw [mul_assoc, ← Real.rpow_add hr]
        congr 1
        ring_nf

theorem l2b_integrable_radial_decayEnvelope (d : ℕ) (hd : 2 ≤ d) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) * l2b_decayEnvelope d r)
      (Ioi (0 : ℝ)) := by
  haveI : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  have hv : Integrable (fun x : Rd d => l2b_decayEnvelope d ‖x‖) := by
    have hi : Integrable (fun x : Rd d => (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by
      apply integrable_one_add_norm (μ := volume)
      simp only [finrank_euclideanSpace_fin]
      norm_num
    convert hi using 1
    funext x
    simp only [l2b_decayEnvelope, max_eq_left (norm_nonneg x)]
  have hr := (integrable_fun_norm_addHaar (μ := (volume : Measure (Rd d)))
    (f := l2b_decayEnvelope d)).mp hv
  simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using hr

theorem l2b_integrable_radial_log_decayEnvelope (d : ℕ) (hd : 2 ≤ d) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) *
      (Real.log (2 + r) * l2b_decayEnvelope d r)) (Ioi (0 : ℝ)) := by
  haveI : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  have hr := (integrable_fun_norm_addHaar (μ := (volume : Measure (Rd d)))
    (f := fun r : ℝ => Real.log (2 + r) * l2b_decayEnvelope d r)).mp
      (l2b_integrable_log_decayEnvelope d)
  simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using hr

theorem l2b_integrable_radial_growth_decayEnvelope (d : ℕ) (hd : 2 ≤ d) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) *
      l2b_decayEnvelope d r * l2b_growthWeight r) (Ioi (0 : ℝ)) :=
  l2b_integrable_radial_growth_of_log hd (l2b_decayEnvelope d)
    (l2b_continuous_decayEnvelope d) (l2b_integrable_radial_decayEnvelope d hd)
    (l2b_integrable_radial_log_decayEnvelope d hd)

end HigherDimLQGMetric
