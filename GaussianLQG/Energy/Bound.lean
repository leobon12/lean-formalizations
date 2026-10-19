import GaussianLQG.Energy.Basic

/-!
# The energy bound (blueprint Lemma `lem:energy-bound`, source (2.12))

Let `ν` be a Borel probability measure supported in `closedBall 0 T`, `T ≥ 1`, with
`ν(B_r(u)) ≤ B r^{1/2}` for all `u` and `r ∈ (0, 1]`, where `B ≥ 1`. Then `ν` is regular and
`ℰ(ν, ν) ≤ 2 log B + 2 + 2 log T` (`isRegular_and_energy_le`).

Proof: `-log|z-w| ≤ log⁺(1/|z-w|)`, whose `ν ⊗ ν`-integral is at most
`∫_0^∞ min(1, B e^{-t/2}) dt = 2 log B + 2` by the layer-cake formula
(`lintegral_posLog_one_div_le_of_sqrt`), and `2 ∫ log|z|₊ dν ≤ 2 log T`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal Real

namespace GaussianLQG

/-- `-log x ≤ log⁺(1/x)` for every real `x`. -/
theorem neg_log_le_posLog_one_div (x : ℝ) : -Real.log x ≤ log⁺ (1 / x) := by
  rw [one_div, ← Real.log_inv, Real.posLog_apply]
  exact le_max_right _ _

/-- Blueprint Lemma `lem:energy-bound`. -/
theorem isRegular_and_energy_le {ν : Measure ℂ} [IsProbabilityMeasure ν] {T B : ℝ} (hT : 1 ≤ T)
    (hsupp : ν (closedBall (0 : ℂ) T)ᶜ = 0) (hB : 1 ≤ B)
    (hball : ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 → (ν (ball u r)).toReal ≤ B * r ^ (1 / 2 : ℝ)) :
    IsRegular ν ∧ energy ν ν ≤ 2 * Real.log B + 2 + 2 * Real.log T := by
  have hreg : IsRegular ν := ⟨inferInstance, ⟨T, hsupp⟩, B, 1 / 2, by norm_num, hball⟩
  refine ⟨hreg, ?_⟩
  have hb : ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ν (ball u r) ≤ ENNReal.ofReal (B * r ^ (1 / 2 : ℝ)) := by
    intro u r hr hr1
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν _)]
    exact ENNReal.ofReal_le_ofReal (hball u r hr hr1)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  -- the logarithmic part
  have hL : logEnergy ν ν ≤ 2 * Real.log B + 2 := by
    rw [logEnergy_eq_integral_prod hreg hreg]
    have hnn : 0 ≤ᵐ[ν.prod ν] fun p : ℂ × ℂ => log⁺ (1 / ‖p.1 - p.2‖) :=
      ae_of_all _ fun p => Real.posLog_nonneg
    have hint : Integrable (fun p : ℂ × ℂ => log⁺ (1 / ‖p.1 - p.2‖)) (ν.prod ν) :=
      hreg.integrable_posLog_div hreg one_pos le_rfl
    have hlin : ∫⁻ p, ENNReal.ofReal (log⁺ (1 / ‖p.1 - p.2‖)) ∂(ν.prod ν) ≤
        ENNReal.ofReal (2 * Real.log B + 2) := by
      have h := lintegral_prod_le_of_forall (μ := ν) (ν := ν)
        (f := fun p : ℂ × ℂ => ENNReal.ofReal (log⁺ (1 / ‖p.1 - p.2‖))) (by fun_prop)
        fun z => lintegral_posLog_one_div_le_of_sqrt ν z hB (hb z)
      rwa [measure_univ, one_mul] at h
    calc ∫ p, -Real.log ‖p.1 - p.2‖ ∂(ν.prod ν)
        ≤ ∫ p, log⁺ (1 / ‖p.1 - p.2‖) ∂(ν.prod ν) :=
          integral_mono (hreg.integrable_neg_log_norm_sub hreg) hint
            fun p => neg_log_le_posLog_one_div _
      _ = (∫⁻ p, ENNReal.ofReal (log⁺ (1 / ‖p.1 - p.2‖)) ∂(ν.prod ν)).toReal :=
          integral_eq_lintegral_of_nonneg_ae hnn hint.aestronglyMeasurable
      _ ≤ (ENNReal.ofReal (2 * Real.log B + 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
      _ = 2 * Real.log B + 2 := ENNReal.toReal_ofReal (by positivity)
  -- the one-variable part
  have hA : ∫ x, Real.log (max 1 ‖x‖) ∂ν ≤ Real.log T := by
    calc ∫ x, Real.log (max 1 ‖x‖) ∂ν ≤ ∫ _x, Real.log T ∂ν := by
          refine integral_mono_ae hreg.integrable_log_max_one_norm (integrable_const _) ?_
          filter_upwards [ae_norm_le_of_compl_closedBall_eq_zero hsupp] with x hx
          exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _)) (max_le hT hx)
      _ = Real.log T := by rw [integral_const, probReal_univ, one_smul]
  rw [energy_eq_logEnergy_add hreg hreg, probReal_univ, one_mul]
  linarith

end GaussianLQG
