import GaussianLQG.Energy.Measures
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Layer-cake bounds for the logarithmic singularity

The analytic core of blueprint Lemmas `lem:energy-finite`, `lem:energy-bound` and `lem:coupling`:
by the layer-cake formula,
`∫ log⁺(ρ/|z-w|) ν(dw) = ∫_0^∞ ν{w : |z-w| < ρ e^{-t}} dt`, so a ball-mass bound for `ν` controls
the truncated logarithmic potential.

* `lintegral_posLog_div_le`: the general layer-cake inequality.
* `lintegral_posLog_div_le_of_ballBound`: `ν(B_r(z)) ≤ B r^α` for `r ≤ 1` and `ρ ≤ 1` give
  `∫ log⁺(ρ/|z-w|) dν(w) ≤ B ρ^α / α`.
* `lintegral_posLog_one_div_le_of_sqrt`: for a probability measure with `ν(B_r(z)) ≤ B r^{1/2}`,
  `B ≥ 1`, `∫ log⁺(1/|z-w|) dν(w) ≤ 2 log B + 2` (this uses `ν(B_r(z)) ≤ min(1, B r^{1/2})`).
* Product versions and integrability on `μ ⊗ ν`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal Real

namespace GaussianLQG

@[fun_prop]
theorem measurable_posLog_div_norm_sub (ρ : ℝ) :
    Measurable fun p : ℂ × ℂ => log⁺ (ρ / ‖p.1 - p.2‖) := by
  fun_prop

/-- Layer cake for the logarithmic singularity: if `ν(B_{ρ e^{-t}}(z)) ≤ g t` for all `t > 0`,
then `∫ log⁺(ρ/|z-w|) dν(w) ≤ ∫_0^∞ g`. -/
theorem lintegral_posLog_div_le (ν : Measure ℂ) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {g : ℝ → ℝ≥0∞}
    (hg : ∀ t : ℝ, 0 < t → ν (ball z (ρ * Real.exp (-t))) ≤ g t) :
    ∫⁻ w, ENNReal.ofReal (log⁺ (ρ / ‖z - w‖)) ∂ν ≤ ∫⁻ t in Ioi 0, g t := by
  have hm : Measurable fun w : ℂ => log⁺ (ρ / ‖z - w‖) := by fun_prop
  rw [lintegral_eq_lintegral_meas_lt ν (ae_of_all _ fun w => Real.posLog_nonneg) hm.aemeasurable]
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  have ht : 0 < t := ht
  refine (measure_mono fun w hw => ?_).trans (hg t ht)
  simp only [mem_ofPred_eq] at hw
  have h1 : t < Real.log (ρ / ‖z - w‖) := by
    rw [Real.posLog_apply] at hw
    rcases lt_max_iff.1 hw with h | h
    · linarith
    · exact h
  have hpos : 0 < ‖z - w‖ := by
    rcases (norm_nonneg (z - w)).lt_or_eq with h | h
    · exact h
    · rw [← h, div_zero, Real.log_zero] at h1
      linarith
  rw [Real.lt_log_iff_exp_lt (div_pos hρ hpos), lt_div_iff₀ hpos] at h1
  rw [mem_ball', dist_eq_norm, Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos t)]
  linarith [mul_comm (Real.exp t) ‖z - w‖]

/-- `∫_0^∞ c e^{-α t} dt = c/α` in `ℝ≥0∞`. -/
theorem lintegral_ofReal_mul_exp_Ioi {c α : ℝ} (hc : 0 ≤ c) (hα : 0 < α) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (c * Real.exp (-α * t)) = ENNReal.ofReal (c / α) := by
  have hint : IntegrableOn (fun t => c * Real.exp (-α * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => by positivity),
    integral_const_mul, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero]
  congr 1
  field_simp

/-- Layer cake with a power-law ball-mass bound: if `ν(B_r(z)) ≤ B r^α` for `0 < r ≤ 1` and
`0 < ρ ≤ 1`, then `∫ log⁺(ρ/|z-w|) dν(w) ≤ B ρ^α / α`. -/
theorem lintegral_posLog_div_le_of_ballBound (ν : Measure ℂ) (z : ℂ) {ρ α B : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hα : 0 < α) (hB : 0 ≤ B)
    (hb : ∀ r : ℝ, 0 < r → r ≤ 1 → ν (ball z r) ≤ ENNReal.ofReal (B * r ^ α)) :
    ∫⁻ w, ENNReal.ofReal (log⁺ (ρ / ‖z - w‖)) ∂ν ≤ ENNReal.ofReal (B * ρ ^ α / α) := by
  have hρα : 0 ≤ B * ρ ^ α := mul_nonneg hB (Real.rpow_nonneg hρ.le _)
  refine (lintegral_posLog_div_le ν z hρ
    (g := fun t => ENNReal.ofReal (B * ρ ^ α * Real.exp (-α * t))) fun t ht => ?_).trans
    (lintegral_ofReal_mul_exp_Ioi hρα hα).le
  have hr : 0 < ρ * Real.exp (-t) := mul_pos hρ (Real.exp_pos _)
  have hr1 : ρ * Real.exp (-t) ≤ 1 := by
    have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    calc ρ * Real.exp (-t) ≤ 1 * 1 := mul_le_mul hρ1 he (Real.exp_pos _).le zero_le_one
      _ = 1 := one_mul 1
  refine (hb _ hr hr1).trans (le_of_eq ?_)
  have e : B * (ρ * Real.exp (-t)) ^ α = B * ρ ^ α * Real.exp (-α * t) := by
    rw [Real.mul_rpow hρ.le (Real.exp_pos _).le, ← Real.exp_mul,
      show -t * α = -α * t by ring, mul_assoc]
  rw [e]

/-- `∫_c^∞ B e^{-t/2} dt = 2 B e^{-c/2}` in `ℝ≥0∞`. -/
theorem lintegral_ofReal_mul_exp_half_Ioi {B : ℝ} (hB : 0 ≤ B) (c : ℝ) :
    ∫⁻ t in Ioi c, ENNReal.ofReal (B * Real.exp (-(1 / 2) * t)) =
      ENNReal.ofReal (2 * B * Real.exp (-(1 / 2) * c)) := by
  have hint : IntegrableOn (fun t => B * Real.exp (-(1 / 2) * t)) (Ioi c) :=
    (integrableOn_exp_mul_Ioi (by norm_num) c).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => by positivity),
    integral_const_mul, integral_exp_mul_Ioi (by norm_num) c]
  congr 1
  ring

/-- Layer cake for the energy bound: for a probability measure with `ν(B_r(z)) ≤ B r^{1/2}`,
`0 < r ≤ 1`, `B ≥ 1`, one has `∫ log⁺(1/|z-w|) dν(w) ≤ 2 log B + 2`
(blueprint `lem:energy-bound`: `∫_0^∞ min(1, B e^{-t/2}) dt = 2 log B + 2`). -/
theorem lintegral_posLog_one_div_le_of_sqrt (ν : Measure ℂ) [IsProbabilityMeasure ν] (z : ℂ)
    {B : ℝ} (hB : 1 ≤ B)
    (hb : ∀ r : ℝ, 0 < r → r ≤ 1 → ν (ball z r) ≤ ENNReal.ofReal (B * r ^ (1 / 2 : ℝ))) :
    ∫⁻ w, ENNReal.ofReal (log⁺ (1 / ‖z - w‖)) ∂ν ≤ ENNReal.ofReal (2 * Real.log B + 2) := by
  have hB0 : 0 < B := by linarith
  set c := 2 * Real.log B with hc_def
  have hc : 0 ≤ c := by
    have := Real.log_nonneg hB
    positivity
  refine (lintegral_posLog_div_le ν z one_pos (g := fun t => ν (ball z (1 * Real.exp (-t))))
    fun t _ => le_rfl).trans ?_
  have hcover : Ioi (0 : ℝ) ⊆ Ioc 0 c ∪ Ioi c := by
    intro t ht
    rcases le_or_gt t c with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr h
  have hexp : Real.exp (-(1 / 2) * c) = B⁻¹ := by
    rw [hc_def, show -(1 / 2) * (2 * Real.log B) = -Real.log B by ring, Real.exp_neg,
      Real.exp_log hB0]
  calc ∫⁻ t in Ioi 0, ν (ball z (1 * Real.exp (-t)))
      ≤ ∫⁻ t in Ioc 0 c ∪ Ioi c, ν (ball z (1 * Real.exp (-t))) := lintegral_mono_set hcover
    _ ≤ (∫⁻ t in Ioc 0 c, ν (ball z (1 * Real.exp (-t)))) +
          ∫⁻ t in Ioi c, ν (ball z (1 * Real.exp (-t))) :=
        lintegral_union_le (fun t => ν (ball z (1 * Real.exp (-t)))) (Ioc 0 c) (Ioi c)
    _ ≤ (∫⁻ _ in Ioc 0 c, 1) + ∫⁻ t in Ioi c, ENNReal.ofReal (B * Real.exp (-(1 / 2) * t)) := by
        refine add_le_add (setLIntegral_mono' measurableSet_Ioc fun t _ => prob_le_one (μ := ν))
          (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_)
        have ht : c < t := ht
        have hr : 0 < 1 * Real.exp (-t) := by positivity
        have hr1 : 1 * Real.exp (-t) ≤ 1 := by
          rw [one_mul, Real.exp_le_one_iff]
          linarith
        refine (hb _ hr hr1).trans (le_of_eq ?_)
        rw [one_mul, ← Real.exp_mul, show -t * (1 / 2) = -(1 / 2) * t by ring]
    _ = ENNReal.ofReal c + ENNReal.ofReal 2 := by
        rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero,
          lintegral_ofReal_mul_exp_half_Ioi hB0.le, hexp]
        congr 2
        field_simp
    _ = ENNReal.ofReal (2 * Real.log B + 2) := (ENNReal.ofReal_add hc (by norm_num)).symm

/-- Tonelli: a uniform bound on the inner lower integrals bounds the integral over `μ ⊗ ν`. -/
theorem lintegral_prod_le_of_forall {μ ν : Measure ℂ} [SFinite ν] {f : ℂ × ℂ → ℝ≥0∞}
    (hf : AEMeasurable f (μ.prod ν)) {M : ℝ≥0∞} (h : ∀ z, ∫⁻ w, f (z, w) ∂ν ≤ M) :
    ∫⁻ p, f p ∂(μ.prod ν) ≤ μ univ * M := by
  rw [lintegral_prod _ hf]
  calc ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ ≤ ∫⁻ _, M ∂μ := lintegral_mono h
    _ = μ univ * M := by rw [lintegral_const, mul_comm]

/-- `log⁺(ρ/|x-y|)` is integrable on `μ ⊗ ν` when `μ` is finite and `ν` has a power-law
ball-mass bound, for `0 < ρ ≤ 1`; its integral is at most `μ(ℂ) B ρ^α / α`. -/
theorem integrable_posLog_div_prod {μ ν : Measure ℂ} [IsFiniteMeasure μ] [SFinite ν]
    {ρ α B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hα : 0 < α) (hB : 0 ≤ B)
    (hb : ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 → ν (ball u r) ≤ ENNReal.ofReal (B * r ^ α)) :
    Integrable (fun p : ℂ × ℂ => log⁺ (ρ / ‖p.1 - p.2‖)) (μ.prod ν) ∧
      ∫ p, log⁺ (ρ / ‖p.1 - p.2‖) ∂(μ.prod ν) ≤ μ.real univ * (B * ρ ^ α / α) := by
  have hnn : 0 ≤ᵐ[μ.prod ν] fun p : ℂ × ℂ => log⁺ (ρ / ‖p.1 - p.2‖) :=
    ae_of_all _ fun p => Real.posLog_nonneg
  have hm : Measurable fun p : ℂ × ℂ => log⁺ (ρ / ‖p.1 - p.2‖) :=
    measurable_posLog_div_norm_sub ρ
  have hlin : ∫⁻ p, ENNReal.ofReal (log⁺ (ρ / ‖p.1 - p.2‖)) ∂(μ.prod ν) ≤
      μ univ * ENNReal.ofReal (B * ρ ^ α / α) :=
    lintegral_prod_le_of_forall (by fun_prop) fun z =>
      lintegral_posLog_div_le_of_ballBound ν z hρ hρ1 hα hB (hb z)
  have hfin : μ univ * ENNReal.ofReal (B * ρ ^ α / α) < ∞ :=
    ENNReal.mul_lt_top (measure_lt_top μ _) ENNReal.ofReal_lt_top
  refine ⟨⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2
    (hlin.trans_lt hfin)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable]
  calc (∫⁻ p, ENNReal.ofReal (log⁺ (ρ / ‖p.1 - p.2‖)) ∂(μ.prod ν)).toReal
      ≤ (μ univ * ENNReal.ofReal (B * ρ ^ α / α)).toReal :=
        ENNReal.toReal_mono hfin.ne hlin
    _ = μ.real univ * (B * ρ ^ α / α) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), measureReal_def]

end GaussianLQG
