import GaussianLQG.Field.Frame.Circle
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Logarithmic integrability for regular measures (blueprint `lem:energy-finite`)

For the frame construction we need `log|u − v| ∈ L¹(α ⊗ β)` and `α ⊗ β (diagonal) = 0` for the
four pairs `α, β ∈ {μ, ν, σ}` with `μ, ν` regular and `σ` the uniform measure on `∂𝔻`.

* `exists_ae_norm_le_of_isRegular`: a regular measure is carried by a closed ball. The ball-mass
  bound in `ℝ≥0∞` form and the absence of atoms are `IsRegular.exists_ballBound` and
  `IsRegular.measure_singleton` (`GaussianLQG/Energy/Measures.lean`).
* `lintegral_ofReal_negLog_le`: `∫ log⁺ (1/|u − v|) μ(du) ≤ C/α` (layer cake).
* `integrable_log_dist_of_isRegular_left`: `log|u − v| ∈ L¹(μ ⊗ ν)` for regular `μ` and finite
  compactly supported `ν`.
* `integrable_log_dist_circle_right`, `integrable_log_dist_circle_left`: the same with one factor
  equal to `σ`, via `∫ |log|u − v|| σ(dv) = 2 ∫ log⁺|u − v| σ(dv) − log⁺|u|`.
* `ae_dist_pos_of_left`, `ae_dist_pos_of_right`: the diagonal is null if one factor has no atoms.

This is a local version of the energy-finiteness lemma (blueprint `lem:energy-finite`) for the
frame construction; it lives in the namespace `GaussianLQG.WNFrame` to avoid clashes with the
energy package.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG
namespace WNFrame

/-! ## Regular measures -/

variable {μ : Measure ℂ}

/-- A regular measure is carried by a closed ball. -/
lemma exists_ae_norm_le_of_isRegular (hμ : IsRegular μ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ u ∂μ, ‖u‖ ≤ R :=
  let ⟨R, hR, h⟩ := hμ.exists_support
  ⟨R, by linarith, ae_norm_le_of_compl_closedBall_eq_zero h⟩

/-! ## The layer-cake bound -/

/-- `|log x| ≤ max 0 (-log x) + x` for `x ≥ 0`. -/
lemma abs_log_le_max_neg_log_add {x : ℝ} (hx : 0 ≤ x) :
    |Real.log x| ≤ max 0 (-Real.log x) + x := by
  rcases le_total 0 (Real.log x) with h | h
  · rw [abs_of_nonneg h]
    have := Real.log_le_self hx
    have := le_max_left 0 (-Real.log x)
    linarith
  · rw [abs_of_nonpos h]
    have := le_max_right 0 (-Real.log x)
    linarith

/-- **Layer cake.** If `μ(B_r(u)) ≤ C r^α` for `0 < r ≤ 1`, then
`∫ log⁺(1/|u − v|) μ(du) ≤ C/α`. -/
lemma lintegral_ofReal_negLog_le {μ : Measure ℂ} {C α : ℝ} (hC : 0 ≤ C) (hα : 0 < α)
    (hb : ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 → μ (Metric.ball u r) ≤ ENNReal.ofReal (C * r ^ α))
    (v : ℂ) :
    ∫⁻ u, ENNReal.ofReal (max 0 (-Real.log ‖u - v‖)) ∂μ ≤ ENNReal.ofReal (C / α) := by
  rw [lintegral_eq_lintegral_meas_lt (f := fun u => max 0 (-Real.log ‖u - v‖)) μ
    (Eventually.of_forall fun u => le_max_left _ _) (by fun_prop)]
  have hint : IntegrableOn (fun s : ℝ => C * Real.exp (-α * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hα).const_mul C
  calc ∫⁻ s in Ioi 0, μ {u | s < max 0 (-Real.log ‖u - v‖)}
      ≤ ∫⁻ s in Ioi 0, ENNReal.ofReal (C * Real.exp (-α * s)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
        have hs0 : 0 < s := hs
        have hsub : {u | s < max 0 (-Real.log ‖u - v‖)} ⊆ Metric.ball v (Real.exp (-s)) := by
          intro u hu
          simp only [mem_ofPred_eq] at hu
          have h1 : s < -Real.log ‖u - v‖ := by
            rcases le_total 0 (-Real.log ‖u - v‖) with h | h
            · rwa [max_eq_right h] at hu
            · rw [max_eq_left h] at hu; linarith
          have hpos : 0 < ‖u - v‖ := by
            rcases (norm_nonneg (u - v)).lt_or_eq with h | h
            · exact h
            · rw [← h, Real.log_zero, neg_zero] at h1; linarith
          rw [Metric.mem_ball, dist_eq_norm]
          rw [← Real.log_lt_iff_lt_exp hpos]
          linarith
        refine (measure_mono hsub).trans ((hb v _ (Real.exp_pos _)
          (Real.exp_le_one_iff.2 (by linarith))).trans (le_of_eq ?_))
        rw [← Real.exp_mul]
        congr 3; ring
    _ = ENNReal.ofReal (C / α) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun s => by positivity), integral_const_mul]
        congr 1
        have h := integral_exp_mul_Ioi (a := -α) (by linarith) 0
        simp only [mul_zero, Real.exp_zero] at h
        rw [h]
        field_simp

/-! ## Integrability of `log|u − v|` -/

/-- `log|u − v| ∈ L¹(μ ⊗ ν)` for regular `μ` and finite `ν` carried by a ball. -/
theorem integrable_log_dist_of_isRegular_left {μ ν : Measure ℂ} (hμ : IsRegular μ)
    [IsFiniteMeasure ν] {R' : ℝ} (hν : ∀ᵐ v ∂ν, ‖v‖ ≤ R') :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (μ.prod ν) := by
  have := hμ.1
  obtain ⟨R, -, hR⟩ := exists_ae_norm_le_of_isRegular hμ
  obtain ⟨C, α, hα, hC, hb⟩ := hμ.exists_ballBound
  have hm : Measurable fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖ := by fun_prop
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hm.enorm.aemeasurable]
  set K : ℝ≥0∞ := ENNReal.ofReal (C / α) + μ univ * ENNReal.ofReal (R + R') with hK
  have hKt : K < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
    ENNReal.mul_lt_top (measure_lt_top μ univ) ENNReal.ofReal_lt_top⟩
  have hinner : ∀ᵐ v ∂ν, ∫⁻ u, ‖Real.log ‖(u, v).1 - (u, v).2‖‖ₑ ∂μ ≤ K := by
    filter_upwards [hν] with v hv
    calc ∫⁻ u, ‖Real.log ‖(u, v).1 - (u, v).2‖‖ₑ ∂μ
        ≤ ∫⁻ u, (ENNReal.ofReal (max 0 (-Real.log ‖u - v‖)) + ENNReal.ofReal (R + R')) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hR] with u hu
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_left _ _)
            (by linarith [norm_nonneg u, norm_nonneg v])]
          refine ENNReal.ofReal_le_ofReal ((abs_log_le_max_neg_log_add (norm_nonneg _)).trans ?_)
          have := norm_sub_le u v
          linarith
      _ = ∫⁻ u, ENNReal.ofReal (max 0 (-Real.log ‖u - v‖)) ∂μ +
            μ univ * ENNReal.ofReal (R + R') := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, mul_comm]
      _ ≤ K := by
          rw [hK]
          gcongr
          exact lintegral_ofReal_negLog_le hC hα hb v
  calc ∫⁻ v, ∫⁻ u, ‖Real.log ‖(u, v).1 - (u, v).2‖‖ₑ ∂μ ∂ν ≤ ∫⁻ _, K ∂ν := lintegral_mono_ae hinner
    _ = K * ν univ := lintegral_const K
    _ < ∞ := ENNReal.mul_lt_top hKt (measure_lt_top ν univ)

/-- `|log x| = 2 log⁺ x − log x`. -/
lemma abs_log_eq_two_posLog_sub (x : ℝ) : |Real.log x| = 2 * Real.posLog x - Real.log x := by
  unfold Real.posLog
  rcases le_total 0 (Real.log x) with h | h
  · rw [max_eq_right h, abs_of_nonneg h]; ring
  · rw [max_eq_left h, abs_of_nonpos h]; ring

/-- `log|u − v| ∈ L¹(α ⊗ σ)` for finite `α` carried by a ball. -/
theorem integrable_log_dist_circle_right {α : Measure ℂ} [IsFiniteMeasure α] {R : ℝ}
    (hα : ∀ᵐ u ∂α, ‖u‖ ≤ R) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (α.prod (circleMeasure 0 1)) := by
  have hm : Measurable fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖ := by fun_prop
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun u => integrable_log_norm_sub_circleMeasure u, ?_⟩
  refine Integrable.mono' (integrable_const (2 * (R + 1)))
    hm.aestronglyMeasurable.norm.integral_prod_right' ?_
  filter_upwards [hα] with u hu
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hS := ae_circleMeasure_mem_sphere 0 1
  have hpl_le : ∀ᵐ v ∂(circleMeasure 0 1), Real.posLog ‖u - v‖ ≤ R + 1 := by
    filter_upwards [hS] with v hv
    have hv1 : ‖v‖ = 1 := by simpa using hv
    refine (Real.posLog_le_abs _).trans ?_
    rw [abs_norm]
    linarith [norm_sub_le u v]
  have hpl : Integrable (fun v => Real.posLog ‖u - v‖) (circleMeasure 0 1) := by
    refine Integrable.mono' (integrable_const (R + 1))
      (by fun_prop : Measurable fun v : ℂ => Real.posLog ‖u - v‖).aestronglyMeasurable ?_
    filter_upwards [hpl_le] with v hv
    rwa [Real.norm_of_nonneg Real.posLog_nonneg]
  have e : ∀ v : ℂ, ‖Real.log ‖(u, v).1 - (u, v).2‖‖ =
      2 * Real.posLog ‖u - v‖ - Real.log ‖u - v‖ := fun v => by
    rw [Real.norm_eq_abs, abs_log_eq_two_posLog_sub]
  simp_rw [e]
  rw [integral_sub (hpl.const_mul 2) (integrable_log_norm_sub_circleMeasure u), integral_const_mul,
    integral_log_norm_sub_circleMeasure]
  have h1 : ∫ v, Real.posLog ‖u - v‖ ∂(circleMeasure 0 1) ≤ R + 1 := by
    refine (integral_mono_ae hpl (integrable_const (R + 1)) hpl_le).trans (le_of_eq ?_)
    simp
  have h2 : 0 ≤ Real.posLog ‖u‖ := Real.posLog_nonneg
  linarith

/-- `log|u − v| ∈ L¹(σ ⊗ ν)` for finite `ν` carried by a ball. -/
theorem integrable_log_dist_circle_left {ν : Measure ℂ} [IsFiniteMeasure ν] {R : ℝ}
    (hν : ∀ᵐ v ∂ν, ‖v‖ ≤ R) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((circleMeasure 0 1).prod ν) := by
  have h := (integrable_log_dist_circle_right hν).swap
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, norm_sub_rev]

/-! ## The diagonal is null -/

lemma measurableSet_diag_complex : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} :=
  measurableSet_eq_fun measurable_fst measurable_snd

lemma setOf_not_dist_pos : {p : ℂ × ℂ | ¬ 0 < ‖p.1 - p.2‖} = {p : ℂ × ℂ | p.1 = p.2} := by
  ext p
  simp only [mem_ofPred_eq, norm_pos_iff, ne_eq, sub_eq_zero, not_not]

lemma ae_dist_pos_of_right {μ ν : Measure ℂ} [SFinite ν] (hν : ∀ u, ν {u} = 0) :
    ∀ᵐ p ∂(μ.prod ν), 0 < ‖p.1 - p.2‖ := by
  rw [ae_iff, setOf_not_dist_pos, Measure.prod_apply measurableSet_diag_complex]
  have e : ∀ x : ℂ, Prod.mk x ⁻¹' {p : ℂ × ℂ | p.1 = p.2} = {x} := fun x => by
    ext y; simp [eq_comm]
  simp only [e, hν, lintegral_zero]

lemma ae_dist_pos_of_left {μ ν : Measure ℂ} [SFinite μ] [SFinite ν] (hμ : ∀ v, μ {v} = 0) :
    ∀ᵐ p ∂(μ.prod ν), 0 < ‖p.1 - p.2‖ := by
  rw [ae_iff, setOf_not_dist_pos, Measure.prod_apply_symm measurableSet_diag_complex]
  have e : ∀ y : ℂ, (fun x : ℂ => (x, y)) ⁻¹' {p : ℂ × ℂ | p.1 = p.2} = {y} := fun y => by
    ext x; simp
  simp only [e, hμ, lintegral_zero]

/-! ## Compatibility names (cleanup W15)

Old forms of `IsRegular.exists_ballBound` (with the conjuncts `0 ≤ C` and `0 < α` swapped) and of
`IsRegular.measure_singleton`, kept so that code written against them still compiles. -/

theorem exists_ball_bound_of_isRegular (hμ : IsRegular μ) :
    ∃ C α : ℝ, 0 ≤ C ∧ 0 < α ∧ ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ (Metric.ball u r) ≤ ENNReal.ofReal (C * r ^ α) :=
  let ⟨C, α, hα, hC, hb⟩ := hμ.exists_ballBound
  ⟨C, α, hC, hα, hb⟩

alias measure_singleton_of_isRegular := IsRegular.measure_singleton

end WNFrame
end GaussianLQG
