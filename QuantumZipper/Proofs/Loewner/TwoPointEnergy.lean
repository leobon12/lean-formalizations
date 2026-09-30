import QuantumZipper.Proofs.Loewner.TwoPoint
import QuantumZipper.Proofs.Zipper.WeldingUniqueness
import QuantumZipper.GFF.Kernels
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Energy modulus for pushed-forward folded circles (L2PT, part (E))

Task L2PT (`audits/2026-09-27-regcoord/AUDIT3.md` §1.3 (E)). For `W` continuous, `T ≥ 0`,
`f = revMap W T`, and folded circles `σ = fc(w,r)`, `σ' = fc(w',r')` with `r, r' ≥ r₀ > 0`,
`‖w‖ + r, ‖w'‖ + r' ≤ R`, `δ = ‖w − w'‖ + |r − r'| ≤ 1`:

`|kernelCov2 neumannH (ν, ν') (ν, ν')| ≤ C · δ^{1/12}`,  `ν = f_* σ`, `ν' = f_* σ'`
(`abs_kernelCov2_revMap_foldedCircle_le`), with `C` depending only on `W, T, r₀, R`.

**A. Log potentials of Frostman measures** (`κ` finite, `IsFrostman κ α C`, `0 < α ≤ 1`,
support in `‖y‖ ≤ B`): `logPot κ x = ∫ log ‖x − y‖ dκ(y)` is integrable, bounded by
`C/α + |log(‖x‖+B+1)|·κ(ℂ)` (`abs_logPot_le`) and Hölder:
`|logPot κ x − logPot κ x'| ≤ (κ(ℂ) + 4C/α)·‖x − x'‖^{α/2}` for `‖x − x'‖ ≤ 1`
(`abs_logPot_sub_le`). The Neumann potential `neuPot κ x = ∫ neumannH x y dκ(y)` equals
`−logPot κ x − logPot κ x̄` and inherits both bounds.

**B. Coupling.** `kernelCov neumannH (f_* fc(w,r)) κ = (2π)⁻¹ ∫_{[0,2π)} neuPot κ (F θ) dθ` with
`F θ = f (foldH (circleMap w r θ))`. Coupling the two circles at the same angle, the
displacement `‖F θ − F' θ‖` is `≤ δ√(R²+4T)/τ` off the strips `{|Im| < τ}` (two-point upper
bound), whose Lebesgue measure is `O(√τ)`; take `τ = √δ`.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real ENNReal ComplexConjugate

namespace QuantumZipper
namespace TwoPoint

/-! ## A. Log potentials of Frostman measures -/

section Potential

variable {κ : Measure ℂ} [IsFiniteMeasure κ] {α C : ℝ}

/-- `log⁺ (s / ‖x − y‖)`. -/
def logRatio (s : ℝ) (x y : ℂ) : ℝ := max (Real.log (s / ‖x - y‖)) 0

theorem logRatio_nonneg (s : ℝ) (x y : ℂ) : 0 ≤ logRatio s x y := le_max_right _ _

theorem measurable_logRatio (s : ℝ) (x : ℂ) : Measurable (logRatio s x) :=
  (Real.measurable_log.comp (measurable_const.div
    (measurable_const.sub measurable_id).norm)).max measurable_const

theorem frostman_ball_le (hF : IsFrostman κ α C) (hC : 0 ≤ C) (x : ℂ) {s : ℝ} (hs : 0 < s) :
    κ (Metric.closedBall x s) ≤ ENNReal.ofReal (C * s ^ α) :=
  (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 (hF x s hs)

theorem lintegral_logRatio_frostman (hF : IsFrostman κ α C) (hα : 0 < α) (hC : 0 ≤ C)
    (x : ℂ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ y, ENNReal.ofReal (logRatio s x y) ∂κ ≤ ENNReal.ofReal (C * s ^ α / α) := by
  have hnn : 0 ≤ᵐ[κ] logRatio s x := ae_of_all _ fun y => logRatio_nonneg s x y
  rw [lintegral_eq_lintegral_meas_lt _ hnn (measurable_logRatio s x).aemeasurable]
  have hC' : Integrable (fun t : ℝ => C * s ^ α * Real.exp (-α * t))
      (volume.restrict (Ioi 0)) :=
    (exp_neg_integrableOn_Ioi 0 hα).const_mul _
  have hval : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (C * s ^ α * Real.exp (-α * t)) =
      ENNReal.ofReal (C * s ^ α / α) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hC' (ae_of_all _ fun t => by positivity),
      integral_const_mul, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero,
      neg_div_neg_eq]
    congr 1; ring
  rw [← hval]
  refine setLIntegral_mono (ENNReal.measurable_ofReal.comp (measurable_const.mul
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)))) fun t (ht : 0 < t) => ?_
  have hsub : {y : ℂ | t < logRatio s x y} ⊆ Metric.closedBall x (s * Real.exp (-t)) := by
    intro y hy
    simp only [mem_setOf_eq, logRatio, lt_max_iff] at hy
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    rcases hy with hy | hy
    · rcases eq_or_lt_of_le (norm_nonneg (x - y)) with h0 | h0
      · rw [← h0, div_zero, Real.log_zero] at hy; linarith
      · have h1 := (Real.lt_log_iff_exp_lt (div_pos hs h0)).1 hy
        rw [lt_div_iff₀ h0] at h1
        rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos t)]
        linarith [mul_comm ‖x - y‖ (Real.exp t)]
    · linarith
  refine (measure_mono hsub).trans ((frostman_ball_le hF hC x (by positivity)).trans
    (le_of_eq ?_))
  congr 1
  rw [Real.mul_rpow hs.le (Real.exp_pos _).le, ← Real.exp_mul,
    show -t * α = -α * t by ring]
  ring

theorem integrable_logRatio (hF : IsFrostman κ α C) (hα : 0 < α) (hC : 0 ≤ C) (x : ℂ) {s : ℝ}
    (hs : 0 < s) : Integrable (logRatio s x) κ := by
  refine ⟨(measurable_logRatio s x).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => logRatio_nonneg s x y)]
  exact lt_of_le_of_lt (lintegral_logRatio_frostman hF hα hC x hs) ENNReal.ofReal_lt_top

theorem integral_logRatio_le (hF : IsFrostman κ α C) (hα : 0 < α) (hC : 0 ≤ C) (x : ℂ)
    {s : ℝ} (hs : 0 < s) : ∫ y, logRatio s x y ∂κ ≤ C * s ^ α / α := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => logRatio_nonneg s x y)
    (measurable_logRatio s x).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (lintegral_logRatio_frostman hF hα hC x hs)

theorem frostman_ae_ne (hF : IsFrostman κ α C) (hα : 0 < α) (hC : 0 ≤ C) (x : ℂ) :
    ∀ᵐ y ∂κ, y ≠ x := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  have hε' : (0 : ℝ) < ε := hε
  set t := ((ε : ℝ) / (C + 1)) ^ (1 / α) with ht
  have ht0 : 0 < t := by positivity
  have htα : t ^ α = ε / (C + 1) := by
    rw [ht, ← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one]
  have hsub : {y : ℂ | y = x} ⊆ Metric.closedBall x t := by
    intro y hy
    simp only [mem_setOf_eq] at hy
    rw [hy]; exact Metric.mem_closedBall_self ht0.le
  refine (measure_mono hsub).trans ((frostman_ball_le hF hC x ht0).trans ?_)
  rw [htα, ← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

theorem abs_log_le_logRatio_add {a D : ℝ} (ha : 0 ≤ a) (hD : 0 < D) (haD : a ≤ D) :
    |Real.log a| ≤ max (Real.log (1 / a)) 0 + |Real.log D| := by
  rcases eq_or_lt_of_le ha with h0 | h0
  · rw [← h0, Real.log_zero, abs_zero]
    exact add_nonneg (le_max_right _ _) (abs_nonneg _)
  · have h1 := Real.log_le_log h0 haD
    have h2 : Real.log (1 / a) = -Real.log a := by rw [one_div, Real.log_inv]
    rw [abs_le]; constructor
    · linarith [le_max_left (Real.log (1 / a)) 0, abs_nonneg (Real.log D)]
    · linarith [le_max_right (Real.log (1 / a)) 0, le_abs_self (Real.log D)]

/-- The logarithmic potential `∫ log ‖x − y‖ dκ(y)`. -/
def logPot (κ : Measure ℂ) (x : ℂ) : ℝ := ∫ y, Real.log ‖x - y‖ ∂κ

theorem measurable_log_norm_sub (x : ℂ) : Measurable fun y : ℂ => Real.log ‖x - y‖ :=
  Real.measurable_log.comp (measurable_const.sub measurable_id).norm

theorem abs_log_norm_sub_le {B : ℝ} (hB0 : 0 ≤ B) {x y : ℂ} (hy : ‖y‖ ≤ B) :
    |Real.log ‖x - y‖| ≤ logRatio 1 x y + |Real.log (‖x‖ + B + 1)| := by
  have h := abs_log_le_logRatio_add (norm_nonneg (x - y))
    (show 0 < ‖x‖ + B + 1 by positivity)
    (by linarith [norm_sub_le x y])
  exact h

theorem frostman_integrable_log (hF : IsFrostman κ α C) (hα : 0 < α) (hC : 0 ≤ C) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂κ, ‖y‖ ≤ B) (x : ℂ) :
    Integrable (fun y => Real.log ‖x - y‖) κ := by
  refine ((integrable_logRatio hF hα hC x one_pos).add
    (integrable_const |Real.log (‖x‖ + B + 1)|)).mono'
    (measurable_log_norm_sub x).aestronglyMeasurable ?_
  filter_upwards [hB] with y hy
  rw [Real.norm_eq_abs]
  exact abs_log_norm_sub_le hB0 hy

theorem abs_logPot_le (hF : IsFrostman κ α C) (hα : 0 < α) (hC : 0 ≤ C) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂κ, ‖y‖ ≤ B) (x : ℂ) :
    |logPot κ x| ≤ C / α + |Real.log (‖x‖ + B + 1)| * κ.real univ := by
  have hi := integrable_logRatio hF hα hC x one_pos
  calc |logPot κ x| ≤ ∫ y, |Real.log ‖x - y‖| ∂κ := abs_integral_le_integral_abs
    _ ≤ ∫ y, (logRatio 1 x y + |Real.log (‖x‖ + B + 1)|) ∂κ := by
        refine integral_mono_ae (frostman_integrable_log hF hα hC hB0 hB x).abs
          (hi.add (integrable_const _)) ?_
        filter_upwards [hB] with y hy
        exact abs_log_norm_sub_le hB0 hy
    _ = (∫ y, logRatio 1 x y ∂κ) + |Real.log (‖x‖ + B + 1)| * κ.real univ := by
        rw [integral_add hi (integrable_const _), integral_const, smul_eq_mul, mul_comm]
    _ ≤ C / α + |Real.log (‖x‖ + B + 1)| * κ.real univ := by
        have := integral_logRatio_le hF hα hC x one_pos
        rw [Real.one_rpow, mul_one] at this
        linarith

/-- Pointwise estimate behind the Hölder bound. -/
theorem abs_log_sub_log_le {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hab : |a - b| ≤ ε) :
    |Real.log a - Real.log b| ≤ Real.sqrt ε + max (Real.log (2 * Real.sqrt ε / a)) 0 +
      max (Real.log (2 * Real.sqrt ε / b)) 0 := by
  set ρ := Real.sqrt ε with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hε
  have hρ2 : ρ ^ 2 = ε := Real.sq_sqrt hε.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hε1
  have hερ : ε ≤ ρ := by nlinarith
  have hm1 := le_max_right (Real.log (2 * ρ / a)) 0
  have hm2 := le_max_right (Real.log (2 * ρ / b)) 0
  have hab' := abs_le.1 hab
  by_cases hcase : ρ ≤ a ∧ ρ ≤ b
  · have k1 : Real.log a - Real.log b ≤ ρ := by
      rw [← Real.log_div ha.ne' hb.ne']
      refine (Real.log_le_sub_one_of_pos (div_pos ha hb)).trans ?_
      rw [div_sub_one hb.ne', div_le_iff₀ hb]
      have := mul_le_mul_of_nonneg_left hcase.2 hρ0.le
      nlinarith
    have k2 : Real.log b - Real.log a ≤ ρ := by
      rw [← Real.log_div hb.ne' ha.ne']
      refine (Real.log_le_sub_one_of_pos (div_pos hb ha)).trans ?_
      rw [div_sub_one ha.ne', div_le_iff₀ ha]
      have := mul_le_mul_of_nonneg_left hcase.1 hρ0.le
      nlinarith
    rw [abs_le]; constructor <;> linarith
  · have hlt : a < 2 * ρ ∧ b < 2 * ρ := by
      rw [not_and_or, not_le, not_le] at hcase
      rcases hcase with h | h <;> constructor <;> linarith
    have e1 : Real.log (2 * ρ / a) = Real.log (2 * ρ) - Real.log a :=
      Real.log_div (by positivity) ha.ne'
    have e2 : Real.log (2 * ρ / b) = Real.log (2 * ρ) - Real.log b :=
      Real.log_div (by positivity) hb.ne'
    have p1 : 0 ≤ Real.log (2 * ρ / a) :=
      Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
    have p2 : 0 ≤ Real.log (2 * ρ / b) :=
      Real.log_nonneg (by rw [le_div_iff₀ hb]; linarith)
    have q1 := le_max_left (Real.log (2 * ρ / a)) 0
    have q2 := le_max_left (Real.log (2 * ρ / b)) 0
    rw [abs_le]; constructor <;> linarith [Real.sqrt_nonneg ε]

theorem abs_norm_sub_norm_le' (a b : ℂ) : |‖a‖ - ‖b‖| ≤ ‖a - b‖ :=
  abs_sub_le_iff.2 ⟨norm_sub_norm_le a b, by rw [norm_sub_rev]; exact norm_sub_norm_le b a⟩

/-- **Hölder continuity of the log potential** of a Frostman measure. -/
theorem abs_logPot_sub_le (hF : IsFrostman κ α C) (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂κ, ‖y‖ ≤ B) {x x' : ℂ} (hxx : ‖x - x'‖ ≤ 1) :
    |logPot κ x - logPot κ x'| ≤ (κ.real univ + 4 * C / α) * ‖x - x'‖ ^ (α / 2) := by
  have hm0 : 0 ≤ κ.real univ := measureReal_nonneg
  rcases eq_or_lt_of_le (norm_nonneg (x - x')) with h0 | hε
  · have : x = x' := by rw [← sub_eq_zero, ← norm_eq_zero]; exact h0.symm
    rw [this, sub_self, abs_zero]
    exact mul_nonneg (by positivity) (by positivity)
  set ε := ‖x - x'‖ with hεdef
  set s := 2 * Real.sqrt ε with hs
  have hs0 : 0 < s := by positivity
  have hi1 := integrable_logRatio hF hα hC x hs0
  have hi2 := integrable_logRatio hF hα hC x' hs0
  have hl1 := frostman_integrable_log hF hα hC hB0 hB x
  have hl2 := frostman_integrable_log hF hα hC hB0 hB x'
  have hpt : ∀ᵐ y ∂κ, |Real.log ‖x - y‖ - Real.log ‖x' - y‖| ≤
      Real.sqrt ε + logRatio s x y + logRatio s x' y := by
    filter_upwards [frostman_ae_ne hF hα hC x, frostman_ae_ne hF hα hC x'] with y hy hy'
    refine abs_log_sub_log_le (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hy)))
      (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hy'))) hε hxx ?_
    refine (abs_norm_sub_norm_le' _ _).trans (le_of_eq ?_)
    rw [hεdef]; congr 1; ring
  have hsq : Real.sqrt ε ≤ ε ^ (α / 2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hε hxx (by linarith)
  have hsα : s ^ α ≤ 2 * ε ^ (α / 2) := by
    rw [hs, Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hε.le, show 1 / 2 * α = α / 2 by ring]
    have h2 : (2 : ℝ) ^ α ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1
      rwa [Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  calc |logPot κ x - logPot κ x'|
      = |∫ y, (Real.log ‖x - y‖ - Real.log ‖x' - y‖) ∂κ| := by
        rw [logPot, logPot, integral_sub hl1 hl2]
    _ ≤ ∫ y, |Real.log ‖x - y‖ - Real.log ‖x' - y‖| ∂κ := abs_integral_le_integral_abs
    _ ≤ ∫ y, (Real.sqrt ε + logRatio s x y + logRatio s x' y) ∂κ :=
        integral_mono_ae (hl1.sub hl2).abs (((integrable_const _).add hi1).add hi2) hpt
    _ = Real.sqrt ε * κ.real univ + (∫ y, logRatio s x y ∂κ) + ∫ y, logRatio s x' y ∂κ := by
        rw [integral_add (f := fun y => Real.sqrt ε + logRatio s x y)
            (g := fun y => logRatio s x' y) ((integrable_const _).add hi1) hi2,
          integral_add (f := fun _ => Real.sqrt ε) (g := fun y => logRatio s x y)
            (integrable_const _) hi1, integral_const, smul_eq_mul, mul_comm]
    _ ≤ ε ^ (α / 2) * κ.real univ + C * s ^ α / α + C * s ^ α / α := by
        have := integral_logRatio_le hF hα hC x hs0
        have := integral_logRatio_le hF hα hC x' hs0
        have := mul_le_mul_of_nonneg_right hsq hm0
        linarith
    _ ≤ ε ^ (α / 2) * κ.real univ + C * (2 * ε ^ (α / 2)) / α +
          C * (2 * ε ^ (α / 2)) / α := by
        have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsα hC) hα.le
        linarith
    _ = (κ.real univ + 4 * C / α) * ε ^ (α / 2) := by ring

/-- The Neumann potential `∫ neumannH x y dκ(y)`. -/
def neuPot (κ : Measure ℂ) (x : ℂ) : ℝ := ∫ y, neumannH x y ∂κ

theorem norm_sub_conj_eq (x y : ℂ) : ‖x - conj y‖ = ‖conj x - y‖ := by
  rw [← Complex.norm_conj (x - conj y), map_sub, Complex.conj_conj]

theorem measurable_neumannH_uncurry : Measurable (Function.uncurry neumannH) := by
  have e : Function.uncurry neumannH =
      fun p : ℂ × ℂ => -Real.log ‖p.1 - p.2‖ - Real.log ‖p.1 - conj p.2‖ := rfl
  rw [e]
  exact ((Real.measurable_log.comp (continuous_fst.sub continuous_snd).norm.measurable).neg).sub
    (Real.measurable_log.comp
      (continuous_fst.sub (Complex.continuous_conj.comp continuous_snd)).norm.measurable)

theorem measurable_neuPot (κ : Measure ℂ) [IsFiniteMeasure κ] : Measurable (neuPot κ) :=
  (StronglyMeasurable.integral_prod_right (f := neumannH) (ν := κ)
    measurable_neumannH_uncurry.stronglyMeasurable).measurable

theorem neuPot_eq (hF : IsFrostman κ α C) (hα : 0 < α) (hC : 0 ≤ C) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂κ, ‖y‖ ≤ B) (x : ℂ) :
    neuPot κ x = -logPot κ x - logPot κ (conj x) := by
  unfold neuPot neumannH logPot
  simp_rw [norm_sub_conj_eq x]
  rw [integral_sub (f := fun y => -Real.log ‖x - y‖) (g := fun y => Real.log ‖conj x - y‖)
    (frostman_integrable_log hF hα hC hB0 hB x).neg
    (frostman_integrable_log hF hα hC hB0 hB (conj x)), integral_neg]

theorem abs_neuPot_le (hF : IsFrostman κ α C) (hα : 0 < α) (hC : 0 ≤ C) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂κ, ‖y‖ ≤ B) {x : ℂ} {X : ℝ} (hx : ‖x‖ ≤ X) :
    |neuPot κ x| ≤ 2 * (C / α) + 2 * (Real.log (X + B + 1) * κ.real univ) := by
  have hm0 : 0 ≤ κ.real univ := measureReal_nonneg
  have hlog : |Real.log (‖x‖ + B + 1)| ≤ Real.log (X + B + 1) := by
    rw [abs_of_nonneg (Real.log_nonneg (by linarith [norm_nonneg x]))]
    exact Real.log_le_log (by positivity) (by linarith)
  have h1 := abs_logPot_le hF hα hC hB0 hB x
  have h2 := abs_logPot_le hF hα hC hB0 hB (conj x)
  rw [Complex.norm_conj] at h2
  have h3 := mul_le_mul_of_nonneg_right hlog hm0
  rw [neuPot_eq hF hα hC hB0 hB x]
  have := abs_le.1 h1
  have := abs_le.1 h2
  rw [abs_le]; constructor <;> linarith

/-- **Hölder continuity of the Neumann potential**, for all displacements, on `‖x‖ ≤ X`. -/
theorem abs_neuPot_sub_le (hF : IsFrostman κ α C) (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ y ∂κ, ‖y‖ ≤ B) {X : ℝ} {x x' : ℂ} (hx : ‖x‖ ≤ X)
    (hx' : ‖x'‖ ≤ X) :
    |neuPot κ x - neuPot κ x'| ≤
      (2 * (κ.real univ + 4 * C / α) + 2 * (2 * (C / α) + 2 * (Real.log (X + B + 1) *
        κ.real univ))) * ‖x - x'‖ ^ (α / 2) := by
  have hm0 : 0 ≤ κ.real univ := measureReal_nonneg
  have hX : 0 ≤ X := (norm_nonneg x).trans hx
  have hP0 : 0 ≤ 2 * (C / α) + 2 * (Real.log (X + B + 1) * κ.real univ) := by
    have : 0 ≤ Real.log (X + B + 1) := Real.log_nonneg (by linarith)
    positivity
  have hK0 : 0 ≤ κ.real univ + 4 * C / α := by positivity
  have hpow : 0 ≤ ‖x - x'‖ ^ (α / 2) := by positivity
  rcases le_or_gt ‖x - x'‖ 1 with h1 | h1
  · have hc : ‖conj x - conj x'‖ = ‖x - x'‖ := by rw [← map_sub, Complex.norm_conj]
    have a1 := abs_logPot_sub_le hF hα hα1 hC hB0 hB h1
    have a2 := abs_logPot_sub_le hF hα hα1 hC hB0 hB (x := conj x) (x' := conj x')
      (by rw [hc]; exact h1)
    rw [hc] at a2
    rw [neuPot_eq hF hα hC hB0 hB x, neuPot_eq hF hα hC hB0 hB x']
    have := abs_le.1 a1
    have := abs_le.1 a2
    have := mul_nonneg hP0 hpow
    rw [abs_le]; constructor <;> nlinarith
  · have hone : 1 ≤ ‖x - x'‖ ^ (α / 2) := Real.one_le_rpow h1.le (by positivity)
    have b1 := abs_le.1 (abs_neuPot_le hF hα hC hB0 hB hx)
    have b2 := abs_le.1 (abs_neuPot_le hF hα hC hB0 hB hx')
    have := mul_le_mul_of_nonneg_left hone hP0
    have := mul_nonneg hK0 hpow
    rw [abs_le]; constructor <;> nlinarith

end Potential

/-! ## B. Coupling two pushed-forward folded circles -/

section Coupling

variable {W : ℝ → ℝ}

private lemma revMap_eq_zero_of_not_im_pos {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : ¬ 0 < z.im) :
    revMap W T z = 0 := by
  unfold revMap
  rw [dif_neg]
  rintro ⟨u, hu⟩
  obtain ⟨h1, h2⟩ := hu.2 0 ⟨le_rfl, hT⟩
  rw [h2, intervalIntegral.integral_same] at h1
  exact hz (by simpa using h1)

/-- `revMap W T` is bounded on bounded sets (the proof of `UnzipFullSplit.norm_revMap_le`,
extended by the junk value `0` off `H`). -/
theorem exists_norm_revMap_le (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (R₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ R₀ → ‖revMap W T z‖ ≤ C := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  have hM' : ∀ s ∈ Icc (0 : ℝ) T, |W s| ≤ M := fun s hs => by
    simpa [Real.norm_eq_abs] using hM s hs
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0 ⟨le_rfl, hT⟩)
  set K := 4 * (2 * M + T + 1) + |R₀| with hK
  have hK4 : 4 ≤ K := by nlinarith [abs_nonneg R₀]
  refine ⟨K + 2 * M + T, by linarith, fun z hzR => ?_⟩
  by_cases hz : 0 < z.im
  swap
  · rw [revMap_eq_zero_of_not_im_pos hT hz, norm_zero]; linarith
  by_cases hle : ‖revMap W T z‖ ≤ K
  · linarith
  push_neg at hle
  have hcont : ContinuousOn (fun s => ‖revMap W s z‖) (Icc 0 T) :=
    (ReverseFlow.continuousOn_revMap_time W hW z hz).norm.mono Icc_subset_Ici_self
  have h0 : ‖revMap W 0 z‖ ≤ K := by
    obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz 0 le_rfl
    rw [revMap_eq W hW z le_rfl le_rfl hu, (hu.2 0 ⟨le_rfl, le_rfl⟩).2,
      intervalIntegral.integral_same, sub_zero]
    calc ‖z - (W 0 : ℂ)‖ ≤ ‖z‖ + ‖(W 0 : ℂ)‖ := norm_sub_le _ _
      _ ≤ |R₀| + M := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add (hzR.trans (le_abs_self _)) (hM' 0 ⟨le_rfl, hT⟩)
      _ ≤ K := by linarith
  obtain ⟨s₀, hs₀, hs₀eq'⟩ := intermediate_value_Icc hT hcont ⟨h0, hle.le⟩
  have hs₀eq : ‖revMap W s₀ z‖ = K := hs₀eq'
  have hsplit : revMap W T z =
      revMap (fun r => W (s₀ + r) - W s₀) (T - s₀) (revMap W s₀ z) := by
    have := ReverseFlow.revMap_add W hW z hz hs₀.1 (sub_nonneg.2 hs₀.2)
    rwa [add_sub_cancel] at this
  have hW' : Continuous fun r => W (s₀ + r) - W s₀ :=
    (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  have hM'' : ∀ r ∈ Icc (0 : ℝ) (T - s₀), |W (s₀ + r) - W s₀| ≤ 2 * M := fun r hr => by
    have h1 := abs_le.1 (hM' (s₀ + r) ⟨by linarith [hs₀.1, hr.1], by linarith [hr.2]⟩)
    have h2 := abs_le.1 (hM' s₀ hs₀)
    rw [abs_le]; constructor <;> linarith
  have hzH : revMap W s₀ z ∈ H := im_revMap_pos hW hz hs₀.1
  have hfar := WeldingUniqueness.norm_revMap_sub_far hW' (sub_nonneg.2 hs₀.2) hM'' hzH
    (by rw [hs₀eq]; nlinarith [abs_nonneg R₀, hs₀.1])
  rw [hs₀eq] at hfar
  rw [hsplit]
  set u₀ := revMap W s₀ z
  set a := revMap (fun r => W (s₀ + r) - W s₀) (T - s₀) u₀
  set c : ℂ := ((W (s₀ + (T - s₀)) - W s₀ : ℝ) : ℂ)
  have e : a = (a - (u₀ - c)) + u₀ - c := by ring
  have hc : ‖c‖ ≤ 2 * M := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hM'' (T - s₀) ⟨sub_nonneg.2 hs₀.2, le_rfl⟩
  have hdiv : 4 * (T - s₀) / K ≤ T := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [hs₀.1]
  calc ‖a‖ = ‖(a - (u₀ - c)) + u₀ - c‖ := by rw [← e]
    _ ≤ ‖a - (u₀ - c)‖ + ‖u₀‖ + ‖c‖ :=
        (norm_sub_le _ _).trans (by linarith [norm_add_le (a - (u₀ - c)) u₀])
    _ ≤ T + K + 2 * M := by
        rw [show ‖u₀‖ = K from hs₀eq]
        exact add_le_add (add_le_add (hfar.trans hdiv) le_rfl) hc
    _ = K + 2 * M + T := by ring

theorem norm_foldH_sub_le (x y : ℂ) : ‖foldH x - foldH y‖ ≤ ‖x - y‖ := by
  have h : ‖foldH x - foldH y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, re_foldH, im_foldH]
    have k : (|x.im| - |y.im|) * (|x.im| - |y.im|) ≤ (x.im - y.im) * (x.im - y.im) := by
      nlinarith [sq_abs x.im, sq_abs y.im, abs_mul x.im y.im, le_abs_self (x.im * y.im)]
    linarith
  nlinarith [norm_nonneg (foldH x - foldH y), norm_nonneg (x - y)]

theorem norm_circleMap_sub_le (w w' : ℂ) (r r' θ : ℝ) :
    ‖circleMap w r θ - circleMap w' r' θ‖ ≤ ‖w - w'‖ + |r - r'| := by
  have e : circleMap w r θ - circleMap w' r' θ =
      (w - w') + ((r - r' : ℝ) : ℂ) * Complex.exp (θ * I) := by
    simp only [circleMap]; push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, mul_one]

/-- Upper two-point bound in the form used for the coupling. -/
theorem norm_revMap_sub_mul_le_upper (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {u v : ℂ}
    {τ R : ℝ} (hτ : 0 < τ) (hu : τ ≤ u.im) (hv : τ ≤ v.im) (huR : u.im ≤ R) (hvR : v.im ≤ R) :
    ‖revMap W T u - revMap W T v‖ * τ ≤ ‖u - v‖ * Real.sqrt (R ^ 2 + 4 * T) := by
  have hu0 : u ∈ H := show 0 < u.im by linarith
  have hv0 : v ∈ H := show 0 < v.im by linarith
  set M := Real.sqrt (R ^ 2 + 4 * T)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hfuM : (revMap W T u).im ≤ M := (le_abs_self _).trans
    (Real.abs_le_sqrt (by nlinarith [im_revMap_sq_le hW hu0 hT]))
  have hfvM : (revMap W T v).im ≤ M := (le_abs_self _).trans
    (Real.abs_le_sqrt (by nlinarith [im_revMap_sq_le hW hv0 hT]))
  have hImp : (revMap W T u).im * (revMap W T v).im ≤ M ^ 2 := by
    rw [sq]; exact mul_le_mul hfuM hfvM (im_revMap_pos hW hv0 hT).le hM
  have hsq : (‖revMap W T u - revMap W T v‖ * τ) ^ 2 ≤ (‖u - v‖ * M) ^ 2 := by
    calc (‖revMap W T u - revMap W T v‖ * τ) ^ 2
        = ‖revMap W T u - revMap W T v‖ ^ 2 * (τ * τ) := by ring
      _ ≤ ‖revMap W T u - revMap W T v‖ ^ 2 * (u.im * v.im) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hu hv hτ.le (by linarith)) (sq_nonneg _)
      _ ≤ ‖u - v‖ ^ 2 * ((revMap W T u).im * (revMap W T v).im) :=
        twoPoint_upper_sq hW hu0 hv0 hT
      _ ≤ ‖u - v‖ ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hImp (sq_nonneg _)
      _ = (‖u - v‖ * M) ^ 2 := by ring
  have h1 : 0 ≤ ‖revMap W T u - revMap W T v‖ * τ := mul_nonneg (norm_nonneg _) hτ.le
  have h2 : 0 ≤ ‖u - v‖ * M := mul_nonneg (norm_nonneg _) hM
  nlinarith [hsq, h1, h2]

/-- `f_* fc(w, r)`. -/
abbrev pfc (W : ℝ → ℝ) (T : ℝ) (w : ℂ) (r : ℝ) : Measure ℂ :=
  (foldedCircle w r).map (revMap W T)

theorem pfc_real_univ (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (w : ℂ) (r : ℝ) :
    (pfc W T w r).real univ = 1 := by
  rw [measureReal_def, Measure.map_apply (measurable_revMap hW hT) MeasurableSet.univ,
    preimage_univ, measure_univ, ENNReal.toReal_one]

theorem pfc_ae_norm_le (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {w : ℂ} {r R Bf : ℝ}
    (hr : 0 ≤ r) (hwR : ‖w‖ + r ≤ R) (hBf : ∀ z : ℂ, ‖z‖ ≤ R → ‖revMap W T z‖ ≤ Bf) :
    ∀ᵐ y ∂pfc W T w r, ‖y‖ ≤ Bf := by
  rw [ae_map_iff (measurable_revMap hW hT).aemeasurable
    (isClosed_le continuous_norm continuous_const).measurableSet]
  filter_upwards [foldedCircle_ae_norm_le w hr] with u hu
  exact hBf u (hu.trans hwR)

theorem kernelCov_pfc (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {w : ℂ} {r : ℝ} {ν : Measure ℂ}
    (hν : ν = pfc W T w r) (κ : Measure ℂ) [IsFiniteMeasure κ] :
    kernelCov neumannH ν κ = (2 * π)⁻¹ *
      ∫ θ in Ico 0 (2 * π), neuPot κ (revMap W T (foldH (circleMap w r θ))) := by
  show ∫ x, neuPot κ x ∂ν = _
  rw [hν, pfc, integral_map (measurable_revMap hW hT).aemeasurable
    (measurable_neuPot κ).aestronglyMeasurable]
  exact integral_foldedCircle_eq ((measurable_neuPot κ).comp (measurable_revMap hW hT)) w r

/-- Bound on `sup |neuPot|` for the pushed-forward circles (`α = 1/3`, mass `1`). -/
def potMax (CF Bf : ℝ) : ℝ := 2 * (CF / (1 / 3)) + 2 * (Real.log (Bf + Bf + 1) * 1)

/-- Hölder constant of `neuPot` for the pushed-forward circles. -/
def holderK (CF Bf : ℝ) : ℝ := 2 * (1 + 4 * CF / (1 / 3)) + 2 * potMax CF Bf

theorem potMax_nonneg {CF Bf : ℝ} (hCF : 0 ≤ CF) (hBf : 0 ≤ Bf) : 0 ≤ potMax CF Bf := by
  unfold potMax
  have : 0 ≤ Real.log (Bf + Bf + 1) := Real.log_nonneg (by linarith)
  positivity

theorem holderK_nonneg {CF Bf : ℝ} (hCF : 0 ≤ CF) (hBf : 0 ≤ Bf) : 0 ≤ holderK CF Bf := by
  unfold holderK
  have := potMax_nonneg hCF hBf
  positivity

/-- The per-measure coupling estimate. -/
theorem abs_integral_neuPot_coupling_le (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    {r₀ R Bf CF δ τ : ℝ} (hr₀ : 0 < r₀) (hCF : 0 ≤ CF) (hBf0 : 0 ≤ Bf)
    (hBf : ∀ z : ℂ, ‖z‖ ≤ R → ‖revMap W T z‖ ≤ Bf) (hτ : 0 < τ)
    {w w' : ℂ} {r r' : ℝ} (hr : r₀ ≤ r) (hr' : r₀ ≤ r') (hwR : ‖w‖ + r ≤ R)
    (hwR' : ‖w'‖ + r' ≤ R) (hδ : ‖w - w'‖ + |r - r'| ≤ δ)
    (κ : Measure ℂ) [IsFiniteMeasure κ] (hFκ : IsFrostman κ (1 / 3) CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ Bf) (hmκ : κ.real univ = 1) :
    |∫ θ in Ico 0 (2 * π), (neuPot κ (revMap W T (foldH (circleMap w r θ))) -
        neuPot κ (revMap W T (foldH (circleMap w' r' θ))))| ≤
      2 * π * (holderK CF Bf * (δ * Real.sqrt (R ^ 2 + 4 * T) / τ) ^ ((1 / 3 : ℝ) / 2)) +
        2 * potMax CF Bf * (72 * π * Real.sqrt (τ / r₀)) := by
  have hπ := Real.pi_pos
  have hr0 : 0 < r := hr₀.trans_le hr
  have hr0' : 0 < r' := hr₀.trans_le hr'
  have : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  set M := Real.sqrt (R ^ 2 + 4 * T) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  set Pm := potMax CF Bf
  set KH := holderK CF Bf
  have hPm0 : 0 ≤ Pm := potMax_nonneg hCF hBf0
  have hKH0 : 0 ≤ KH := holderK_nonneg hCF hBf0
  set F : ℝ → ℂ := fun θ => revMap W T (foldH (circleMap w r θ)) with hFdef
  set F' : ℝ → ℂ := fun θ => revMap W T (foldH (circleMap w' r' θ)) with hF'def
  have hFm : Measurable F :=
    (measurable_revMap hW hT).comp (measurable_foldH.comp (measurable_circleMap w r))
  have hF'm : Measurable F' :=
    (measurable_revMap hW hT).comp (measurable_foldH.comp (measurable_circleMap w' r'))
  have hFb : ∀ θ, ‖F θ‖ ≤ Bf := fun θ => hBf _ ((norm_foldH _).le.trans
    ((norm_circleMap_le_add w hr0.le θ).trans hwR))
  have hF'b : ∀ θ, ‖F' θ‖ ≤ Bf := fun θ => hBf _ ((norm_foldH _).le.trans
    ((norm_circleMap_le_add w' hr0'.le θ).trans hwR'))
  have hPb : ∀ x : ℂ, ‖x‖ ≤ Bf → |neuPot κ x| ≤ Pm := fun x hx => by
    have := abs_neuPot_le hFκ (by norm_num) hCF hBf0 hBκ hx
    rwa [hmκ] at this
  have hH : ∀ x x' : ℂ, ‖x‖ ≤ Bf → ‖x'‖ ≤ Bf →
      |neuPot κ x - neuPot κ x'| ≤ KH * ‖x - x'‖ ^ ((1 / 3 : ℝ) / 2) := fun x x' hx hx' => by
    have := abs_neuPot_sub_le hFκ (by norm_num) (by norm_num) hCF hBf0 hBκ hx hx'
    rwa [hmκ] at this
  have hi : ∀ G : ℝ → ℂ, Measurable G → (∀ θ, ‖G θ‖ ≤ Bf) →
      Integrable (fun θ => neuPot κ (G θ)) (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    fun G hG hGb => Integrable.of_bound ((measurable_neuPot κ).comp hG).aestronglyMeasurable Pm
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hPb _ (hGb θ))
  set Bad : Set ℝ := {θ | |(circleMap w r θ).im| < τ} ∪ {θ | |(circleMap w' r' θ).im| < τ}
    with hBad
  have hBadm : MeasurableSet Bad :=
    ((isOpen_lt (continuous_abs.comp (Complex.continuous_im.comp (continuous_circleMap w r)))
      continuous_const).union (isOpen_lt (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_circleMap w' r'))) continuous_const)).measurableSet
  set D := KH * (δ * M / τ) ^ ((1 / 3 : ℝ) / 2) with hD
  have hD0 : 0 ≤ D := by
    have hδ0 : 0 ≤ δ := le_trans (by positivity) hδ
    positivity
  have hpt : ∀ θ, |neuPot κ (F θ) - neuPot κ (F' θ)| ≤
      D + Bad.indicator (fun _ => 2 * Pm) θ := by
    intro θ
    by_cases hθ : θ ∈ Bad
    · rw [Set.indicator_of_mem hθ]
      have a1 := abs_le.1 (hPb _ (hFb θ))
      have a2 := abs_le.1 (hPb _ (hF'b θ))
      rw [abs_le]; constructor <;> linarith
    · rw [Set.indicator_of_notMem hθ, add_zero]
      simp only [hBad, mem_union, mem_setOf_eq, not_or, not_lt] at hθ
      set u := foldH (circleMap w r θ)
      set v := foldH (circleMap w' r' θ)
      have hu : τ ≤ u.im := by rw [im_foldH]; exact hθ.1
      have hv : τ ≤ v.im := by rw [im_foldH]; exact hθ.2
      have huR : u.im ≤ R := (Complex.im_le_norm _).trans ((norm_foldH _).le.trans
        ((norm_circleMap_le_add w hr0.le θ).trans hwR))
      have hvR : v.im ≤ R := (Complex.im_le_norm _).trans ((norm_foldH _).le.trans
        ((norm_circleMap_le_add w' hr0'.le θ).trans hwR'))
      have huv : ‖u - v‖ ≤ δ :=
        (norm_foldH_sub_le _ _).trans ((norm_circleMap_sub_le w w' r r' θ).trans hδ)
      have hkey := norm_revMap_sub_mul_le_upper hW hT hτ hu hv huR hvR
      have hdisp : ‖F θ - F' θ‖ ≤ δ * M / τ := by
        rw [le_div_iff₀ hτ]
        exact hkey.trans (mul_le_mul_of_nonneg_right huv hM0)
      refine (hH _ _ (hFb θ) (hF'b θ)).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hdisp (by norm_num))
        hKH0
  have hint := (hi F hFm hFb).sub (hi F' hF'm hF'b)
  have hrhs : Integrable (fun θ => D + Bad.indicator (fun _ => 2 * Pm) θ)
      (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    (integrable_const D).add ((integrable_const (2 * Pm)).indicator hBadm)
  have hvolI : (volume.restrict (Ico (0 : ℝ) (2 * π))).real univ = 2 * π := by
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (by positivity)]
  have hstrip : ∀ (z : ℂ) (ρ : ℝ), r₀ ≤ ρ →
      volume {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |(circleMap z ρ θ).im| < τ} ≤
        ENNReal.ofReal (36 * π * Real.sqrt (τ / r₀)) := fun z ρ hρ => by
    refine (volume_strip_le z (hr₀.trans_le hρ) hτ).trans (ENNReal.ofReal_le_ofReal ?_)
    have : Real.sqrt (τ / ρ) ≤ Real.sqrt (τ / r₀) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hτ.le hr₀ hρ)
    nlinarith
  have hvolB : (volume.restrict (Ico (0 : ℝ) (2 * π))).real Bad ≤ 72 * π * Real.sqrt (τ / r₀) := by
    rw [measureReal_def, Measure.restrict_apply hBadm]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have hsub : Bad ∩ Ico 0 (2 * π) ⊆
        {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |(circleMap w r θ).im| < τ} ∪
        {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |(circleMap w' r' θ).im| < τ} := by
      rintro θ ⟨hb, hI⟩
      rcases hb with h | h
      · exact Or.inl ⟨hI, h⟩
      · exact Or.inr ⟨hI, h⟩
    have h36 : (0 : ℝ) ≤ 36 * π * Real.sqrt (τ / r₀) := by positivity
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans
      ((add_le_add (hstrip w r hr) (hstrip w' r' hr')).trans (le_of_eq ?_)))
    rw [← ENNReal.ofReal_add h36 h36]
    congr 1; ring
  calc |∫ θ in Ico 0 (2 * π), (neuPot κ (F θ) - neuPot κ (F' θ))|
      ≤ ∫ θ in Ico 0 (2 * π), |neuPot κ (F θ) - neuPot κ (F' θ)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ θ in Ico 0 (2 * π), (D + Bad.indicator (fun _ => 2 * Pm) θ) :=
        integral_mono hint.abs hrhs hpt
    _ = 2 * π * D + (volume.restrict (Ico (0 : ℝ) (2 * π))).real Bad * (2 * Pm) := by
        rw [integral_add (integrable_const D) ((integrable_const (2 * Pm)).indicator hBadm),
          integral_const, integral_indicator_const _ hBadm, hvolI, smul_eq_mul, smul_eq_mul]
    _ ≤ 2 * π * D + 72 * π * Real.sqrt (τ / r₀) * (2 * Pm) := by
        have := mul_le_mul_of_nonneg_right hvolB (by positivity : (0 : ℝ) ≤ 2 * Pm)
        linarith
    _ = _ := by rw [hD]; ring

/-- **(E) Energy modulus.** For pushed-forward folded circles `ν = f_* fc(w,r)` and
`ν' = f_* fc(w',r')` with `r, r' ≥ r₀ > 0`, `‖w‖ + r, ‖w'‖ + r' ≤ R` and
`δ = ‖w − w'‖ + |r − r'| ≤ 1`, the Neumann energy of `ν − ν'` is `≤ C δ^{1/12}`, with `C`
depending only on `W, T, r₀, R`. -/
theorem abs_kernelCov2_revMap_foldedCircle_le (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    {r₀ R : ℝ} (hr₀ : 0 < r₀) :
    ∃ Cst : ℝ, ∀ (w w' : ℂ) (r r' : ℝ), r₀ ≤ r → r₀ ≤ r' → ‖w‖ + r ≤ R → ‖w'‖ + r' ≤ R →
      ‖w - w'‖ + |r - r'| ≤ 1 →
      |kernelCov2 neumannH (pfc W T w r, pfc W T w' r') (pfc W T w r, pfc W T w' r')| ≤
        Cst * (‖w - w'‖ + |r - r'|) ^ (1 / 12 : ℝ) := by
  have hπ := Real.pi_pos
  obtain ⟨Bf, hBf0, hBf⟩ := exists_norm_revMap_le hW hT R
  set CF := 18 / Real.sqrt r₀ + 12 * Real.sqrt (R ^ 2 + 4 * T) / r₀ with hCFdef
  have hCF : 0 ≤ CF := by positivity
  set M := Real.sqrt (R ^ 2 + 4 * T) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  set Pm := potMax CF Bf
  set KH := holderK CF Bf
  have hPm0 : 0 ≤ Pm := potMax_nonneg hCF hBf0
  have hKH0 : 0 ≤ KH := holderK_nonneg hCF hBf0
  refine ⟨2 * KH * M ^ ((1 / 3 : ℝ) / 2) + 144 * Pm / Real.sqrt r₀,
    fun w w' r r' hr hr' hwR hwR' hδ1 => ?_⟩
  have hr0 : 0 < r := hr₀.trans_le hr
  have hr0' : 0 < r' := hr₀.trans_le hr'
  set δ := ‖w - w'‖ + |r - r'| with hδdef
  rcases eq_or_lt_of_le (show 0 ≤ δ by positivity) with hδ0 | hδ
  · have hw : w = w' := by
      have := norm_nonneg (w - w'); have := abs_nonneg (r - r')
      rw [← sub_eq_zero, ← norm_eq_zero]; linarith
    have hrr : r = r' := by
      have := norm_nonneg (w - w'); have := abs_nonneg (r - r')
      rw [← sub_eq_zero, ← abs_eq_zero]; linarith
    subst hw hrr
    have : kernelCov2 neumannH (pfc W T w r, pfc W T w r) (pfc W T w r, pfc W T w r) = 0 := by
      unfold kernelCov2; ring
    rw [this, abs_zero, ← hδ0, Real.zero_rpow (by norm_num), mul_zero]
  obtain ⟨ν, hν⟩ : ∃ ν, ν = pfc W T w r := ⟨_, rfl⟩
  obtain ⟨ν', hν'⟩ : ∃ ν', ν' = pfc W T w' r' := ⟨_, rfl⟩
  rw [← hν, ← hν']
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have : IsFiniteMeasure ν' := by rw [hν']; infer_instance
  have hFν : IsFrostman ν (1 / 3) CF := hν ▸ isFrostman_revMap_foldedCircle hW hT hr₀ hr hwR
  have hFν' : IsFrostman ν' (1 / 3) CF := hν' ▸ isFrostman_revMap_foldedCircle hW hT hr₀ hr' hwR'
  have hBν : ∀ᵐ y ∂ν, ‖y‖ ≤ Bf := hν ▸ pfc_ae_norm_le hW hT hr0.le hwR hBf
  have hBν' : ∀ᵐ y ∂ν', ‖y‖ ≤ Bf := hν' ▸ pfc_ae_norm_le hW hT hr0'.le hwR' hBf
  have hmν : ν.real univ = 1 := hν ▸ pfc_real_univ hW hT w r
  have hmν' : ν'.real univ = 1 := hν' ▸ pfc_real_univ hW hT w' r'
  set τ := Real.sqrt δ with hτdef
  have hτ : 0 < τ := Real.sqrt_pos.2 hδ
  have hI1 : |∫ θ in Ico 0 (2 * π), (neuPot ν (revMap W T (foldH (circleMap w r θ))) -
        neuPot ν (revMap W T (foldH (circleMap w' r' θ))))| ≤
      2 * π * (KH * (δ * M / τ) ^ ((1 / 3 : ℝ) / 2)) + 2 * Pm * (72 * π * Real.sqrt (τ / r₀)) :=
    abs_integral_neuPot_coupling_le hW hT hr₀ hCF hBf0 hBf hτ hr hr' hwR hwR' le_rfl
    ν hFν hBν hmν
  have hI2 : |∫ θ in Ico 0 (2 * π), (neuPot ν' (revMap W T (foldH (circleMap w r θ))) -
        neuPot ν' (revMap W T (foldH (circleMap w' r' θ))))| ≤
      2 * π * (KH * (δ * M / τ) ^ ((1 / 3 : ℝ) / 2)) + 2 * Pm * (72 * π * Real.sqrt (τ / r₀)) :=
    abs_integral_neuPot_coupling_le hW hT hr₀ hCF hBf0 hBf hτ hr hr' hwR hwR' le_rfl
    ν' hFν' hBν' hmν'
  have : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have hFm : ∀ (z : ℂ) (ρ : ℝ), Measurable fun θ => revMap W T (foldH (circleMap z ρ θ)) :=
    fun z ρ => (measurable_revMap hW hT).comp (measurable_foldH.comp (measurable_circleMap z ρ))
  have hint : ∀ (κ : Measure ℂ) [IsFiniteMeasure κ], IsFrostman κ (1 / 3) CF →
      (∀ᵐ y ∂κ, ‖y‖ ≤ Bf) → κ.real univ = 1 → ∀ (z : ℂ) (ρ : ℝ), r₀ ≤ ρ → ‖z‖ + ρ ≤ R →
      Integrable (fun θ => neuPot κ (revMap W T (foldH (circleMap z ρ θ))))
        (volume.restrict (Ico (0 : ℝ) (2 * π))) := by
    intro κ _ hFκ hBκ hmκ z ρ hρ hzR
    refine Integrable.of_bound ((measurable_neuPot κ).comp (hFm z ρ)).aestronglyMeasurable Pm
      (ae_of_all _ fun θ => ?_)
    rw [Real.norm_eq_abs]
    have := abs_neuPot_le hFκ (by norm_num) hCF hBf0 hBκ (hBf _ ((norm_foldH _).le.trans
      ((norm_circleMap_le_add z (hr₀.trans_le hρ).le θ).trans hzR)))
    rwa [hmκ] at this
  have e1 := integral_sub (hint ν hFν hBν hmν w r hr hwR) (hint ν hFν hBν hmν w' r' hr' hwR')
  have e2 := integral_sub (hint ν' hFν' hBν' hmν' w r hr hwR)
    (hint ν' hFν' hBν' hmν' w' r' hr' hwR')
  have hexp : kernelCov2 neumannH (ν, ν') (ν, ν') = (2 * π)⁻¹ *
      ((∫ θ in Ico 0 (2 * π), (neuPot ν (revMap W T (foldH (circleMap w r θ))) -
          neuPot ν (revMap W T (foldH (circleMap w' r' θ))))) -
        ∫ θ in Ico 0 (2 * π), (neuPot ν' (revMap W T (foldH (circleMap w r θ))) -
          neuPot ν' (revMap W T (foldH (circleMap w' r' θ))))) := by
    show kernelCov neumannH ν ν - kernelCov neumannH ν ν' - kernelCov neumannH ν' ν +
      kernelCov neumannH ν' ν' = _
    rw [kernelCov_pfc hW hT hν ν, kernelCov_pfc hW hT hν ν', kernelCov_pfc hW hT hν' ν,
      kernelCov_pfc hW hT hν' ν', e1, e2]
    ring
  -- the algebra of `τ = √δ`
  have hdiv : δ * M / τ = Real.sqrt δ * M := by
    rw [hτdef, mul_div_right_comm, Real.div_sqrt]
  have hpow1 : (δ * M / τ) ^ ((1 / 3 : ℝ) / 2) = M ^ ((1 / 3 : ℝ) / 2) * δ ^ (1 / 12 : ℝ) := by
    rw [hdiv, Real.mul_rpow (Real.sqrt_nonneg _) hM0, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hδ.le, show (1 / 2 : ℝ) * ((1 / 3 : ℝ) / 2) = 1 / 12 by norm_num]
    ring
  have hpow2 : Real.sqrt (τ / r₀) ≤ δ ^ (1 / 12 : ℝ) / Real.sqrt r₀ := by
    rw [Real.sqrt_div (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hδ.le]
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  rw [hexp, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  have hsub := abs_sub _ _ |>.trans (add_le_add hI1 hI2)
  rw [hpow1] at hsub
  have hsr : 0 < Real.sqrt r₀ := Real.sqrt_pos.2 hr₀
  have h3 := mul_le_mul_of_nonneg_left hpow2 (by positivity : (0 : ℝ) ≤ 2 * Pm * (72 * π))
  have hδp : 0 ≤ δ ^ (1 / 12 : ℝ) := by positivity
  calc (2 * π)⁻¹ * |_ - _| ≤ (2 * π)⁻¹ *
        (2 * (2 * π * (KH * (M ^ ((1 / 3 : ℝ) / 2) * δ ^ (1 / 12 : ℝ))) +
          2 * Pm * (72 * π * Real.sqrt (τ / r₀)))) := by
        refine mul_le_mul_of_nonneg_left (hsub.trans (le_of_eq ?_)) (by positivity)
        ring
    _ ≤ (2 * π)⁻¹ *
        (2 * (2 * π * (KH * (M ^ ((1 / 3 : ℝ) / 2) * δ ^ (1 / 12 : ℝ))) +
          2 * Pm * (72 * π) * (δ ^ (1 / 12 : ℝ) / Real.sqrt r₀))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [h3]
    _ = (2 * KH * M ^ ((1 / 3 : ℝ) / 2) + 144 * Pm / Real.sqrt r₀) * δ ^ (1 / 12 : ℝ) := by
        field_simp
        ring

end Coupling

end TwoPoint
end QuantumZipper
