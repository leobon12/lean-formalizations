import GaussianLQG.Metric.Rotation
import LQGMetric.Field.CircleAvgAffine

/-!
# Rotations preserve the normalized whole-plane GFF

Let `h` be a whole-plane GFF normalized by `h_1(0) = 0` (`LQGMetric.IsNormalizedWPGFF`) and let
`‖a‖ = 1`. Then `h(a·) = GaussianLQG.rotDist a h` is again a normalized whole-plane GFF
(`isNormalizedWPGFF_rotDist`), so by uniqueness of the law of the normalized field
(`LQGMetric.CircleAvg.map_eq_of_isNormalizedWPGFF`) it has the law of `h` (`map_rotDist_eq`).
This is the rotation part of the invariance in law `h(z + a·) − h_{|a|}(z) =ᵈ h` used for (S4) in
the proof of blueprint Proposition `prop:S2-S5`.

The whole-plane GFF part is `GaussianLQG.isWholePlaneGFF_rotDist`. The normalization needs
`(h(a·))_1(0) = h_1(0)` almost surely (`ae_circleAvg_rotDist`). The circle average
`LQGMetric.circleAvg` is the limit of the pairings of `h` with `Φ_n = circBump n 0 1`, a
mollification of the uniform measure on the unit circle by the bump `ψ_n = bumpTest n 0`. That bump
is a mathlib `ContDiffBump` whose profile is not known to be radial, so `Φ_n(a⁻¹ ·) ≠ Φ_n` in
general and the identity is not deterministic. We argue almost surely, as in
`LQGMetric.CircleAvg.ae_circleAvg_affineComp`: the log potential of `Φ_n(a⁻¹ ·)` at `x` is that of
`Φ_n` at `a⁻¹ x` (`logPot_testRot`), and both are within `2^{-n}` of `−log|x|₊`, which is rotation
invariant. Hence the mean-zero differences `Φ_n(a⁻¹ ·) − Φ_n` have variance at most `4 · 2^{-n}`
(`logCov_rotCircDiff_le`), the pairings of `h` with them tend to `0` almost surely
(Borel–Cantelli, `LQGMetric.CircleAvg.ae_tendsto_zero_of_sq_le`), and the two limits agree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace GaussianLQG

open LQGMetric LQGMetric.CircleAvg

/-! ## Log potentials under a rotation -/

/-- The log potential of `φ(a⁻¹ ·)` at `x` is the log potential of `φ` at `a⁻¹ x`, for
`‖a‖ = 1`. -/
lemma logPot_testRot {a : ℂ} (ha : ‖a‖ = 1) (φ : TestC) (x : ℂ) :
    logPot (testRot a φ) x = logPot φ (a⁻¹ * x) := by
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  unfold logPot
  simp only [testRot_apply ha0]
  rw [← integral_comp_mul_of_norm_eq_one ha]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e : x - a * u = a * (a⁻¹ * x - u) := by
    rw [mul_sub, mul_inv_cancel_left₀ ha0]
  simp only
  rw [inv_mul_cancel_left₀ ha0, e, norm_mul, ha, one_mul]

/-- `log|·|₊`, the circle-average potential of the unit circle, is rotation invariant. -/
lemma circLog_zero_one_inv_mul {a : ℂ} (ha : ‖a‖ = 1) (x : ℂ) :
    circLog 0 1 (a⁻¹ * x) = circLog 0 1 x := by
  rw [circLog_eq one_ne_zero, circLog_eq one_ne_zero, zero_sub, zero_sub, norm_neg, norm_neg,
    norm_mul, norm_inv, ha, inv_one, one_mul]

/-! ## The rotation differences of the mollified unit circle -/

/-- the mean-zero difference `Φ_n(a⁻¹ ·) − Φ_n` of the mollified unit circle and its rotation -/
def rotCircDiff {a : ℂ} (ha : ‖a‖ = 1) (n : ℕ) : TestC0 :=
  ⟨testRot a (circBump n 0 1) - circBump n 0 1, by
    show ∫ x, (testRot a (circBump n 0 1) x - circBump n 0 1 x) = 0
    rw [integral_sub (integrable_testC _) (integrable_testC _), integral_testRot ha, sub_self]⟩

lemma abs_logPot_rotCircDiff_le {a : ℂ} (ha : ‖a‖ = 1) (n : ℕ) (x : ℂ) :
    |logPot (rotCircDiff ha n).1 x| ≤ 2 * (2 : ℝ)⁻¹ ^ n := by
  show |logPot (⇑(testRot a (circBump n 0 1) - circBump n 0 1)) x| ≤ _
  rw [logPot_sub, logPot_testRot ha, logPot_circBump, logPot_circBump]
  have h1 := abs_integral_bump_circLog_sub_le one_pos n 0 (a⁻¹ * x)
  have h2 := abs_integral_bump_circLog_sub_le one_pos n 0 x
  have h3 := circLog_zero_one_inv_mul ha x
  rw [div_one] at h1 h2
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma testRot_circBump_nonneg {a : ℂ} (ha : ‖a‖ = 1) (n : ℕ) (y : ℂ) :
    0 ≤ testRot a (circBump n 0 1) y := by
  rw [testRot_apply (ne_zero_of_norm_eq_one ha)]
  exact circBump_nonneg _ _ _ _

/-- **Variance rate**: `Var⟨h, Φ_n(a⁻¹ ·) − Φ_n⟩ ≤ 4 · 2^{-n}`. -/
theorem logCov_rotCircDiff_le {a : ℂ} (ha : ‖a‖ = 1) (n : ℕ) :
    logCov (rotCircDiff ha n).1 (rotCircDiff ha n).1 ≤ 4 * (2 : ℝ)⁻¹ ^ n := by
  set D := rotCircDiff ha n
  set c := 2 * (2 : ℝ)⁻¹ ^ n
  rw [logCov_eq_integral_logPot]
  have hD : ∀ x, |D.1 x| ≤ testRot a (circBump n 0 1) x + circBump n 0 1 x := by
    intro x
    show |testRot a (circBump n 0 1) x - circBump n 0 1 x| ≤ _
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (testRot_circBump_nonneg ha _ _), abs_of_nonneg (circBump_nonneg _ _ _ _)]
  have hb : ∀ x, ‖D.1 x * logPot D.1 x‖ ≤
      (testRot a (circBump n 0 1) x + circBump n 0 1 x) * c := by
    intro x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hD x) (abs_logPot_rotCircDiff_le ha n x) (abs_nonneg _)
      (add_nonneg (testRot_circBump_nonneg ha _ _) (circBump_nonneg _ _ _ _))
  have hint : Integrable fun x => (testRot a (circBump n 0 1) x + circBump n 0 1 x) * c :=
    ((integrable_testC _).add (integrable_testC _)).mul_const c
  have := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans
    (norm_integral_le_of_norm_le hint (Eventually.of_forall hb)))
  refine this.trans (le_of_eq ?_)
  rw [integral_mul_const, integral_add (integrable_testC _) (integrable_testC _),
    integral_testRot ha, integral_circBump]
  simp only [c]
  ring

/-- The mollified circle averages of `h(a·)` are those of `h` plus the rotation differences. -/
lemma mollAvg_rotDist (a : ℂ) (ha : ‖a‖ = 1) (g : DistC) (n : ℕ) :
    mollAvg (rotDist a g) n 0 1 = mollAvg g n 0 1 + g (rotCircDiff ha n).1 := by
  rw [mollAvg_eq, mollAvg_eq, rotDist_apply]
  show g (testRot a (circBump n 0 1)) =
    g (circBump n 0 1) + g (testRot a (circBump n 0 1) - circBump n 0 1)
  rw [map_sub]
  ring

/-! ## The whole-plane GFF -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- **The unit circle average is a.s. rotation invariant**: for a whole-plane GFF `h` and
`‖a‖ = 1`, almost surely `(h(a·))_1(0) = h_1(0)`. -/
theorem ae_circleAvg_rotDist (hh : IsWholePlaneGFF h P) {a : ℂ} (ha : ‖a‖ = 1) :
    ∀ᵐ ω ∂P, circleAvg (rotDist a (h ω)) 1 0 = circleAvg (h ω) 1 0 := by
  have := hh.gaussian.isProbabilityMeasure
  have hE : ∀ᵐ ω ∂P, Tendsto (fun n => h ω (rotCircDiff ha n).1) atTop (𝓝 0) :=
    ae_tendsto_zero_of_sq_le (C := 4) (q := 2⁻¹)
      (fun n => (integral_sq_pair hh _).1) (by norm_num) (by norm_num)
      fun n => (integral_sq_pair hh _).2.trans_le (logCov_rotCircDiff_le ha n)
  filter_upwards [ae_tendsto_mollAvg hh 0 one_pos, hE] with ω ⟨b, hb⟩ hω
  rw [circleAvg_eq_of_tendsto hb]
  refine circleAvg_eq_of_tendsto ?_
  simp_rw [mollAvg_rotDist a ha]
  simpa only [add_zero] using hb.add hω

/-- **Rotations preserve the normalized whole-plane GFF**: if `h` is a whole-plane GFF normalized
by `h_1(0) = 0` and `‖a‖ = 1`, then so is `h(a·) = rotDist a h`. -/
theorem isNormalizedWPGFF_rotDist (hh : IsNormalizedWPGFF h P) {a : ℂ} (ha : ‖a‖ = 1) :
    IsNormalizedWPGFF (fun ω => rotDist a (h ω)) P := by
  refine ⟨isWholePlaneGFF_rotDist hh.1 ha, ?_⟩
  filter_upwards [ae_circleAvg_rotDist hh.1 ha, hh.2] with ω h1 h2
  rw [h1, h2]

/-- `g ↦ rotDist a g` is measurable on `𝒟'(ℂ)`. -/
theorem measurable_rotDist (a : ℂ) : Measurable (rotDist a) :=
  GFFInv.measurable_distC_iff.2 fun φ => GFFInv.measurable_pair (testRot a φ)

/-- **Rotation invariance in law of the normalized whole-plane GFF**: for `‖a‖ = 1`, `h(a·)` has
the law of `h`. -/
theorem map_rotDist_eq (hh : IsNormalizedWPGFF h P) {a : ℂ} (ha : ‖a‖ = 1) :
    P.map (fun ω => rotDist a (h ω)) = P.map h :=
  map_eq_of_isNormalizedWPGFF (isNormalizedWPGFF_rotDist hh ha) hh

end GaussianLQG
