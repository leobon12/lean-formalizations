import GaussianLQG.Core.Defs
import GaussianLQG.LQG.Euclid.Basic

/-!
# Union bound and grid filling (blueprint Lemma `lem:euclidean`, Steps 3 and 4)

* `le_rpow_sum_rpow`, `eLpNorm_rpow_sum_rpow_le`: the maximum over a finite family is dominated by
  `M = (∑_i f_i^p)^{1/p}`, and `‖M‖_p ≤ (#s)^{1/p} max_i ‖f_i‖_p` (union bound).
* `abs_euclid_sub_le`: for a metric `d`, `e ≥ 0` and points `z, w, z', w'`,
  `|e d(z,w) - |z-w|| ≤ |e d(z',w') - |z'-w'|| + e (d(z,z') + d(w,w')) + |z - z'| + |w - w'|`.
* `rpow_card_mul_le`: the exponent bookkeeping `n^{1/P₀} K ξ ≤ (2R+5) K ξ^{1/2}` when
  `n ≤ ((2R+5)/ξ)⁴`, `P₀ ≥ 8` and `ξ ≤ 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaussianLQG

/-- A term of a finite family is at most `(∑_j f_j^p)^{1/p}`. -/
theorem le_rpow_sum_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) {i : ι}
    (hi : i ∈ s) : f i ≤ (∑ j ∈ s, f j ^ p) ^ (1 / p) := by
  calc f i = (f i ^ p) ^ (1 / p) := by
        rw [one_div, ENNReal.rpow_rpow_inv hp.ne']
    _ ≤ (∑ j ∈ s, f j ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (Finset.single_le_sum (f := fun j => f j ^ p) (fun j _ => zero_le) hi)
          (by positivity)

/-- **Union bound.** If `‖f_i‖_p ≤ B` for every `i ∈ s`, then
`‖(∑_{i ∈ s} f_i^p)^{1/p}‖_p ≤ (#s)^{1/p} B`. -/
theorem eLpNorm_rpow_sum_rpow_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) {f : ι → Ω → ℝ≥0∞} (hf : ∀ i ∈ s, Measurable (f i)) {p : ℝ} (hp : 0 < p)
    {B : ℝ≥0∞} (hB : ∀ i ∈ s, eLpNorm (f i) (ENNReal.ofReal p) μ ≤ B) :
    eLpNorm (fun ω => (∑ i ∈ s, f i ω ^ p) ^ (1 / p)) (ENNReal.ofReal p) μ ≤
      (s.card : ℝ≥0∞) ^ (1 / p) * B := by
  rw [eLpNorm_ofReal_eq hp]
  simp_rw [enorm_eq_self]
  have hpow : ∀ ω, ((∑ i ∈ s, f i ω ^ p) ^ (1 / p)) ^ p = ∑ i ∈ s, f i ω ^ p := fun ω => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  simp_rw [hpow]
  rw [lintegral_finsetSum' s fun i hi => ((hf i hi).pow_const p).aemeasurable]
  have hterm : ∀ i ∈ s, ∫⁻ ω, f i ω ^ p ∂μ ≤ B ^ p := by
    intro i hi
    have h := lintegral_enorm_rpow_eq (μ := μ) hp (f i)
    simp_rw [enorm_eq_self] at h
    rw [h]
    exact ENNReal.rpow_le_rpow (hB i hi) hp.le
  calc (∑ i ∈ s, ∫⁻ ω, f i ω ^ p ∂μ) ^ (1 / p) ≤ (∑ _i ∈ s, B ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (Finset.sum_le_sum hterm) (by positivity)
    _ = ((s.card : ℝ≥0∞) * B ^ p) ^ (1 / p) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (s.card : ℝ≥0∞) ^ (1 / p) * B := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- **Grid filling.** For a metric `d = D.1`, `e ≥ 0` and points `z, w, z', w'`:
`|e d(z,w) - |z - w|| ≤ |e d(z',w') - |z' - w'|| + e (d(z,z') + d(w,w'))
  + (|z - z'| + |w - w'|)`. -/
theorem abs_euclid_sub_le (D : LQGMetric.ContMetric) {e : ℝ} (he : 0 ≤ e) (z w z' w' : ℂ) :
    |e * D.1 (z, w) - ‖z - w‖| ≤ |e * D.1 (z', w') - ‖z' - w'‖| +
      e * (D.1 (z, z') + D.1 (w, w')) + (‖z - z'‖ + ‖w - w'‖) := by
  have hm := D.2.toIsMetricFn
  have t1 : D.1 (z, w) ≤ D.1 (z, z') + D.1 (z', w') + D.1 (w, w') := by
    have h1 := hm.triangle z z' w
    have h2 := hm.triangle z' w' w
    have h3 := hm.symm w' w
    linarith
  have t2 : D.1 (z', w') ≤ D.1 (z, z') + D.1 (z, w) + D.1 (w, w') := by
    have h1 := hm.triangle z' z w'
    have h2 := hm.triangle z w w'
    have h3 := hm.symm z' z
    linarith
  have e1 := mul_le_mul_of_nonneg_left t1 he
  have e2 := mul_le_mul_of_nonneg_left t2 he
  have n1 : ‖z - w‖ ≤ ‖z - z'‖ + ‖z' - w'‖ + ‖w - w'‖ := by
    have h1 := norm_sub_le_norm_sub_add_norm_sub z z' w
    have h2 := norm_sub_le_norm_sub_add_norm_sub z' w' w
    rw [norm_sub_rev w' w] at h2
    linarith
  have n2 : ‖z' - w'‖ ≤ ‖z - z'‖ + ‖z - w‖ + ‖w - w'‖ := by
    have h1 := norm_sub_le_norm_sub_add_norm_sub z' z w'
    have h2 := norm_sub_le_norm_sub_add_norm_sub z w w'
    rw [norm_sub_rev z' z] at h1
    linarith
  have a1 := le_abs_self (e * D.1 (z', w') - ‖z' - w'‖)
  have a2 := neg_abs_le (e * D.1 (z', w') - ‖z' - w'‖)
  rw [abs_le]
  constructor <;> nlinarith

/-- Exponent bookkeeping for the union bound: if `n ≤ ((2R+5)/ξ)⁴`, `P₀ ≥ 8`, `0 < ξ ≤ 1`,
`R ≥ 0` and `K ≥ 0`, then `n^{1/P₀} (K ξ) ≤ (2R+5) K ξ^{1/2}`. -/
theorem rpow_card_mul_le {n R ξ K P0 : ℝ} (hn0 : 0 ≤ n) (hn : n ≤ ((2 * R + 5) / ξ) ^ 4)
    (hP0 : 8 ≤ P0) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hR : 0 ≤ R) (hK : 0 ≤ K) :
    n ^ (1 / P0) * (K * ξ) ≤ (2 * R + 5) * K * Real.sqrt ξ := by
  have hP0' : 0 < P0 := by linarith
  have hA : 1 ≤ 2 * R + 5 := by linarith
  have hx0 : 0 ≤ (2 * R + 5) / ξ := by positivity
  have h1 : n ^ (1 / P0) ≤ (2 * R + 5) ^ (4 / P0) / ξ ^ (4 / P0) := by
    calc n ^ (1 / P0) ≤ (((2 * R + 5) / ξ) ^ 4) ^ (1 / P0) :=
          Real.rpow_le_rpow hn0 hn (by positivity)
      _ = ((2 * R + 5) / ξ) ^ (4 / P0) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
          congr 1
          push_cast
          ring
      _ = (2 * R + 5) ^ (4 / P0) / ξ ^ (4 / P0) := Real.div_rpow (by linarith) hξ.le _
  have h2 : (2 * R + 5) ^ (4 / P0) ≤ 2 * R + 5 := by
    calc (2 * R + 5) ^ (4 / P0) ≤ (2 * R + 5) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hA (by rw [div_le_one hP0']; linarith)
      _ = 2 * R + 5 := Real.rpow_one _
  have h3 : ξ / ξ ^ (4 / P0) ≤ Real.sqrt ξ := by
    rw [← Real.rpow_one_sub' hξ.le, Real.sqrt_eq_rpow]
    · refine Real.rpow_le_rpow_of_exponent_ge hξ hξ1 ?_
      rw [show (1 : ℝ) - 4 / P0 = 1 - 4 / P0 from rfl]
      have : 4 / P0 ≤ 1 / 2 := by rw [div_le_iff₀ hP0']; linarith
      linarith
    · have : 4 / P0 ≤ 1 / 2 := by rw [div_le_iff₀ hP0']; linarith
      linarith
  have hξp : 0 < ξ ^ (4 / P0) := Real.rpow_pos_of_pos hξ _
  calc n ^ (1 / P0) * (K * ξ) ≤ (2 * R + 5) ^ (4 / P0) / ξ ^ (4 / P0) * (K * ξ) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2 * R + 5) ^ (4 / P0) * K * (ξ / ξ ^ (4 / P0)) := by
        field_simp
    _ ≤ (2 * R + 5) * K * Real.sqrt ξ := by
        gcongr

end GaussianLQG
