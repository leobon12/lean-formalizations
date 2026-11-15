/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedSource
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessDeriv
import InteractingSLE.Spec.ZhanGT4.MTildeBoundField

/-!
# Uniform local bounds for the fused opposite-view field

Packet PROVE-ZHAN-GT4-A22. Bounds depend only on the raw-field bound,
the source scale and the protected source gap, never on a path or time.
-/

set_option autoImplicit false
noncomputable section
open Set Complex
namespace InteractingSLE.ZhanGT4

/-- A common bound for the fused logarithm and its four formal derivatives. -/
def seedAccessBound (κ R K L c : ℝ) : ℝ := K +
  |dualGamma κ R| * L + |R| * L + |R| / c + |R| / c ^ 2 +
    2 * |R| / c ^ 3 + 2 * |dualGamma κ R| / c ^ 2 + 2 * |R| / c ^ 2

theorem seedAccessBound_nonneg {κ R K L c : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hc : 0 < c) :
    0 ≤ seedAccessBound κ R K L c := by unfold seedAccessBound; positivity

private theorem abs_div_pow_le {a x c : ℝ} (hc : 0 < c) (hx : c ≤ |x|) (k : ℕ) :
    |a / x ^ k| ≤ |a| / c ^ k := by
  rw [abs_div, abs_pow]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hc k)
    (pow_le_pow_left₀ hc.le hx k)

namespace FrzData
variable {n : ℕ} (d : FrzData n)

/-- The actual fused field inherits a uniform local bound from the raw
field and the separated-source scale. The spatial gap need not have a sign. -/
theorem seedAccess_bounds {p t x K L c : ℝ} (hL : 0 ≤ L) (hc : 0 < c)
    (hb : |d.ell t x| ≤ K ∧ |d.LSX t x| ≤ K ∧ |d.LSXX t x| ≤ K ∧
      |d.LSXXX t x| ≤ K ∧ |d.ellT t x| ≤ K)
    (hG : |Real.log (deriv (QuantumZipper.fwdMap d.W t) p).re| ≤ L)
    (hlog : |Real.log (x - d.seedAccessSource p t)| ≤ L)
    (hx : c ≤ |x - d.seedAccessSource p t|)
    (hE : c ≤ |d.seedAccessSource p t - d.W t|) :
    |d.seedAccessEll p t x| ≤ seedAccessBound d.κ d.seedAccessExponent K L c ∧
    |d.seedAccessX p t x| ≤ seedAccessBound d.κ d.seedAccessExponent K L c ∧
    |d.seedAccessXX p t x| ≤ seedAccessBound d.κ d.seedAccessExponent K L c ∧
    |d.seedAccessXXX p t x| ≤ seedAccessBound d.κ d.seedAccessExponent K L c ∧
    |d.seedAccessT p t x| ≤ seedAccessBound d.κ d.seedAccessExponent K L c := by
  have b0 : |d.seedAccessEll p t x| ≤ K + |dualGamma d.κ d.seedAccessExponent| * L +
      |d.seedAccessExponent| * L := by
    exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
      (add_le_add hb.1 (abs_mul_le_of_le le_rfl hG))) (abs_mul_le_of_le le_rfl hlog))
  have b1 : |d.seedAccessX p t x| ≤ K + |d.seedAccessExponent| / c :=
    (abs_sub _ _).trans (add_le_add hb.2.1 (by
      simpa only [pow_one] using (abs_div_pow_le (a := d.seedAccessExponent) hc hx 1)))
  have b2 : |d.seedAccessXX p t x| ≤ K + |d.seedAccessExponent| / c ^ 2 :=
    (abs_add_le _ _).trans (add_le_add hb.2.2.1 (abs_div_pow_le hc hx 2))
  have b3 : |d.seedAccessXXX p t x| ≤ K + 2 * |d.seedAccessExponent| / c ^ 3 := by
    have hh := abs_div_pow_le (a := 2 * d.seedAccessExponent) hc hx 3
    rw [abs_mul, abs_two] at hh
    exact (abs_sub _ _).trans (add_le_add hb.2.2.2.1 hh)
  have bt1 : |2 * dualGamma d.κ d.seedAccessExponent /
      (d.seedAccessSource p t - d.W t) ^ 2| ≤ 2 * |dualGamma d.κ d.seedAccessExponent| / c ^ 2 := by
    simpa only [abs_mul, abs_two] using
        abs_div_pow_le (a := 2 * dualGamma d.κ d.seedAccessExponent) hc hE 2
  have bt2 : |d.seedAccessExponent * (2 / (d.seedAccessSource p t - d.W t)) /
      (x - d.seedAccessSource p t)| ≤ 2 * |d.seedAccessExponent| / c ^ 2 := by
    have hprod : c ^ 2 ≤ |(d.seedAccessSource p t - d.W t) * (x - d.seedAccessSource p t)| := by
      rw [abs_mul, pow_two]
      exact mul_le_mul hE hx hc.le (abs_nonneg _)
    have hh := div_le_div_of_nonneg_left (abs_nonneg (2 * d.seedAccessExponent))
      (sq_pos_of_pos hc) hprod
    have he : d.seedAccessExponent * (2 / (d.seedAccessSource p t - d.W t)) /
        (x - d.seedAccessSource p t) = (2 * d.seedAccessExponent) /
          ((d.seedAccessSource p t - d.W t) * (x - d.seedAccessSource p t)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he, abs_div, abs_mul, abs_two]
    simpa only [abs_mul, abs_two] using hh
  have bt : |d.seedAccessT p t x| ≤ K + 2 * |dualGamma d.κ d.seedAccessExponent| / c ^ 2 +
      2 * |d.seedAccessExponent| / c ^ 2 :=
    (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hb.2.2.2.2 bt1)) bt2)
  have n0 : 0 ≤ |dualGamma d.κ d.seedAccessExponent| * L := by positivity
  have n1 : 0 ≤ |d.seedAccessExponent| * L := by positivity
  have n2 : 0 ≤ |d.seedAccessExponent| / c := by positivity
  have n3 : 0 ≤ |d.seedAccessExponent| / c ^ 2 := by positivity
  have n4 : 0 ≤ 2 * |d.seedAccessExponent| / c ^ 3 := by positivity
  have n5 : 0 ≤ 2 * |dualGamma d.κ d.seedAccessExponent| / c ^ 2 := by positivity
  have n6 : 0 ≤ 2 * |d.seedAccessExponent| / c ^ 2 := by positivity
  unfold seedAccessBound
  exact ⟨by linarith only [b0, n2, n3, n4, n5, n6],
    by linarith only [b1, n0, n1, n3, n4, n5, n6],
    by linarith only [b2, n0, n1, n2, n4, n5, n6],
    by linarith only [b3, n0, n1, n2, n3, n5, n6],
    by linarith only [bt, n0, n1, n2, n3, n4]⟩

end FrzData
end InteractingSLE.ZhanGT4
