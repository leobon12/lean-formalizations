import HigherDimLQGContinuity.Continuum.LowerEnergy

/-! Turning a finite extended-real crossing energy into a measurable real envelope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

def l2_lowerEnvelope {Ω : Type*} (X : Ω → ℝ≥0∞) (q : ℝ) (ω : Ω) : ℝ :=
  max 1 ((X ω).toReal ^ (1 / q))

theorem l2_measurable_lowerEnvelope {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ≥0∞} (hX : Measurable X) {q : ℝ} (hq : 0 < q) :
    Measurable (l2_lowerEnvelope X q) := by
  unfold l2_lowerEnvelope
  exact measurable_const.max
    ((Real.continuous_rpow_const (by positivity : 0 ≤ 1 / q)).measurable.comp
      (ENNReal.measurable_toReal.comp hX))

theorem l2_lowerEnvelope_one_le {Ω : Type*} (X : Ω → ℝ≥0∞) (q : ℝ) (ω : Ω) :
    1 ≤ l2_lowerEnvelope X q ω := le_max_left _ _

theorem l2_lowerEnvelope_pow {Ω : Type*} {X : Ω → ℝ≥0∞}
    {q : ℝ} (hq : 0 < q) {ω : Ω} (hX1 : 1 ≤ X ω)
    (hXtop : X ω ≠ ⊤) :
    (ENNReal.ofReal (l2_lowerEnvelope X q ω)) ^ q = X ω := by
  have hx1 : 1 ≤ (X ω).toReal := by
    exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hXtop).2 hX1
  have hqinv : 0 ≤ 1 / q := by positivity
  have hpow1 : 1 ≤ (X ω).toReal ^ (1 / q) :=
    Real.one_le_rpow hx1 hqinv
  have hH : l2_lowerEnvelope X q ω = (X ω).toReal ^ (1 / q) :=
    max_eq_right hpow1
  have hreal : (l2_lowerEnvelope X q ω) ^ q = (X ω).toReal := by
    rw [hH, ← Real.rpow_mul (by positivity : 0 ≤ (X ω).toReal)]
    have heq : (1 / q) * q = 1 := by field_simp
    rw [heq, Real.rpow_one]
  rw [ENNReal.ofReal_rpow_of_nonneg
    (by linarith [l2_lowerEnvelope_one_le X q ω]) hq.le, hreal,
    ENNReal.ofReal_toReal hXtop]

theorem l2_lowerEnvelope_moment_pointwise {Ω : Type*}
    {X : Ω → ℝ≥0∞} {q p : ℝ} (hq : 0 < q) (hpq : p < q)
    (ω : Ω) (hX1 : 1 ≤ X ω) :
    ENNReal.ofReal ((l2_lowerEnvelope X q ω) ^ p) ≤ X ω := by
  by_cases hXtop : X ω = ⊤
  · rw [hXtop]
    exact le_top
  have hx1 : 1 ≤ (X ω).toReal :=
    (ENNReal.toReal_le_toReal ENNReal.one_ne_top hXtop).2 hX1
  have hpow1 : 1 ≤ (X ω).toReal ^ (1 / q) :=
    Real.one_le_rpow hx1 (by positivity : 0 ≤ 1 / q)
  have hH : l2_lowerEnvelope X q ω = (X ω).toReal ^ (1 / q) :=
    max_eq_right hpow1
  have hpdiv : p / q ≤ 1 := (div_le_iff₀ hq).2 (by linarith)
  have hreal : (l2_lowerEnvelope X q ω) ^ p ≤ (X ω).toReal := by
    rw [hH, ← Real.rpow_mul (by positivity : 0 ≤ (X ω).toReal)]
    have heq : (1 / q) * p = p / q := by ring
    rw [heq]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx1 hpdiv
  calc
    ENNReal.ofReal ((l2_lowerEnvelope X q ω) ^ p) ≤
        ENNReal.ofReal (X ω).toReal := ENNReal.ofReal_le_ofReal hreal
    _ = X ω := ENNReal.ofReal_toReal hXtop

theorem l2_lowerEnergy_term_le {d : ℕ} (D : DistRd d → ContMetric d)
    (R β q : ℝ) (k : ℕ) {z : Rd d}
    (hz : z ∈ l2_lowerGrid d R k) (g : DistRd d) :
    l2_lowerTerm D β q k z g ≤ l2_lowerEnergy D R β q g := by
  calc
    l2_lowerTerm D β q k z g ≤ l2_lowerGridSum D R β q k g := by
      unfold l2_lowerGridSum
      exact Finset.single_le_sum
        (f := fun u => l2_lowerTerm D β q k u g)
        (fun i hi => show (0 : ℝ≥0∞) ≤ l2_lowerTerm D β q k i g from bot_le) hz
    _ ≤ ∑' j : ℕ, l2_lowerGridSum D R β q j g :=
      ENNReal.le_tsum (f := fun j => l2_lowerGridSum D R β q j g) k
    _ ≤ l2_lowerEnergy D R β q g := by
      unfold l2_lowerEnergy
      exact le_add_of_nonneg_left (zero_le_one : (0 : ℝ≥0∞) ≤ 1)

/-- Algebraic conversion from an inverse ratio bound to a crossing barrier. -/
theorem l2_ratio_to_cross {a Z H : ℝ≥0∞} (ha : a ≠ 0)
    (hH0 : H ≠ 0) (hHtop : H ≠ ⊤) (hratio : a * Z⁻¹ ≤ H) :
    a / H ≤ Z := by
  by_cases hZtop : Z = ⊤
  · rw [hZtop]
    exact le_top
  have hZ0 : Z ≠ 0 := by
    intro hz
    subst Z
    simp [ha, hHtop] at hratio
  have hmul : a ≤ H * Z := by
    have hh := mul_le_mul_of_nonneg_right hratio
      (show (0 : ℝ≥0∞) ≤ Z from bot_le)
    simpa only [mul_assoc, ENNReal.inv_mul_cancel hZ0 hZtop, mul_one] using hh
  exact (ENNReal.div_le_iff' hH0 hHtop).2 hmul

theorem l2_lowerEnvelope_grid_barrier {d : ℕ}
    {D : DistRd d → ContMetric d} {R β q : ℝ}
    (hq : 0 < q) {g : DistRd d}
    (hfinite : l2_lowerEnergy D R β q g ≠ ⊤) :
    ∀ k : ℕ, ∀ z ∈ l2_lowerGrid d R k,
      ENNReal.ofReal ((l2_lowerRadius k) ^ β /
        l2_lowerEnvelope (l2_lowerEnergy D R β q) q g) ≤
        acrossDist (rho D g) z (l2_lowerRadius k) (2 * l2_lowerRadius k) := by
  intro k z hz
  let X : ℝ≥0∞ := l2_lowerEnergy D R β q g
  let H : ℝ := l2_lowerEnvelope (l2_lowerEnergy D R β q) q g
  have hX1 : 1 ≤ X := by unfold X l2_lowerEnergy; exact le_add_of_nonneg_right bot_le
  have hH1 : 1 ≤ H := l2_lowerEnvelope_one_le _ q g
  have hHpos : 0 < H := by linarith
  have hHq : (ENNReal.ofReal H) ^ q = X :=
    l2_lowerEnvelope_pow hq hX1 hfinite
  let a : ℝ≥0∞ := ENNReal.ofReal ((l2_lowerRadius k) ^ β)
  let Z : ℝ≥0∞ := acrossDist (rho D g) z (l2_lowerRadius k) (2 * l2_lowerRadius k)
  have ha : a ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (l2_lowerRadius_pos k) β)).ne'
  have hterm : (a * Z⁻¹) ^ q ≤ X := by
    simpa only [X, a, Z, l2_lowerTerm] using
      l2_lowerEnergy_term_le D R β q k hz g
  have hratio : a * Z⁻¹ ≤ ENNReal.ofReal H := by
    rw [← hHq] at hterm
    exact (ENNReal.rpow_le_rpow_iff hq).mp hterm
  have hh := l2_ratio_to_cross ha
    (ENNReal.ofReal_pos.mpr hHpos).ne' ENNReal.ofReal_ne_top hratio
  simpa only [a, Z, H, ENNReal.ofReal_div_of_pos hHpos] using hh

end HigherDimLQGContinuity
