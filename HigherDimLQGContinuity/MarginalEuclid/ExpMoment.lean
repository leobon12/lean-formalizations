import HigherDimLQGContinuity.MarginalEuclid.UnitLaw
import GaussianLQG.LQG.Euclid.Basic

/-!
# Exponential moments of the log unit distance

The Gaussian concentration interface supplies moments of every order. A
nonnegative power series turns these into a uniform exponential moment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

theorem n5_exp_series (t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp t) =
      ∑' n : ℕ, ENNReal.ofReal (t ^ n / n.factorial) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  exact ENNReal.ofReal_tsum_of_nonneg (fun n => div_nonneg (pow_nonneg ht _) (Nat.cast_nonneg _))
    (Real.summable_pow_div_factorial t)
theorem n5_term (lam x : ℝ) (hlam : 0 ≤ lam) (n : ℕ) :
    ENNReal.ofReal ((lam * |x|) ^ n / n.factorial) =
      ENNReal.ofReal (lam ^ n / n.factorial) * ENNReal.ofReal (|x| ^ n) := by
  have h : (lam * |x|) ^ n / (n.factorial : ℝ) =
      (lam ^ n / n.factorial) * |x| ^ n := by
    rw [mul_pow]
    ring
  rw [h, ENNReal.ofReal_mul (div_nonneg (pow_nonneg hlam n) (Nat.cast_nonneg _))]
theorem n5_moment_term_bound (lam A : ℝ) (hlam : 0 ≤ lam) (hA : 0 ≤ A)
    (hsmall : lam * A * Real.exp 1 ≤ 1 / 2) (n : ℕ) :
    (lam * A * n) ^ n / n.factorial ≤ (1 / 2 : ℝ) ^ n := by
  have hfact := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg _) n
  have hfacpos : (0 : ℝ) ≤ (n.factorial : ℝ) := Nat.cast_nonneg _
  have hbase : 0 ≤ lam * A := mul_nonneg hlam hA
  calc
    (lam * A * n) ^ n / n.factorial = (lam * A) ^ n * ((n : ℝ) ^ n / n.factorial) := by ring
    _ ≤ (lam * A) ^ n * Real.exp n := mul_le_mul_of_nonneg_left hfact (pow_nonneg hbase _)
    _ = (lam * A * Real.exp 1) ^ n := by
      rw [show Real.exp (n : ℝ) = (Real.exp 1) ^ n by
        simpa only [mul_one] using (Real.exp_nat_mul 1 n)]
      exact (mul_pow (lam * A) (Real.exp 1) n).symm
    _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ (mul_nonneg hbase (Real.exp_nonneg _)) hsmall _
theorem n5_exp_moment_generic {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (A lam : ℝ) (hA : 0 ≤ A) (hlam : 0 ≤ lam)
    (hsmall : lam * A * Real.exp 1 ≤ 1 / 2)
    (hmom : ∀ n : ℕ, 1 ≤ n →
      ∫⁻ ω, ENNReal.ofReal (|X ω| ^ n) ∂μ ≤ ENNReal.ofReal ((A * n) ^ n)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ ≤ 2 := by
  let f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal ((lam * |X ω|) ^ n / n.factorial)
  have hfmeas (n : ℕ) : Measurable (f n) := by
    unfold f
    exact ENNReal.measurable_ofReal.comp
      (((measurable_const.mul (continuous_abs.measurable.comp hX)).pow_const n).div_const _)
  have hseries (ω : Ω) : ENNReal.ofReal (Real.exp (lam * |X ω|)) = ∑' (n : ℕ), f n ω :=
    n5_exp_series _ (mul_nonneg hlam (abs_nonneg _))
  have hterm (n : ℕ) : ∫⁻ ω, f n ω ∂μ ≤
      ENNReal.ofReal ((lam * A * n) ^ n / n.factorial) := by
    by_cases hn : n = 0
    · subst n
      simp only [f, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one,
        lintegral_const, measure_univ, mul_one]
      exact le_rfl
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hconst : ∀ ω, f n ω =
          ENNReal.ofReal (lam ^ n / n.factorial) * ENNReal.ofReal (|X ω| ^ n) :=
        fun ω => n5_term lam (X ω) hlam n
      simp_rw [hconst]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc
        ENNReal.ofReal (lam ^ n / n.factorial) *
            ∫⁻ ω, ENNReal.ofReal (|X ω| ^ n) ∂μ
          ≤ ENNReal.ofReal (lam ^ n / n.factorial) * ENNReal.ofReal ((A * n) ^ n) :=
              by
                gcongr
                exact hmom n hn1
        _ = ENNReal.ofReal ((lam * A * n) ^ n / n.factorial) := by
          rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hlam _) (Nat.cast_nonneg _))]
          congr 1
          rw [mul_pow]
          ring
  calc
    ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * |X ω|)) ∂μ
      = ∑' (n : ℕ), ∫⁻ ω, f n ω ∂μ := by
        simp_rw [hseries]
        exact lintegral_tsum fun n => (hfmeas n).aemeasurable
    _ ≤ ∑' (n : ℕ), ENNReal.ofReal ((lam * A * n) ^ n / n.factorial) :=
      ENNReal.tsum_le_tsum hterm
    _ ≤ ∑' (n : ℕ), ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
      ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal
        (n5_moment_term_bound lam A hlam hA hsmall n)
    _ = 2 := by
      simp_rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [ENNReal.tsum_geometric]
      norm_num [ENNReal.ofReal_div_of_pos]

/-- Convert an `Lⁿ` bound into the corresponding lower-integral moment bound. -/
theorem n5_lintegral_abs_pow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (n : ℕ) (hn : 0 < n) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm X (ENNReal.ofReal n) μ ≤ ENNReal.ofReal B) :
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ n) ∂μ ≤ ENNReal.ofReal (B ^ n) := by
  have heq : (∫⁻ ω, ENNReal.ofReal (|X ω| ^ n) ∂μ) =
      eLpNorm X (ENNReal.ofReal n) μ ^ (n : ℝ) := by
    have h0 : (0 : ℝ) < n := by exact_mod_cast hn
    convert GaussianLQG.lintegral_enorm_rpow_eq h0 X using 1
    · congr 1
      funext ω
      rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_natCast,
        ← ENNReal.ofReal_pow (abs_nonneg _)]
  rw [heq, ENNReal.rpow_natCast]
  simpa only [ENNReal.ofReal_pow hB] using (pow_le_pow_left₀ (by positivity) h n)

/-- Integer moments from a fixed concentration witness, including order one. -/
theorem n5_moments_logRho {d : ℕ} (hd : 3 ≤ d) {ξ₂ C : ℝ}
    (hC0 : 0 ≤ C)
    (hbound : ∀ ξ ∈ Ioc (0 : ℝ) ξ₂, ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D → ∀ p : ℝ, 2 ≤ p →
      eLpNorm (fun g => Real.log ((rho D g).1 (0, e₁ d)))
        (ENNReal.ofReal p) (normLGFLaw d) ≤ ENNReal.ofReal (C * p * ξ))
    {ξ : ℝ} (hξint : ξ ∈ Ioc (0 : ℝ) ξ₂)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D) :
    ∀ n : ℕ, 1 ≤ n →
      ∫⁻ g, ENNReal.ofReal
          (|Real.log ((rho D g).1 (0, e₁ d))| ^ n) ∂(normLGFLaw d) ≤
        ENNReal.ofReal ((2 * C * ξ * n) ^ n) := by
  intro n hn
  have hξ : 0 < ξ := hξint.1
  have hξle : ξ ≤ ξ₂ := hξint.2
  letI : IsProbabilityMeasure (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
  let X : DistRd d → ℝ := fun g => Real.log ((rho D g).1 (0, e₁ d))
  have hX : Measurable X := measurable_log_rho_apply hD.measurable _
  have hCξ : 0 ≤ C * ξ := mul_nonneg hC0 hξ.le
  have hbase : 0 ≤ 2 * C * ξ * n := by positivity
  by_cases hn2 : 2 ≤ n
  · have hp : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hb := hbound ξ ⟨hξ, hξle⟩ D hD (n : ℝ) hp
    have hM := n5_lintegral_abs_pow_le n (by omega) (by positivity : 0 ≤ C * n * ξ) hb
    apply hM.trans
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (by positivity : 0 ≤ C * n * ξ)
    nlinarith [mul_nonneg hC0 hξ.le]
  · have hn1 : n = 1 := by omega
    subst n
    have h2 := hbound ξ ⟨hξ, hξle⟩ D hD 2 (by norm_num)
    have hmono : eLpNorm X (ENNReal.ofReal (1 : ℝ)) (normLGFLaw d) ≤
        eLpNorm X (ENNReal.ofReal (2 : ℝ)) (normLGFLaw d) := by
      apply eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      exact hX.aestronglyMeasurable
    have h2' : eLpNorm X (ENNReal.ofReal (1 : ℝ)) (normLGFLaw d) ≤
        ENNReal.ofReal (2 * C * ξ) := by
      calc
        _ ≤ ENNReal.ofReal (C * 2 * ξ) := hmono.trans h2
        _ = _ := by congr 1; ring
    have hM := n5_lintegral_abs_pow_le (X := X) (μ := normLGFLaw d) 1 (by norm_num)
      (by positivity : 0 ≤ 2 * C * ξ) (by simpa only [Nat.cast_one] using h2')
    simpa only [Nat.cast_one, mul_one] using hM

/-- Exponential moments of the log normalized unit distance, uniformly for small parameters. -/
theorem expMoment_logRho_le {d : ℕ} (hd : 3 ≤ d)
    (hC : ConcentrationStmt d) (hR : StrongRotLaw d) :
    ∃ ξ₂ C₃ : ℝ, 0 < ξ₂ ∧ 1 ≤ C₃ ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξ₂, Real.sqrt (2 * d) < distExp d ξ →
        ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
          ∀ u : Rd d, ‖u‖ = 1 → ∀ lam : ℝ, 0 ≤ lam →
            lam ≤ (2 * Real.exp 1 * C₃ * ξ)⁻¹ →
              ∫⁻ g, ENNReal.ofReal
                (Real.exp (lam * |Real.log ((rho D g).1 (0, u))|)) ∂(normLGFLaw d) ≤ 2 := by
  obtain ⟨ξ₂, C, hξ₂, hC0, hbound⟩ := hC
  refine ⟨ξ₂, max 1 (2 * C), hξ₂, le_max_left _ _, ?_⟩
  intro ξ hξint hgap D hD u hu lam hlam hlamle
  have hξ : 0 < ξ := hξint.1
  letI : IsProbabilityMeasure (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
  let X : DistRd d → ℝ := fun g => Real.log ((rho D g).1 (0, e₁ d))
  have hX : Measurable X := measurable_log_rho_apply hD.measurable _
  have hmom : ∀ n : ℕ, 1 ≤ n →
      ∫⁻ g, ENNReal.ofReal (|X g| ^ n) ∂(normLGFLaw d) ≤
        ENNReal.ofReal ((2 * C * ξ * n) ^ n) :=
    n5_moments_logRho hd hC0 hbound hξint hD
  have hA : 0 ≤ 2 * C * ξ := by positivity
  have hsmall : lam * (2 * C * ξ) * Real.exp 1 ≤ 1 / 2 := by
    have hCmax : 2 * C ≤ max 1 (2 * C) := le_max_right _ _
    have hmaxpos : 0 < max 1 (2 * C) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hden : 0 < 2 * Real.exp 1 * max 1 (2 * C) * ξ := by positivity
    have hprod := mul_le_mul_of_nonneg_right hlamle hden.le
    rw [inv_mul_cancel₀ hden.ne'] at hprod
    have hcmp : lam * (2 * C * ξ) * Real.exp 1 ≤
        lam * (max 1 (2 * C) * ξ) * Real.exp 1 := by
      have := mul_le_mul_of_nonneg_left hCmax (mul_nonneg hlam hξ.le)
      nlinarith [Real.exp_pos 1]
    nlinarith [Real.exp_pos 1]
  have hunit : ∫⁻ g, ENNReal.ofReal (Real.exp (lam * |X g|)) ∂(normLGFLaw d) ≤ 2 :=
    n5_exp_moment_generic (normLGFLaw d) X hX (2 * C * ξ) lam hA hlam hsmall hmom
  let F : ℝ → ℝ≥0∞ := fun a => ENNReal.ofReal (Real.exp (lam * |Real.log a|))
  have hF : Measurable F := by
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (continuous_abs.measurable.comp Real.measurable_log)))
  have hmu : Measurable (fun g : DistRd d => (rho D g).1 (0, u)) :=
    p2_measurable_contMetric_apply (measurable_rho hD.measurable) _
  have hme : Measurable (fun g : DistRd d => (rho D g).1 (0, e₁ d)) :=
    p2_measurable_contMetric_apply (measurable_rho hD.measurable) _
  have hlaw := law_rho_unit hd hR hξ hgap hD hu
  have htransfer : (∫⁻ g, F ((rho D g).1 (0, u)) ∂(normLGFLaw d)) =
      ∫⁻ g, F ((rho D g).1 (0, e₁ d)) ∂(normLGFLaw d) := by
    rw [← lintegral_map hF hmu, hlaw, lintegral_map hF hme]
  exact htransfer.trans_le hunit

end HigherDimLQGContinuity
