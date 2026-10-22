import HigherDimLQGMetric.Sphere.Law
import HigherDimLQGMetric.Field.SphereBump

/-!
# Mollified sphere bumps at a continuous scale

Packet F3 (Phase A, block A1). MA0 Details (a) D-F3.

`sphMol ε z r = ε^{-d} (sphBump 0 0 (r/ε))((· - z)/ε)` is the test function
`y ↦ ∫ ε^{-d} ψ_{0,0}((y - z - r u)/ε) dσ(u)`, i.e. the density of `z + r U + ε V`
(`posM_sphMol : posM (sphMol ε z r) = sphLaw r z ε`, `ε > 0`). At the dyadic scales it is F1's
`sphBump` (`sphMol_two_pow_inv : sphMol 2^{-n} z r = sphBump n z r`), so
`sphereAvgSeq h r z n = h (sphMol 2^{-n} z r)`; the continuous scale `ε` is the extra parameter
of the Kolmogorov argument of `Sphere/Cont.lean`.

Proof of `posM_sphMol` (own step): for measurable `A`, by Tonelli and the substitution
`y = z + r u + ε s` (Lebesgue measure: translation invariance and `map (ε •) vol = ε^{-d} vol`),
`∫_A sphMol = ∫ σ(du) ∫ 1_A(z + r u + ε s) ψ_{0,0}(s) ds = (σ ⊗ ψ_{0,0})(z + r U + ε V ∈ A)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- `σ_{r,z} * ψ_ε` with `ψ_ε = ε^{-d} ψ_{0,0}(·/ε)`, as a test function. -/
def sphMol (ε : ℝ) (z : Rd d) (r : ℝ) : TestRd d :=
  ((ε ^ d)⁻¹) • testAffinePull ε z (sphBump 0 0 (r / ε))

theorem sphMol_apply {ε : ℝ} (hε : ε ≠ 0) (z : Rd d) (r : ℝ) (y : Rd d) :
    sphMol ε z r y =
      ∫ u, (ε ^ d)⁻¹ * bumpTest 0 0 (ε⁻¹ • (y - (z + r • u))) ∂(unitSphereProb d) := by
  rw [sphMol, smul_apply, smul_eq_mul, testAffinePull_apply hε, sphBump_apply,
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only
  rw [bumpTest_apply_sub, zero_add]
  congr 2
  rw [smul_sub ε⁻¹ y (z + r • u), smul_add, smul_smul, inv_mul_eq_div, smul_sub, div_eq_inv_mul,
    mul_comm ε⁻¹ r]
  abel

/-- `ψ_{n,x}(y) = 2^{nd} ψ_{0,0}(2^n (y - x))`. -/
theorem bumpTest_eq_pow_mul (n : ℕ) (x y : Rd d) :
    bumpTest n x y = ((2 : ℝ) ^ n) ^ d * bumpTest 0 0 ((2 : ℝ) ^ n • (y - x)) := by
  rw [bumpTest_apply, bumpTest_apply, sub_zero, smul_smul, ← pow_add, zero_add, pow_one,
    ← mul_assoc, ← mul_assoc, ← mul_pow, ← pow_succ, add_comm 1 n]

theorem sphMol_two_pow_inv (n : ℕ) (z : Rd d) (r : ℝ) :
    sphMol ((2 : ℝ) ^ n)⁻¹ z r = sphBump n z r := by
  ext y
  rw [sphMol_apply (inv_ne_zero (by positivity)), sphBump_apply]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only
  rw [inv_inv, inv_pow, inv_inv, bumpTest_eq_pow_mul n (z + r • u) y]

theorem sphMol_nonneg {ε : ℝ} (hε : 0 < ε) (z : Rd d) (r : ℝ) (y : Rd d) :
    0 ≤ sphMol ε z r y := by
  rw [sphMol_apply hε.ne']
  exact integral_nonneg fun u => mul_nonneg (by positivity) (bumpTest_nonneg 0 0 _)

theorem integral_sphMol (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (z : Rd d) (r : ℝ) :
    ∫ y, sphMol ε z r y = 1 := by
  have h1 : ∫ y, sphMol ε z r y = (ε ^ d)⁻¹ * ∫ y, testAffinePull ε z (sphBump 0 0 (r / ε)) y := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    rw [sphMol, smul_apply, smul_eq_mul]
  rw [h1, integral_testAffinePull _ hε, integral_sphBump hd, mul_one,
    inv_mul_cancel₀ (by positivity)]

/-! ### `posM (sphMol ε z r) = sphLaw r z ε` -/

/-- `∫ g = ε^d ∫ g(x + ε s) ds` for Lebesgue measure on `ℝ^d`. -/
theorem lintegral_eq_ofReal_pow_mul_lintegral_comp {g : Rd d → ℝ≥0∞} (hg : Measurable g)
    {ε : ℝ} (hε : 0 < ε) (x : Rd d) :
    ∫⁻ y, g y = ENNReal.ofReal (ε ^ d) * ∫⁻ s, g (x + ε • s) := by
  have hmap := Measure.map_addHaar_smul (volume : Measure (Rd d)) hε.ne'
  rw [finrank_rd] at hmap
  have h1 : ∫⁻ s, g (x + ε • s) = ENNReal.ofReal ((ε ^ d)⁻¹) * ∫⁻ t, g (x + t) := by
    have := lintegral_map (μ := (volume : Measure (Rd d))) (f := fun t => g (x + t))
      (g := fun s => ε • s) (by fun_prop) (by fun_prop)
    rw [hmap, lintegral_smul_measure, smul_eq_mul,
      abs_of_pos (inv_pos.2 (pow_pos hε d))] at this
    exact this.symm
  rw [h1, lintegral_add_left_eq_self g x, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    mul_inv_cancel₀ (pow_pos hε d).ne', ENNReal.ofReal_one, one_mul]

/-- `sphLaw r z ε A = ∫ σ(du) (bumpLaw d){v | z + r u + ε v ∈ A}`. -/
theorem sphLaw_apply' (r : ℝ) (z : Rd d) (ε : ℝ) {A : Set (Rd d)} (hA : MeasurableSet A) :
    sphLaw r z ε A = ∫⁻ u, bumpLaw d {v | z + r • u + ε • v ∈ A} ∂(unitSphereProb d) := by
  rw [sphLaw, Measure.map_apply (measurable_sphLawFun r z ε) hA,
    Measure.prod_apply (measurable_sphLawFun r z ε hA)]
  rfl

theorem setLIntegral_ofReal_scaledBump {ε : ℝ} (hε : 0 < ε) (x : Rd d) {A : Set (Rd d)}
    (hA : MeasurableSet A) :
    ∫⁻ y in A, ENNReal.ofReal ((ε ^ d)⁻¹ * bumpTest 0 0 (ε⁻¹ • (y - x))) =
      bumpLaw d {v | x + ε • v ∈ A} := by
  set F : Rd d → ℝ≥0∞ := fun y => ENNReal.ofReal ((ε ^ d)⁻¹ * bumpTest 0 0 (ε⁻¹ • (y - x)))
    with hF
  have hFm : Measurable F := by
    refine Measurable.ennreal_ofReal (Measurable.const_mul ?_ _)
    exact (bumpTest 0 (0 : Rd d)).continuous.measurable.comp (by fun_prop)
  set S : Set (Rd d) := {v | x + ε • v ∈ A} with hS
  have hSm : MeasurableSet S := (by fun_prop : Measurable fun v : Rd d => x + ε • v) hA
  have hpt : ∀ s : Rd d, A.indicator F (x + ε • s) =
      ENNReal.ofReal ((ε ^ d)⁻¹) * S.indicator (fun v => ENNReal.ofReal (bumpTest 0 0 v)) s := by
    intro s
    by_cases hs : x + ε • s ∈ A
    · have hs' : s ∈ S := hs
      rw [indicator_of_mem hs, indicator_of_mem hs', hF]
      simp only
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hε.ne', one_smul,
        ENNReal.ofReal_mul (by positivity)]
    · have hs' : s ∉ S := hs
      rw [indicator_of_notMem hs, indicator_of_notMem hs', mul_zero]
  rw [← lintegral_indicator hA, lintegral_eq_ofReal_pow_mul_lintegral_comp (hFm.indicator hA) hε x]
  simp_rw [hpt]
  rw [lintegral_const_mul _ ((Measurable.ennreal_ofReal
      (bumpTest 0 (0 : Rd d)).continuous.measurable).indicator hSm),
    lintegral_indicator hSm, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    mul_inv_cancel₀ (pow_pos hε d).ne', ENNReal.ofReal_one, one_mul, bumpLaw, posM,
    withDensity_apply _ hSm]

/-- **The density of `z + r U + ε V`** is `sphMol ε z r` (`ε > 0`, `d ≥ 1`). -/
theorem posM_sphMol (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (z : Rd d) (r : ℝ) :
    posM (sphMol ε z r) = sphLaw r z ε := by
  have := isProbabilityMeasure_unitSphereProb hd
  ext A hA
  rw [sphLaw_apply' r z ε hA, posM, withDensity_apply _ hA]
  have hGc : Continuous fun p : Rd d × Rd d =>
      (ε ^ d)⁻¹ * bumpTest 0 0 (ε⁻¹ • (p.1 - (z + r • p.2))) := by
    refine continuous_const.mul ((bumpTest 0 (0 : Rd d)).continuous.comp ?_)
    fun_prop
  have hint : ∀ y, ENNReal.ofReal (sphMol ε z r y) = ∫⁻ u,
      ENNReal.ofReal ((ε ^ d)⁻¹ * bumpTest 0 0 (ε⁻¹ • (y - (z + r • u)))) ∂(unitSphereProb d) := by
    intro y
    have hcu : Continuous fun u : Rd d => (ε ^ d)⁻¹ * bumpTest 0 0 (ε⁻¹ • (y - (z + r • u))) := by
      refine continuous_const.mul ((bumpTest 0 (0 : Rd d)).continuous.comp ?_)
      fun_prop
    rw [sphMol_apply hε.ne', ofReal_integral_eq_lintegral_ofReal
      (integrable_unitSphereProb_of_continuous hcu)
      (ae_of_all _ fun u => mul_nonneg (by positivity) (bumpTest_nonneg 0 0 _))]
  simp_rw [hint]
  rw [lintegral_lintegral_swap (hGc.measurable.ennreal_ofReal.aemeasurable)]
  refine lintegral_congr fun u => ?_
  exact setLIntegral_ofReal_scaledBump hε (z + r • u) hA

/-- At the dyadic scales: `posM (sphBump n z r) = sphLaw r z 2^{-n}`. -/
theorem posM_sphBump (hd : 1 ≤ d) (n : ℕ) (z : Rd d) (r : ℝ) :
    posM (sphBump n z r) = sphLaw r z ((2 : ℝ) ^ n)⁻¹ := by
  rw [← sphMol_two_pow_inv, posM_sphMol hd (by positivity)]

theorem exists_isBddSupp_sphMol (ε : ℝ) (z : Rd d) (r : ℝ) :
    ∃ M D, IsBddSupp (fun y => sphMol ε z r y) M D :=
  exists_isBddSupp_testOn _

end HigherDimLQGMetric
