import LQGMetric.Field.CameronMartin

/-!
# Total variation of a Cameron–Martin shift of the whole-plane GFF (source §7, packet P-L2 T3)

Source: `source/small-parameter-lqg-geodesics.pdf`, §7 (the line after (7.4): "by the
Cameron–Martin relative entropy and Pinsker"), corrected in planning audit GA4
(`planning/audits/GA4-sections-7-8.md`), "Details for later use", item **A5**, and §(c), where the
first theorem below was compiled in scratch as `GA4.abs_lawPair0_addFun_sub_le'`.

Pinsker's inequality is not in Mathlib (ruling G13); GA4-6 replaces it by the χ² (L²) form of
Cameron–Martin, which gives the same order:

* `abs_lawPair0_addFun_sub_le`: for a whole-plane GFF `h`, a test function `φ` and a measurable set
  `A` of mean-zero pairings, `|P[h + φ ∈ A] − P[h ∈ A]| ≤ √(e^{‖φ‖²_∇} − 1)`;
* `abs_lawPair0_addFun_sub_le_sqrt_two`: if `‖φ‖²_∇ ≤ 1`, the bound is `≤ √(2 ‖φ‖²_∇)`
  (since `e^x − 1 ≤ 2x` on `[0, 1]`).

Here `‖φ‖²_∇ = (2π)⁻¹ ∫ |∇φ|²` is `LQGMetric.gradEnergy`, the source's (1.1). The bound is assembled from
`LQGMetric.shift_cm`, `LQGMetric.covNorm_cm` and `QuantumZipper.CameronMartin.abs_measureReal_shift_sub_le`.
The docstring of `LQGMetric/Field/CameronMartin.lean` advertises a declaration
`abs_lawPair0_addFun_sub_le` that no longer exists there; the statement is provided here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace SmallGammaGeodesics

open LQGMetric

/-- **Cameron–Martin total-variation bound** (GA4 A5): for a whole-plane GFF `h`, a test function
`φ` and a measurable set `A` of mean-zero pairings,
`|P[h + φ ∈ A] − P[h ∈ A]| ≤ √(e^{‖φ‖²_∇} − 1)`. -/
theorem abs_lawPair0_addFun_sub_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (φ : TestC)
    (A : Set (TestC0 → ℝ)) (hA : MeasurableSet A) :
    |(lawPair0 (fun ω => addFun (h ω) (testCont φ)) P).real A - (lawPair0 h P).real A| ≤
      Real.sqrt (Real.exp (gradEnergy φ) - 1) := by
  have key := QuantumZipper.CameronMartin.abs_measureReal_shift_sub_le
    (gaussian_pairProc hh)
    (fun ψ => (measurable_evalDist ψ.1).comp hh.measurable)
    (centered_pairProc hh) (Finsupp.single (cmTest0 φ) 1) A hA
  rw [covNorm_cm hh] at key
  unfold lawPair0
  rw [shift_cm hh]
  exact key

/-- The Dirichlet energy `(2π)⁻¹ ∫ |∇φ|²` is nonnegative. -/
theorem gradEnergy_nonneg (φ : ℂ → ℝ) : 0 ≤ gradEnergy φ := by
  unfold gradEnergy
  have hπ : 0 ≤ (2 * Real.pi)⁻¹ := inv_nonneg.2 (by positivity)
  exact mul_nonneg hπ (integral_nonneg fun z => sq_nonneg _)

/-- `e^x − 1 ≤ 2x` for `0 ≤ x ≤ 1`. -/
theorem exp_sub_one_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Real.exp x - 1 ≤ 2 * x := by
  have h := Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg hx0]; exact hx1)
  rw [abs_of_nonneg hx0] at h
  exact (le_abs_self _).trans h

/-- **Total variation for small Dirichlet energy** (GA4 A5): if `‖φ‖²_∇ ≤ 1`, then
`|P[h + φ ∈ A] − P[h ∈ A]| ≤ √(2 ‖φ‖²_∇)`. -/
theorem abs_lawPair0_addFun_sub_le_sqrt_two {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (φ : TestC) (hφ : gradEnergy φ ≤ 1)
    (A : Set (TestC0 → ℝ)) (hA : MeasurableSet A) :
    |(lawPair0 (fun ω => addFun (h ω) (testCont φ)) P).real A - (lawPair0 h P).real A| ≤
      Real.sqrt (2 * gradEnergy φ) :=
  (abs_lawPair0_addFun_sub_le hh φ A hA).trans
    (Real.sqrt_le_sqrt (exp_sub_one_le_two_mul (gradEnergy_nonneg φ) hφ))

end SmallGammaGeodesics
