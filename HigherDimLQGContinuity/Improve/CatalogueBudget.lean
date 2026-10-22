import HigherDimLQGContinuity.Improve.BinLower
import HigherDimLQGContinuity.Improve.GainParams

/-!
# Uniform gain and error budgets for every catalogue in the class family
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- Every class in the finite union has a bin at least one quarter of the
nominal lower unit. The factor four accounts for the endpoint padding of
`s7b_binIndices`. -/
theorem q11_class_bin_lower {d : ℕ} {V Δ K0 : ℝ}
    (hΔ : 0 < Δ) {cl : ℕ × (Fin d → ℤ) × ℤ}
    (hcl : cl ∈ q11ClassSet d V Δ K0) :
    Δ ^ K0 / 4 ≤ (2 : ℝ) ^ cl.2.2 := by
  have hbin : cl.2.2 ∈ s7b_binIndices (Δ ^ K0) (Δ ^ (-K0)) :=
    (Finset.mem_product.mp (Finset.mem_product.mp hcl).2).2
  exact q11_bin_lower_all (Real.rpow_pos_of_pos hΔ _) hbin

/-- The bin lower bound pays for the Proposition 4.5 gain and local error
with `cg = 4` and `cη = 4 cε`. -/
theorem q11_catalogue_budget {d : ℕ} {V Δ K0 v cseed U0 dsep : ℝ}
    (hΔ : 0 < Δ) (hv : 0 ≤ v) (hcseed : 0 ≤ cseed)
    (hU0 : 0 < U0) (hdsep : 0 < dsep)
    {cl : ℕ × (Fin d → ℤ) × ℤ}
    (hcl : cl ∈ q11ClassSet d V Δ K0) :
    let Q := (2 : ℝ) ^ cl.2.2
    let cε := min (1 / 4) (dsep / (8 * U0))
    q11GainDelta v cseed Δ K0 U0 * U0 ≤
      4 * v * cseed * Q ∧
    q11Error v cseed Δ K0 U0 dsep ≤
      (4 * cε) * v * cseed * Q ∧
    0 ≤ 4 * cε ∧ 4 * cε ≤ 1 := by
  let Q : ℝ := (2 : ℝ) ^ cl.2.2
  let cε : ℝ := min (1 / 4) (dsep / (8 * U0))
  have hQ : Δ ^ K0 ≤ 4 * Q := by
    have := q11_class_bin_lower hΔ hcl
    dsimp [Q]
    linarith
  have hvc : 0 ≤ v * cseed := mul_nonneg hv hcseed
  have hmul := mul_le_mul_of_nonneg_left hQ hvc
  have hcε : 0 ≤ cε := by dsimp [cε]; positivity
  have hcε1 : 4 * cε ≤ 1 := by
    dsimp [cε]
    linarith [min_le_left (1 / 4 : ℝ) (dsep / (8 * U0))]
  have hmulε := mul_le_mul_of_nonneg_left hmul hcε
  have hgain : q11GainDelta v cseed Δ K0 U0 * U0 =
      v * cseed * Δ ^ K0 := by
    dsimp [q11GainDelta]
    field_simp
  have herr : q11Error v cseed Δ K0 U0 dsep =
      cε * (v * cseed * Δ ^ K0) := rfl
  change q11GainDelta v cseed Δ K0 U0 * U0 ≤
      4 * v * cseed * Q ∧
    q11Error v cseed Δ K0 U0 dsep ≤
      (4 * cε) * v * cseed * Q ∧
    0 ≤ 4 * cε ∧ 4 * cε ≤ 1
  constructor
  · rw [hgain]
    nlinarith only [hmul]
  constructor
  · rw [herr]
    nlinarith only [hmulε]
  exact ⟨by positivity, hcε1⟩

end HigherDimLQGContinuity
