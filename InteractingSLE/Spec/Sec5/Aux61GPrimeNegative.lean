/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CovWire
import InteractingSLE.Spec.Sec5.Aux61FibDataData
import InteractingSLE.Spec.Sec5.Aux61FibSeed
import InteractingSLE.Spec.Sec4.Strip

/-! # The explicit negative reference word and its admissible seed

The high interval lies strictly left of the fresh seed. The finite word
has the canonical heights near zero and outside the comparison interval.
The strong negative barrier follows from the proved height calculation.
Stopped stochastic avoidance remains the separate `R5NegStatement` input.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric MeasureTheory
open QuantumZipper (H chiC)

namespace InteractingSLE.Sec5.Aux61GPrime

/-- The negative reference: height `v` between `x₂` and `x₁`, canonical
heights elsewhere. Values at the three listed jump points are immaterial. -/
def negativeBoundary (κ x₂ x₁ v z : ℝ) : ℝ :=
  (if z < 0 then -sleLambda κ else sleLambda κ) +
    (v + sleLambda κ) * ((if z < x₁ then 1 else 0) - (if z < x₂ then 1 else 0))

/-- The three elementary steps are locally constant away from their jumps. -/
theorem negativeBoundary_pc (κ x₂ x₁ v : ℝ) :
    IsPiecewiseConstantBoundaryData (negativeBoundary κ x₂ x₁ v) {x₂, x₁, 0} := by
  intro y hy
  have hy₂ : y ∉ ({x₂} : Finset ℝ) := by simpa using fun h => hy (by simp_all)
  have hy₁ : y ∉ ({x₁} : Finset ℝ) := by simpa using fun h => hy (by simp_all)
  have hy₀ : y ∉ ({0} : Finset ℝ) := by simpa using fun h => hy (by simp_all)
  filter_upwards [Sec4.isPiecewiseConstantBoundaryData_ite_lt 0 (-sleLambda κ) (sleLambda κ) y hy₀,
    Sec4.isPiecewiseConstantBoundaryData_ite_lt x₁ (1 : ℝ) 0 y hy₁,
    Sec4.isPiecewiseConstantBoundaryData_ite_lt x₂ (1 : ℝ) 0 y hy₂] with z h₀ h₁ h₂
  unfold negativeBoundary
  rw [h₀, h₁, h₂]

theorem negativeBoundary_pos {κ x₂ x₁ v z : ℝ} (h₂₁ : x₂ < x₁) (h₁ : x₁ < 0) (hz : 0 < z) :
    negativeBoundary κ x₂ x₁ v z = sleLambda κ := by
  simp [negativeBoundary, not_lt.2 hz.le, not_lt.2 (h₁.trans hz).le,
    not_lt.2 (h₂₁.trans (h₁.trans hz)).le]

theorem negativeBoundary_seedLeft {κ x₂ x₁ v z : ℝ} (h₂₁ : x₂ < x₁)
    (hz₁ : x₁ < z) (hz₀ : z < 0) : negativeBoundary κ x₂ x₁ v z = -sleLambda κ := by
  simp [negativeBoundary, hz₀, not_lt.2 hz₁.le, not_lt.2 (h₂₁.trans hz₁).le]

theorem negativeBoundary_high {κ x₂ x₁ v z : ℝ} (h₁ : x₁ < 0)
    (hz₂ : x₂ < z) (hz₁ : z < x₁) : negativeBoundary κ x₂ x₁ v z = v := by
  simp only [negativeBoundary, ite_eq_left (hz₁.trans h₁), ite_eq_left hz₁,
    ite_eq_right (not_lt.2 hz₂.le), sub_zero, mul_one]
  ring

theorem negativeBoundary_farLeft {κ x₂ x₁ v z : ℝ} (h₂₁ : x₂ < x₁) (h₁ : x₁ < 0)
    (hz : z < x₂) : negativeBoundary κ x₂ x₁ v z = -sleLambda κ := by
  simp [negativeBoundary, hz, hz.trans h₂₁, hz.trans (h₂₁.trans h₁)]

/-- The exact negative-side reference predicate, including its force-weight
barrier, follows from the strictly high physical interval height. -/
theorem negativeBoundary_refNeg {κ x₂ x₁ v : ℝ} (hκ : 0 < κ) (hκ₄ : κ < 4)
    (h₂₁ : x₂ < x₁) (h₁ : x₁ < 0) (hv : sleLambda κ + Real.pi * chiC κ < v)
    {I : Set ℝ} (hI : I ⊆ Ioo x₂ x₁) :
    Aux61Cov.RefNeg κ (negativeBoundary κ x₂ x₁ v) {x₂, x₁, 0} I := by
  refine ⟨hκ₄, negativeBoundary_pc κ x₂ x₁ v, x₂, x₁, v, h₂₁, h₁,
    (fun z hz => negativeBoundary_pos h₂₁ h₁ hz),
    (fun z hz₁ hz₀ => negativeBoundary_seedLeft h₂₁ hz₁ hz₀),
    (fun z hz₂ hz₁ => negativeBoundary_high h₁ hz₂ hz₁),
    (fun z hz => negativeBoundary_farLeft h₂₁ h₁ hz), ?_, hI⟩
  exact (Aux61Cov.cumWeightLeft_le_of_high hκ hv).le

/-- The canonical heights on the seed's two sides give an admissible
initial force state, independently of the high interval's height. -/
theorem negativeBoundary_seed {κ x₂ x₁ v : ℝ} (hκ : 0 < κ) (h₂₁ : x₂ < x₁) (h₁ : x₁ < 0) :
    ¬ ForceWord.ThresholdCondition
      (flowLineRhoL κ (negativeBoundary κ x₂ x₁ v) {x₂, x₁, 0} 0 0)
      (flowLineRhoR κ (negativeBoundary κ x₂ x₁ v) {x₂, x₁, 0} 0 0) 0
      (flowLineXL (negativeBoundary κ x₂ x₁ v) {x₂, x₁, 0} 0)
      (flowLineXR (negativeBoundary κ x₂ x₁ v) {x₂, x₁, 0} 0) := by
  have hL : PiecewiseConstantBoundaryData.leftLim (negativeBoundary κ x₂ x₁ v) 0 = -sleLambda κ :=
    Sec4.leftLim_eq_of_forall h₁ fun z hz => negativeBoundary_seedLeft h₂₁ hz.1 hz.2
  have hR : PiecewiseConstantBoundaryData.rightLim (negativeBoundary κ x₂ x₁ v) 0 = sleLambda κ :=
    Sec4.rightLim_eq_of_forall one_pos fun z hz => negativeBoundary_pos h₂₁ h₁ hz.1
  apply Aux61Fib.not_threshold_seed hκ
  · rw [hL]; linarith [Sec4.sleLambda_pos hκ]
  · rw [hR]; linarith [Sec4.sleLambda_pos hκ]

end InteractingSLE.Sec5.Aux61GPrime
