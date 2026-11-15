/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3RetainedNoLaunch
import InteractingSLE.Spec.Supplement.SBS3MarkedRecenter
import InteractingSLE.Spec.Supplement.SBS3MarkedPost

/-!
# S3: the actual word and field update at every instruction

A launch uses its stopped record. Without a launch, the chart's real
translation is applied to the old word and field. These formulas are
defined on all samples, including terminal states, and are measurable for
the exact retained pasts.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- Each ordinary instruction in the prefix has finite allotted time.
Switches and instructions beyond the program are unrestricted. -/
def HasFiniteOrdinaryTimes (spec : ExplSpec) (k : ℕ) : Prop :=
  ∀ j < k, ∀ (θ : ℝ) (t : ℝ≥0∞), spec.2.2[j]? = some (Sum.inl (θ, t)) → t ≠ ⊤

open Classical in
/-- The word after one instruction, including instructions without a launch. -/
def nextRetainedWord {Ω : Type u} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (β : Ω → BoundaryWord) (ω : Ω) : BoundaryWord :=
  if (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none then
    BoundaryWord.shiftW (WalkInf.recAmt κ b jumps spec E k ω) (β ω)
  else stopWord κ (β ω, instrAngle spec k, pastMap κ b jumps spec E (k + 1) ω (Fin.last k))

open Classical in
/-- The field after the same actual instruction and chart update. -/
def nextRetainedField {Ω : Type u} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (Y : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) : DistOn upperHalfPlaneOpens :=
  if (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none then
    flowField (WalkInf.recAmt κ b jumps spec E k ω) 0 (Y ω)
  else recField κ (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)) (Y ω)

/-- The actual real translation is measured by the new retained past. -/
theorem measurable_recAmt_pastSigma {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    Measurable[pastSigma κ b jumps spec E (k + 1)] (WalkInf.recAmt κ b jumps spec E k) := by
  refine measurable_pastSigma_of_runs runMeasStatement hb (fun j _ => hEm j) (fun j _ => hreg j) ?_
    (fun ω ω' he => ?_)
  · exact Complex.measurable_re.comp
      ((measurable_chart_apply runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hreg j)
          (Nat.le_succ k) 0).sub
        (measurable_chart_apply runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hreg j) le_rfl 0))
  · simp only [WalkInf.recAmt, he k (Nat.le_succ k), he (k + 1) le_rfl]

/-- The updated word is measurable for the exact new past. -/
theorem measurable_nextRetainedWord {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ} {β : Ω → BoundaryWord}
    (hβ : Measurable[pastSigma κ b jumps spec E k] β) :
    Measurable[pastSigma κ b jumps spec E (k + 1)] (nextRetainedWord κ b jumps spec E k β) := by
  classical
  have hβ' := hβ.mono (pastSigma_mono spec E (Nat.le_succ k)) le_rfl
  have hN := (pastSigma_mono spec E (Nat.le_succ k)) _
    (measurableSet_noLaunch_pastSigma (κ := κ) (spec := spec) hb hEm hreg k)
  exact Measurable.ite hN
    (BoundaryWord.measurable_shiftW.comp ((measurable_recAmt_pastSigma hb hEm hreg k).prodMk hβ'))
    ((measurable_stopWord κ).comp (hβ'.prodMk
      (measurable_const.prodMk (measurable_lastRetainedRecord spec E k))))

/-- The matching updated field is ambient-measurable. -/
theorem measurable_nextRetainedField {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    (h𝒢 : pastSigma κ b jumps spec E (k + 1) ≤ mΩ) {Y : Ω → DistOn upperHalfPlaneOpens}
    (hY : Measurable Y) : Measurable (nextRetainedField κ b jumps spec E k Y) := by
  classical
  have hN := h𝒢 _ ((pastSigma_mono spec E (Nat.le_succ k)) _
    (measurableSet_noLaunch_pastSigma (κ := κ) (spec := spec) hb hEm hreg k))
  have ha := (measurable_recAmt_pastSigma (κ := κ) (spec := spec) hb hEm hreg k).mono h𝒢 le_rfl
  have hRec := (measurable_lastRetainedRecord (κ := κ) (b := b) (jumps := jumps) spec E k).mono h𝒢 le_rfl
  exact Measurable.ite hN
    (Measurable.comp (g := fun p : ℝ × DistOn upperHalfPlaneOpens => flowField p.1 0 p.2)
      (f := fun ω => (WalkInf.recAmt κ b jumps spec E k ω, Y ω))
      measurable_flowField_uncurry (ha.prodMk hY))
    (Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => recField κ p.1 p.2)
      (f := fun ω => (pastMap κ b jumps spec E (k + 1) ω (Fin.last k), Y ω))
      (measurable_recField κ) (hRec.prodMk hY))

end InteractingSLE.Theorem14.SB.S3
