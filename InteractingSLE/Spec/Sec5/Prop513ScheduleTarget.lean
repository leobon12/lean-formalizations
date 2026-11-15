/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleInputs
import InteractingSLE.Spec.Sec5.Prop513FieldLaw

/-!
# The remaining source-coordinate input for the target-normalized tree

The schedule induction uses a chart sending the common target to infinity.
The original strip field is recorded in chart E. This file identifies the
concrete Q-field and states its still-needed canonical boundary-mean covariance
as a named input. It is not inferred from the R56 height inequalities.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw Sec4 QuantumZipper

/-- The half-plane change from chart E to chart Q: `z ↦ z/(z+1+q)` on `ℍ`.
Its inherited derivative argument is the one fixed by this composition. -/
def targetChart (q : ℝ) : Chart :=
  ((Chart.id.recenter (-(1 + q))).trans (stripCounterflowChart q)).trans
    (Chart.id.recenter (-2))

theorem targetChart_isConformal {q : ℝ} (hq : 0 < q) : (targetChart q).IsConformal :=
  ((Chart.isConformal_id.recenter _).trans (Prop513Field.isConformal hq)).trans
    (Chart.isConformal_id.recenter _)

/-- The actual field in chart Q, with coefficient `χ` and the inherited lift. -/
def targetField (κ q : ℝ) (hq : 0 < q) (f : DistOn upperHalfPlaneOpens) :
    DistOn upperHalfPlaneOpens :=
  Chart.chartTransport (targetChart_isConformal hq) 1 0 (chiC κ) f

theorem measurable_targetField (κ q : ℝ) (hq : 0 < q) : Measurable (targetField κ q hq) :=
  Chart.measurable_chartTransport (targetChart_isConformal hq) 1 0 (chiC κ)

/-- Exact remaining input: the canonical GFF law of the E-to-Q transported
field, including its bounded harmonic boundary mean. This has not been proved
by the finite-schedule induction. -/
def TargetCanonicalFieldStatement (κ x₀ : ℝ) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  IsStripGFF κ P h bL bU JL JU →
    IsGFFWithBoundaryData P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω))
      (stripQHData κ (Real.exp (π * x₀)) bL bU)
      (stripQHJumps (Real.exp (π * x₀)) JL JU)

/-- The source's chosen heights give the initial word and the GFF required by
the finite-schedule theorem, once the displayed Q-field covariance is supplied. -/
theorem exists_extremeWord_targetField {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ)
    (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hQ : TargetCanonicalFieldStatement κ x₀ (fig51Lower a b)
      (fig51Upper x₀ a' b') {0} {x₀} P h) :
    ∃ c : BoundaryWord, ExtremeHeights κ c ∧
      IsGFFWithBoundaryData P
        (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) c.fn c.jumps := by
  obtain ⟨c, hcJ, hc, hH⟩ := exists_extremeWord_fig51 hκ hb
  refine ⟨c, hH, ?_⟩
  rw [hcJ]
  apply (Restart.isGFFWithBoundaryData_congr P _
    (S := (stripQHJumps (Real.exp (π * x₀)) {0} {x₀} : Set ℝ))
    (fun y hy => hc y (by rwa [hcJ]))).2
  exact hQ hG

end InteractingSLE.Sec5.Prop513Schedule
