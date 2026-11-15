/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksNull
import InteractingSLE.Spec.Sec5.Aux61GInstAccessLocal
import InteractingSLE.Spec.Sec5.Aux61GHistAccess
import InteractingSLE.Spec.Sec5.Aux61GContEndpoint

/-! # The initial raw code is recorded in null-completed physical marks

At time zero every code driver is zero. Thus only the initial aliveness
event must be recorded. For an access code the physical stop condition
identifies that event almost surely with the restart event. No causal
reconstruction of the positive-time decoded driver is needed here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWord
open Aux61Marks (nullMarks)
open Aux61Fib (FibCode)
open Aux61FibK (codeFiltration)
open Aux61FibData (IsRestartSpec inPath exitEv)
open Aux61GInst (HasAccessLanding accessExitCode)

universe u
variable {X : Type u} {ℋ : MeasurableSpace X} [mX : MeasurableSpace X] {μ : Measure X}

/-- The raw zero-time code sigma-algebra is in the completed physical marks
when initial aliveness agrees almost surely with a physical mark. -/
theorem codeFiltration_zero_le_nullMarks {Y : X → FibCode}
    (hlm : Measurable fun x => (Y x).life) {S : Set X} (hS : MeasurableSet[ℋ] S)
    (hlive : ∀ᵐ x ∂μ, (0 : ℝ≥0∞) < (Y x).life ↔ x ∈ S) :
    (codeFiltration.{u} 0).comap (fun x => ULift.up.{u} (Y x)) ≤ nullMarks ℋ μ := by
  classical
  refine Aux61Marks.codeFiltration_comap_le_nullMarks fun r hr A _ => ?_
  have hr0 : r = 0 := le_antisymm hr zero_le
  subst r
  simp only [ENNReal.coe_zero, FibCode.driver_zero]
  by_cases hA : ((0 : ℝ), (fun _ : Fin 0 => (0 : ℝ)),
      (fun _ : Fin 0 => (0 : ℝ))) ∈ A
  · simp only [hA, and_true]
    refine Aux61Marks.measurableSet_nullMarks_of_ae_eq
      (measurableSet_lt measurable_const hlm) hS ?_
    filter_upwards [hlive] with x hx
    exact propext hx
  · simp only [hA, and_false, ofPred_false]
    exact @MeasurableSet.empty X (nullMarks ℋ μ)

/-- The source physical stop condition records the zero-time access code
in completed marks whenever the restart event itself is a physical mark. -/
theorem accessExitCode_zero_le_nullMarks
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
    (hs : IsRestartSpec E c ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
    (hland : HasAccessLanding E c ρ T V)
    (hinj : ∀ x ∈ E, InjOn (ρ x) {r | (r : ℝ≥0∞) < T x})
    (hlift : ∀ x ∈ E, ContinuousOn (c x).2.2 (c x).dom)
    {a k : ℝ} {h : X → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hE : MeasurableSet[ℋ] E)
    (hstop : ∀ᵐ x ∂μ, x ∈ E → 0 < T x ∧
      (T x < ⊤ ∨ ∃ r : ℝ≥0, (r : ℝ≥0∞) < T x ∧ inPath E c ρ T x r ∉ V)) :
    (codeFiltration.{u} 0).comap
      (fun x => ULift.up.{u} (accessExitCode E c ρ T V a k h x)) ≤ nullMarks ℋ μ := by
  have hY := Aux61GInst.measurable_accessExitCode (a := a) (k := k)
    hs hV hV0 hland hinj hlift hh
  apply codeFiltration_zero_le_nullMarks (FibCode.measurable_life.comp hY) hE
  filter_upwards [hstop] with x hx
  constructor
  · intro hlive
    have he : x ∈ exitEv E c ρ T V :=
      Aux61GInst.mem_exitEv_of_lt_accessLife (q := 0) (by simpa only [ENNReal.coe_zero] using hlive)
    exact he.1.1
  · intro hxE
    exact Aux61GHist.accessExitCode_life_pos hs hV hV0 hland hinj
      (Aux61GCont.mem_exitEv_of_contact_or_exit hxE (hx hxE).1 (hx hxE).2)

end InteractingSLE.Sec5.Aux61GWord
