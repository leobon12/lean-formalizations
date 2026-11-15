/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1BorelClock
import InteractingSLE.Foundations.Loewner.TraceCodingTop
import InteractingSLE.Spec.Sec7.StripSysSel

/-!
# Measurable regular-driver codes and their traces

Continuation of PROVE-GW1-DET. The existing transient-trace coding theorem
makes the regular-driver domain Borel. On that domain, the existing selector
`LP.traceAt` is the actual continuous generating trace, jointly measurable
in the code and time by the Caratheodory measurability theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.Theorem14.GW1Borel

abbrev Code := ℚ≥0 → ℝ

/-- The existing continuous normalized regularization of a rational driver code. -/
def driver (f : Code) (t : ℝ≥0) : ℝ := Sec7.Coding.regQ t f

theorem continuous_driver (f : Code) : Continuous (driver f) := Sec7.Coding.continuous_regQ f

theorem driver_zero (f : Code) : driver f 0 = 0 :=
  QuantumZipper.Thm18Asm.G1Pkg.regB_zero _

theorem measurable_driver (t : ℝ≥0) : Measurable (fun f : Code => driver f t) :=
  Sec7.Coding.measurable_regQ t

/-- Codes whose regularization is a regular transient counterflow driver. -/
def regularCodes : Set Code := {f | GW1Path.IsRegCf (driver f)}

theorem measurableSet_regularCodes : MeasurableSet regularCodes := by
  obtain ⟨G, hG, hchar⟩ := Sec7.transientTraceCodingStatement
  have hm : Measurable (fun f : Code => fun q : ℚ≥0 => driver f q) :=
    measurable_pi_iff.2 fun q => measurable_driver q
  convert hG.preimage hm using 1
  ext f
  exact ⟨fun h => (hchar _ (continuous_driver f) (driver_zero f)).2 h.2.2,
    fun h => ⟨continuous_driver f, driver_zero f,
      (hchar _ (continuous_driver f) (driver_zero f)).1 h⟩⟩

abbrev RegularCode := regularCodes

instance : StandardBorelSpace RegularCode := measurableSet_regularCodes.standardBorel

/-- The actual generating trace of a regular code, using the already measurable selector. -/
def trace (f : RegularCode) (t : ℝ≥0) : ℂ := LP.traceAt t (driver f.1)

theorem trace_eq {f : RegularCode} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace (driver f.1) ⊤ γ) : trace f = γ := by
  funext t
  exact LP.traceAt_eq_of_isGeneratingTrace hγ (continuous_driver _).continuousOn
    (driver_zero _) ENNReal.coe_lt_top

theorem trace_properties (f : RegularCode) :
    IsGeneratingTrace (driver f.1) ⊤ (trace f) ∧
      Tendsto (fun t => ‖trace f t‖) atTop atTop := by
  obtain ⟨γ, hγ, hinf⟩ := f.2.2.2
  rw [trace_eq hγ]
  exact ⟨hγ, hinf⟩

theorem continuous_trace (f : RegularCode) : Continuous (trace f) :=
  Sec5.continuous_of_isGeneratingTrace_top (trace_properties f).1

theorem measurable_trace (t : ℝ≥0) : Measurable (fun f : RegularCode => trace f t) :=
  (LP.measurable_traceAt t).comp (measurable_pi_iff.2 fun s =>
    (measurable_driver s).comp measurable_subtype_coe)

theorem measurable_trace_eval : Measurable (fun p : RegularCode × ℝ≥0 => trace p.1 p.2) := by
  exact (measurable_uncurry_of_continuous_of_measurable continuous_trace measurable_trace).comp
    measurable_swap

/-- First visit of a target in the original (uninverted) trace coordinate. -/
def visitTime (p : RegularCode × ℂ) : ℝ≥0∞ := Sec7.Aux130.firstVisit (trace p.1) p.2

theorem measurable_visitTime : Measurable visitTime := by
  apply measurable_of_Iic
  intro t
  change MeasurableSet {p : RegularCode × ℂ | Sec7.Aux130.firstVisit (trace p.1) p.2 ≤ t}
  by_cases ht : t = ⊤
  · simp only [ht, le_top, ofPred_true, MeasurableSet.univ]
  · have h := Sec7.StripSys.measurableSet_inter_firstVisit_le
      (Ω := RegularCode × ℂ) MeasurableSet.univ
      (γ := fun p => trace p.1) (fun p _ => continuous_trace p.1)
      (fun q => (measurable_trace _).comp measurable_fst) measurable_snd t.toNNReal
    simpa only [univ_inter, ENNReal.coe_toNNReal ht] using h

end InteractingSLE.Theorem14.GW1Borel
