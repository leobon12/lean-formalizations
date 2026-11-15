/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TreeExtractSchedules
import InteractingSLE.Spec.Restart.StagedPathVersion

/-!
# Finite-schedule drivers and their measurable trace coordinates

Concatenation is along the deterministic own-capacity durations of the schedule.
Measurability of the drivers follows directly from `IsStagedHistory`. Their
regularity and determination by the field are displayed as separate inputs;
they do not follow merely from measurability of the stage records.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513TreeExtract

open Sec7.StripSideHeightProb

/-- Concatenate the stage drivers using the schedule's successive time gaps. -/
def joinedDriver {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ℕ → ℝ≥0 → List (ℝ × ℝ≥0) → Ω → ℝ≥0 → ℝ
  | _, _, [], _, _ => 0
  | j, a, (_, t) :: l, ω, r =>
      catPath (E j ω).1 (t - a) (joinedDriver E (j + 1) t l ω) r

theorem measurable_joinedDriver {Ω : Type*} [MeasurableSpace Ω]
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : ∀ j, Measurable (E j))
    (j : ℕ) (a : ℝ≥0) (l : List (ℝ × ℝ≥0)) :
    Measurable (joinedDriver E j a l) := by
  induction l generalizing j a with
  | nil => exact measurable_const
  | cons p l ih =>
      exact (Sec7.StripDet.measurable_catPath (p.2 - a)).comp
        ((measurable_fst.comp (hE j)).prodMk (ih (j + 1) p.2))

def prefixDriver {Ω : Type*}
    (E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (s : Schedule) : Ω → ℝ≥0 → ℝ :=
  joinedDriver (E s) 0 0 (scheduleList s)

/-- Strict availability of every scheduled ordinary piece through its requested
own-capacity duration. This omits a piece stopped exactly at its lifetime. -/
def scheduleAvailable {Ω : Type*}
    (E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (s : Schedule) (ω : Ω) : Prop :=
  ∀ j < (scheduleSpec s).2.2.length, Exist.StagedLaw.instrTime (scheduleSpec s) j < (E s j ω).2

theorem measurableSet_scheduleAvailable {Ω : Type*} [MeasurableSpace Ω]
    {E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (s : Schedule) (hE : ∀ j, Measurable (E s j)) :
    MeasurableSet {ω | scheduleAvailable E s ω} := by
  have hm : ∀ j, MeasurableSet {ω | j < (scheduleSpec s).2.2.length →
      Exist.StagedLaw.instrTime (scheduleSpec s) j < (E s j ω).2} := by
    intro j
    by_cases hj : j < (scheduleSpec s).2.2.length
    · simpa only [hj, true_implies, Function.comp_apply] using
        measurableSet_lt measurable_const (measurable_snd.comp (hE j))
    · simp only [hj, false_implies, ofPred_true]
      exact MeasurableSet.univ
  simpa only [scheduleAvailable, ofPred_forall] using MeasurableSet.iInter hm

/-- The staged carrier supplies ambient measurability of every finite driver. -/
theorem measurable_prefixDriver_of_staged {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ s, IsStagedHistory κ b J P h (scheduleSpec s) (E s)) (s : Schedule) :
    Measurable (prefixDriver E s) :=
  measurable_joinedDriver (hE s).1 _ _ _

/-- The precise remaining finite-prefix regularity input. It includes the
almost-sure trace through the terminal time; the bare staged-history carrier
does not include this assertion (R51). -/
def PrefixTraceRegularity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Schedule → Set Ω) (E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ s, ∀ᵐ ω ∂P, ω ∈ A s →
    ContinuousOn (prefixDriver E s ω) {t | (t : ℝ≥0∞) < terminal s} ∧
    prefixDriver E s ω 0 = 0 ∧
    ∃ η, IsGeneratingTrace (prefixDriver E s ω) (terminal s) η

/-- The R48-safe determination obligation for finite extreme-angle schedules.
This is a named input, not a consequence of stage-record measurability. -/
def PrefixFieldDrivers {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Schedule → Set Ω) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∃ D : Schedule → LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0 → ℝ,
    (∀ s, Measurable (D s)) ∧
    ∀ s, ∀ᵐ ω ∂P, ω ∈ A s → ∀ t : ℝ≥0, (t : ℝ≥0∞) < terminal s →
      D s (h ω) t = prefixDriver E s ω t

/-- The separate field-determination obligation for the availability flags. -/
def PrefixAvailabilityFieldStatement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∃ a : Schedule → LQGMetric.DistOn upperHalfPlaneOpens → Bool,
    (∀ s, Measurable (a s)) ∧
    ∀ᵐ ω ∂P, ∀ s, a s (h ω) = true ↔ scheduleAvailable E s ω

/-- The local prefix-consistency obligation for different staged programs.
The bare carrier is specified separately for each program and does not itself
assert this agreement across programs. -/
def PrefixEndpointCompatibility {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂P, ∀ n m,
    scheduleAvailable E (scheduleAt n) ω →
    scheduleAvailable E (scheduleAt (descendantIndex n m)) ω →
    ∀ η η' : ℝ≥0 → ℂ,
      IsGeneratingTrace (prefixDriver E (scheduleAt n) ω) (terminal (scheduleAt n)) η →
      IsGeneratingTrace (prefixDriver E (scheduleAt (descendantIndex n m)) ω)
        (terminal (scheduleAt (descendantIndex n m))) η' →
      η' (terminal (scheduleAt n)) = η (terminal (scheduleAt n))

/-- Trace coordinates read from a field-measurable representative driver. -/
def prefixTrace {Ω : Type*}
    (D : Schedule → Ω → ℝ≥0 → ℝ) (s : Schedule) (ω : Ω) (t : ℝ) : ℂ :=
  (LP.drivingTrace ((terminal s : ℝ≥0∞), D s ω)).2 t.toNNReal

theorem measurable_prefixTrace {Ω : Type*} {𝒢 : MeasurableSpace Ω}
    {D : Schedule → Ω → ℝ≥0 → ℝ} (hD : ∀ s, Measurable[𝒢] (D s))
    (s : Schedule) (t : ℝ) : Measurable[𝒢] fun ω => prefixTrace D s ω t :=
  (measurable_pi_apply t.toNNReal).comp (measurable_snd.comp
    (LP.measurable_drivingTrace.comp (measurable_const.prodMk (hD s))))

/-- The reconstructed coordinates agree with every actual generating prefix,
including its finite terminal point. -/
theorem prefixTrace_eq {Ω : Type*}
    {E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {D : Schedule → Ω → ℝ≥0 → ℝ} {s : Schedule} {ω : Ω}
    (hc : ContinuousOn (prefixDriver E s ω) {t | (t : ℝ≥0∞) < terminal s})
    (h0 : prefixDriver E s ω 0 = 0)
    (hD : ∀ t : ℝ≥0, (t : ℝ≥0∞) < terminal s → D s ω t = prefixDriver E s ω t)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace (prefixDriver E s ω) (terminal s) η)
    {t : ℝ} (ht : t ∈ Icc 0 (terminal s : ℝ)) : prefixTrace D s ω t = η t.toNNReal := by
  have he := LP.drivingTrace_eq hη hc h0 hD
  have ht' : t.toNNReal ≤ terminal s := by
    simpa only [Real.toNNReal_coe] using Real.toNNReal_mono ht.2
  change (LP.drivingTrace ((terminal s : ℝ≥0∞), D s ω)).2 t.toNNReal = _
  rw [he]
  dsimp only
  rw [min_eq_left (ENNReal.coe_le_coe.2 ht'), ENNReal.toNNReal_coe]

end InteractingSLE.Sec5.Prop513TreeExtract
