/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1BorelRelation

/-!
# The Borel relation with an explicit retargeting clock

Continuation of PROVE-GW1-DET. The source and output are regular codes.
The clock is also coded at rational times. All defining tests are countable;
the generating traces and first-visit times use existing measurable selectors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.Theorem14.GW1Borel

abbrev Base := (RegularCode × ℝ) × RegularCode
abbrev Witness := Base × Code

/-- Source first visit of the desired physical target, in trace coordinates. -/
def targetTime (p : Base) : ℝ≥0∞ := visitTime (p.1.1, -(p.1.2 : ℂ)⁻¹)

theorem measurable_targetTime : Measurable targetTime :=
  measurable_visitTime.comp ((measurable_fst.comp measurable_fst).prodMk
    ((Complex.measurable_ofReal.comp (measurable_snd.comp measurable_fst)).inv.neg))

theorem targetTime_eq (p : Base) (hv : p.1.2 ≠ 0) :
    targetTime p = firstTipTime infinitySourceChart (driver p.1.1.1) {(p.1.2 : ℂ)} := by
  rw [GW1Det.firstTipTime_singleton_eq_firstVisit (trace_properties p.1.1).1
    (continuous_driver _) (driver_zero _),
    GW4Reg.firstVisit_eq_aux130 _ (Complex.ofReal_ne_zero.2 hv)]
  rfl

/-- The original clock relation, with a countable test for its tip clause. -/
theorem prefixClock_iff (p : Base) (hv : p.1.2 ≠ 0) (f : Code) :
    GW1LaunchClock.IsPrefixClock (Chart.id.recenter p.1.2) (driver p.1.1.1) (driver p.2.1)
      {(p.1.2 : ℂ)} (clock f) ↔
    StrictMono (clock f) ∧ range (clock f) = {t : ℝ≥0 | (t : ℝ≥0∞) < targetTime p} ∧
      ∀ q : ℚ≥0, trace p.2 q * (1 + (p.1.2 : ℂ) * trace p.1.1 (clock f q)) =
        trace p.1.1 (clock f q) := by
  unfold GW1LaunchClock.IsPrefixClock
  rw [← targetTime_eq p hv]
  have htip : (∀ r z, ((Chart.id.recenter p.1.2).trans infinitySourceChart).tipAt (driver p.2.1) r z ↔
      infinitySourceChart.tipAt (driver p.1.1.1) (clock f r) z) ↔
      ∀ q : ℚ≥0, trace p.2 q * (1 + (p.1.2 : ℂ) * trace p.1.1 (clock f q)) =
        trace p.1.1 (clock f q) := by
    simp_rw [tipAt_iff_polynomial]
    exact polynomial_iff_rat _ _ _ (continuous_clock f)
  rw [htip]
  exact and_iff_right (continuous_clock f)

/-- A rational code is canonical when it is exactly the restriction of the
continuous clock it encodes. This clause is needed for injective projection. -/
def witnessGraph : Set Witness :=
  {p | (∀ q : ℚ≥0, p.1.2.1 q = driver p.1.2.1 q) ∧ p.1.1.2 ≠ 0 ∧
    targetTime p.1 < ⊤ ∧ (∀ q : ℚ≥0, p.2 q = (clock p.2 q : ℝ)) ∧
    StrictMono (clock p.2) ∧ range (clock p.2) = {t : ℝ≥0 | (t : ℝ≥0∞) < targetTime p.1} ∧
    ∀ q : ℚ≥0, trace p.1.2 q * (1 + (p.1.1.2 : ℂ) * trace p.1.1.1 (clock p.2 q)) =
      trace p.1.1.1 (clock p.2 q)}

theorem measurable_source : Measurable (fun p : Witness => p.1.1.1) :=
  measurable_fst.comp (measurable_fst.comp measurable_fst)

theorem measurable_output : Measurable (fun p : Witness => p.1.2) :=
  measurable_snd.comp measurable_fst

theorem measurable_target : Measurable (fun p : Witness => p.1.1.2) :=
  measurable_snd.comp (measurable_fst.comp measurable_fst)

theorem measurableSet_output_canonical :
    MeasurableSet {p : Witness | ∀ q : ℚ≥0, p.1.2.1 q = driver p.1.2.1 q} := by
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun q => measurableSet_eq_fun
    ((measurable_pi_apply q).comp (measurable_subtype_coe.comp measurable_output))
    ((measurable_driver q).comp (measurable_subtype_coe.comp measurable_output))

theorem measurableSet_clock_canonical :
    MeasurableSet {p : Witness | ∀ q : ℚ≥0, p.2 q = (clock p.2 q : ℝ)} := by
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun q => measurableSet_eq_fun
    ((measurable_pi_apply q).comp measurable_snd)
    (measurable_coe_nnreal_real.comp ((measurable_clock q).comp measurable_snd))

theorem measurableSet_polynomial : MeasurableSet {p : Witness | ∀ q : ℚ≥0,
    trace p.1.2 q * (1 + (p.1.1.2 : ℂ) * trace p.1.1.1 (clock p.2 q)) =
      trace p.1.1.1 (clock p.2 q)} := by
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  have harg : Measurable (fun p : Witness => (p.1.1.1, clock p.2 q)) :=
    measurable_source.prodMk ((measurable_clock q).comp measurable_snd)
  have hsource : Measurable (fun p : Witness => trace p.1.1.1 (clock p.2 q)) :=
    @Measurable.comp Witness (RegularCode × ℝ≥0) ℂ _ _ _
      (fun p : RegularCode × ℝ≥0 => trace p.1 p.2)
      (fun p : Witness => (p.1.1.1, clock p.2 q)) measurable_trace_eval harg
  exact measurableSet_eq_fun (((measurable_trace q).comp measurable_output).mul
    (measurable_const.add ((Complex.measurable_ofReal.comp measurable_target).mul hsource))) hsource

theorem measurableSet_witnessGraph : MeasurableSet witnessGraph := by
  have hT : Measurable (fun p : Witness => targetTime p.1) :=
    measurable_targetTime.comp measurable_fst
  have harg : Measurable (fun p : Witness => (p.2, targetTime p.1)) :=
    measurable_snd.prodMk hT
  have hrange : MeasurableSet {p : Witness | StrictMono (clock p.2) ∧
      range (clock p.2) = {t : ℝ≥0 | (t : ℝ≥0∞) < targetTime p.1}} :=
    measurableSet_clock_range.preimage (f := fun p : Witness => (p.2, targetTime p.1)) harg
  have hne : MeasurableSet {p : Witness | p.1.1.2 ≠ 0} :=
    (measurableSet_eq_fun measurable_target measurable_const).compl
  have hfin : MeasurableSet {p : Witness | targetTime p.1 < ⊤} :=
    measurableSet_lt hT measurable_const
  convert measurableSet_output_canonical.inter (hne.inter
    (hfin.inter
      (measurableSet_clock_canonical.inter (hrange.inter measurableSet_polynomial)))) using 1
  ext p
  simp only [witnessGraph, mem_ofPred_eq, mem_inter_iff, and_assoc]

theorem witness_prefix {p : Witness} (hp : p ∈ witnessGraph) :
    GW1LaunchClock.IsPrefixClock (Chart.id.recenter p.1.1.2) (driver p.1.1.1.1) (driver p.1.2.1)
      {(p.1.1.2 : ℂ)} (clock p.2) :=
  (prefixClock_iff p.1 hp.2.1 p.2).2 hp.2.2.2.2

end InteractingSLE.Theorem14.GW1Borel
