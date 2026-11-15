/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Sample

/-! # The fixed initial joint-chart trace and its oriented observations -/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist.StagedLaw Restart

/-- The root-normalized driver starts after the INITIAL retained piece. -/
def jointDriverRead (a : ℝ≥0) (x : ℝ) (s v v₀ : ℝ≥0)
    (p : RecData × RecData) : ℝ≥0 → ℝ :=
  fun u => stageDriverRead a 1 x s v v₀ v₀ u p

/-- LP's total trace reader of that fixed joint-chart driver. -/
def jointTraceRead (a : ℝ≥0) (x : ℝ) (s v v₀ : ℝ≥0)
    (p : RecData × RecData) : ℝ≥0 → ℂ :=
  (LP.drivingTrace
    (capacityIncrement a x s v₀ (v - v₀) p, jointDriverRead a x s v v₀ p)).2

/-- Dyadic endpoint evaluation is Borel even for an exceptional trace reader. -/
def jointTipRead (a : ℝ≥0) (x : ℝ) (s v v₀ u : ℝ≥0)
    (p : RecData × RecData) : ℂ :=
  endVal ((u : ℝ≥0∞), jointTraceRead a x s v v₀ p)

/-- Reflection in the imaginary axis changes the driver sign and preserves H. -/
def orientTip (n : ℕ) (z : ℂ) : ℂ := if Even n then z else -star z

theorem measurable_jointDriverRead (a : ℝ≥0) (x : ℝ) (s v v₀ : ℝ≥0) :
    Measurable (jointDriverRead a x s v v₀) :=
  measurable_pi_iff.mpr fun _ =>
    measurable_stageDriverRead_random measurable_id measurable_const a 1 x s v v₀ v₀

theorem jointDriverRead_zero (a : ℝ≥0) (x : ℝ) (s v v₀ : ℝ≥0)
    (p : RecData × RecData) : jointDriverRead a x s v v₀ p 0 = 0 := by
  simp only [jointDriverRead, stageDriverRead, zero_div, add_zero, sub_self, mul_zero]

theorem measurable_jointTraceRead (a : ℝ≥0) (x : ℝ) (s v v₀ : ℝ≥0) :
    Measurable (jointTraceRead a x s v v₀) :=
  (measurable_snd.comp LP.measurable_drivingTrace).comp
    ((measurable_coe_nnreal_ennreal.comp
      (measurable_capacityIncrement_random measurable_id measurable_const a x s v₀)).prodMk
        (measurable_jointDriverRead a x s v v₀))

theorem measurable_jointTipRead_random {Ω : Type*} [MeasurableSpace Ω]
    {p : Ω → RecData × RecData} (hp : Measurable p)
    {u : Ω → ℝ≥0} (hu : Measurable u)
    (a : ℝ≥0) (x : ℝ) (s v v₀ : ℝ≥0) :
    Measurable fun ω => jointTipRead a x s v v₀ (u ω) (p ω) :=
  measurable_endVal.comp ((measurable_coe_nnreal_ennreal.comp hu).prodMk
    ((measurable_jointTraceRead a x s v v₀).comp hp))

theorem measurable_orientTip (n : ℕ) : Measurable (orientTip n) := by
  classical
  change Measurable (fun z : ℂ => if Even n then z else -star z)
  by_cases hn : Even n
  · simp only [hn, ↓reduceIte]
    exact measurable_id
  · simp only [hn, ↓reduceIte]
    exact Complex.continuous_conj.measurable.neg

theorem orientTip_mem_H_iff (n : ℕ) (z : ℂ) : orientTip n z ∈ QuantumZipper.H ↔
    z ∈ QuantumZipper.H := by
  classical
  by_cases hn : Even n
  · simp only [orientTip, hn, ↓reduceIte]
  · simp only [orientTip, hn, ↓reduceIte, QuantumZipper.H, mem_ofPred_eq,
      Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg]

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
