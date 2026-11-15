/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootL6Unit

/-!
# A common measurable driver record for GW2's finite-force models

Continuation of PROVE-T14-GW2ROOT2. The record forgets the force marks but
keeps the killing time and rational absolute-driver observations. Its slow
event is measurable and is preserved by an earlier buffer stop. This gives
one common carrier even when the finite force-word lengths vary.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootV7

open Sec5 RootN4

/-- The killing time and rational observations of the normalized absolute driver. -/
abbrev DriverRecord := ℝ≥0∞ × (ℚ≥0 → ℝ)

/-- Forget force marks and add the starting absolute driver position. -/
def driverRecord (a : ℝ) {nL nR : ℕ} (z : Prop59Stage.Samp nL nR) :
    DriverRecord := (z.1, fun q => a + (z.2 q).1)

/-- Kill a record at the minimum of its lifetime and the supplied buffer time. -/
def cutRecord (L : ℝ≥0∞) (z : DriverRecord) : DriverRecord :=
  (min L z.1, fun q => if ((q : ℝ≥0) : ℝ≥0∞) < min L z.1 then z.2 q else 0)

/-- The countable slow event on the common carrier. -/
def slowSet : Set DriverRecord :=
  {z | ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ) < 1 →
    ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q ≤ 7 / 4}

/-- The driver projection is measurable, uniformly in both force-word lengths. -/
theorem measurable_driverRecord (a : ℝ) {nL nR : ℕ} :
    Measurable (driverRecord a : Prop59Stage.Samp nL nR → DriverRecord) := by
  exact measurable_fst.prodMk (measurable_pi_iff.2 fun q =>
    measurable_const.add (measurable_fst.comp ((measurable_pi_apply q).comp
      measurable_snd)))

/-- Buffer killing is measurable in both the buffer and the original record. -/
theorem measurable_cutRecord {Ω : Type*} [MeasurableSpace Ω]
    {L : Ω → ℝ≥0∞} {z : Ω → DriverRecord} (hL : Measurable L)
    (hz : Measurable z) : Measurable fun ω => cutRecord (L ω) (z ω) := by
  exact (hL.min hz.fst).prodMk (measurable_pi_iff.2 fun q =>
    Measurable.ite (measurableSet_lt measurable_const (hL.min hz.fst))
      ((measurable_pi_apply q).comp hz.snd) measurable_const)

/-- The common slow event only uses countably many measurable observations. -/
theorem measurableSet_slowSet : MeasurableSet slowSet := by
  have heq : slowSet = ⋂ q : ℚ≥0, {z : DriverRecord |
      ((q : ℝ≥0) : ℝ) < 1 → ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q ≤ 7 / 4} := by
    ext z
    simp only [slowSet, mem_ofPred_eq, mem_iInter]
  rw [heq]
  refine MeasurableSet.iInter fun q => ?_
  by_cases hq : ((q : ℝ≥0) : ℝ) < 1
  · simp only [hq, true_imp_iff]
    simp only [imp_iff_not_or]
    exact (measurableSet_lt measurable_const
      (measurable_fst : Measurable (Prod.fst : DriverRecord → ℝ≥0∞))).compl.union
      (measurableSet_le ((measurable_pi_apply q).comp
        (measurable_snd : Measurable (Prod.snd : DriverRecord → (ℚ≥0 → ℝ)) ))
        measurable_const)
  · simp only [hq, false_imp_iff, ofPred_true, MeasurableSet.univ]

/-- Earlier killing preserves every live rational observation bound. -/
theorem cutRecord_mem_slowSet {z : DriverRecord} (hz : z ∈ slowSet)
    (L : ℝ≥0∞) : cutRecord L z ∈ slowSet := by
  intro q hq1 hqL
  change ((q : ℝ≥0) : ℝ≥0∞) < min L z.1 at hqL
  have hqζ := hqL.trans_le (min_le_right _ _)
  change (if ((q : ℝ≥0) : ℝ≥0∞) < min L z.1 then z.2 q else 0) ≤ 7 / 4
  rw [ite_eq_left hqL]
  exact hz q hq1 hqζ

/-- The finite-force unit event implies the slow event after forgetting marks. -/
theorem driverRecord_mem_slowSet_of_unit {nL nR : ℕ} {a : ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {z : Prop59Stage.Samp nL nR}
    (hz : ((a, xL, xR), z) ∈ Prop59Stage.unitSet) :
    driverRecord a z ∈ slowSet := fun q hq1 hqζ => (hz q hq1 hqζ).le

/-- The common driver record of an evolution, killed at the buffer time. -/
def modelSample {nL nR : ℕ} (e : EvolutionData.{u} nL nR) (a : ℝ)
    (L : e.Ω → ℝ≥0∞) (ω : e.Ω) : DriverRecord :=
  cutRecord (L ω) (driverRecord a (Prop59Stage.samp (e.W · ω)
    (fun i t => e.VL i t ω) (fun i t => e.VR i t ω) (e.lifetime ω)))

/-- A genuine integrated evolution and a measurable buffer yield a measurable sample. -/
theorem measurable_modelSample {κ : ℝ} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (e : EvolutionData.{u} nL nR) (hE : e.IsEvolution κ xL ρL xR ρR)
    (a : ℝ) {L : e.Ω → ℝ≥0∞} (hL : @Measurable _ _ e.mΩ _ L) :
    @Measurable _ _ e.mΩ _ (modelSample e a L) := by
  let : MeasurableSpace e.Ω := e.mΩ
  exact measurable_cutRecord hL ((measurable_driverRecord a).comp
    (Prop59Stage.measurable_samp_of_evolution hE))

/-- Before its killing time, the model record reads exactly the raw absolute driver. -/
theorem modelSample_read {nL nR : ℕ} (e : EvolutionData.{u} nL nR)
    (a : ℝ) (L : e.Ω → ℝ≥0∞) (ω : e.Ω) {q : ℚ≥0}
    (hq : ((q : ℝ≥0) : ℝ≥0∞) < (modelSample e a L ω).1) :
    (modelSample e a L ω).2 q = a + e.W q ω := by
  change ((q : ℝ≥0) : ℝ≥0∞) < min (L ω) (e.lifetime ω) at hq
  have hqζ := hq.trans_le (min_le_right _ _)
  change (if ((q : ℝ≥0) : ℝ≥0∞) < min (L ω) (e.lifetime ω) then
    a + ((Prop59Stage.samp (e.W · ω) (fun i t => e.VL i t ω)
      (fun i t => e.VR i t ω) (e.lifetime ω)).2 q).1 else 0) = _
  rw [ite_eq_left hq, Prop59Stage.samp_snd_of_lt _ _ _ hqζ]

end InteractingSLE.Theorem14.GW2TipSystem.RootV7
