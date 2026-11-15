/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6ReadDBoundary
import InteractingSLE.Spec.Supplement.GB6SourceCFlow

/-!
# A total Borel inverse-chart readout

The inverse map at each interior point is measurable in the recorded driver.
A fixed vertical limit gives a Borel function on every record and every complex
input. At nonexceptional upper-half-plane points it is the continuous inverse
extension, including at real boundary visits.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Supp8.GB6.ReadD

open Exist.StagedLaw

/-- Fold the lower half-plane upwards, so every vertical approximation is
interior even when the readout is evaluated on an arbitrary path. -/
def upperPoint (z : ℂ) : ℂ := (z.re : ℂ) + (|z.im| : ℝ) * I

theorem upperPoint_mem (z : ℂ) : upperPoint z ∈ Hbar := by
  change 0 ≤ (upperPoint z).im
  simp [upperPoint, abs_nonneg]

theorem upperPoint_eq {z : ℂ} (hz : z ∈ Hbar) : upperPoint z = z := by
  have hz' : 0 ≤ z.im := hz
  apply Complex.ext <;> simp [upperPoint, abs_of_nonneg hz']

theorem measurable_upperPoint : Measurable upperPoint :=
  (Complex.measurable_ofReal.comp Complex.measurable_re).add
    ((Complex.measurable_ofReal.comp Complex.measurable_im.abs).mul_const I)

/-- Fixed interior evaluation of the inverse relative chart from a record. -/
theorem measurable_relInv_record (s : ℝ≥0) {z : ℂ} (hz : z ∈ H) :
    Measurable fun r : RecData => relInv (rdrv r) s z := by
  let B : ℝ≥0 → RecData → ℝ := fun t r => rdrv r t
  have hm := QuantumZipper.RS.measurable_fwdMapInv_drive
    (B := B) (fun t => measurable_rdrv_apply t)
    (fun r => (continuous_rdrv r).comp NNReal.continuous_coe)
    (fun r => rdrv_zero r) 1 s.coe_nonneg (neg_inv_mem_H hz)
  have he : ∀ r, QuantumZipper.drive 1 B r = rdrv r := by
    intro r
    funext x
    simp [QuantumZipper.drive, B, rdrv]
  simp_rw [he] at hm
  exact hm.inv.neg

/-- The inverse map at a measurable random interior point is measurable.
This uses the existing random-domain limit theorem rather than a new joint
measurability theorem for Loewner maps. -/
theorem measurable_relInv_random {Ω : Type*} [MeasurableSpace Ω] (s : ℝ≥0)
    {r : Ω → RecData} (hr : Measurable r) {z : Ω → ℂ} (hz : Measurable z)
    (hzH : ∀ ω, z ω ∈ H) : Measurable fun ω => relInv (rdrv (r ω)) s (z ω) := by
  refine Restart.measurable_of_tendsto_nhdsWithin (D := fun _ : Ω => H)
      (f := fun ω v => relInv (rdrv (r ω)) s v)
      (fun _ => QuantumZipper.isOpen_H) (fun _ => MeasurableSet.const _) ?_ hz
      (fun ω => subset_closure (hzH ω)) ?_
  · intro v
    by_cases hv : v ∈ H
    · simpa only [hv, ofPred_true, indicator_univ, Function.comp_def] using (measurable_relInv_record s hv).comp hr
    · simp only [hv, ofPred_false, indicator_empty]
      exact measurable_const
  · intro ω
    exact (continuousOn_relInv (continuous_rdrv (r ω)) (rdrv_zero (r ω)) s.coe_nonneg _ (hzH ω)).tendsto

/-- A total Borel inverse readout. The limit has its standard `limUnder`
default when no finite landing value exists. -/
def inverseRead (s : ℝ≥0) (p : RecData × ℂ) : ℂ :=
  limUnder atTop fun n => relInv (rdrv p.1) s (CoordB.vert n (upperPoint p.2))

theorem measurable_inverseRead (s : ℝ≥0) : Measurable (inverseRead s) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  apply Measurable.stronglyMeasurable
  apply measurable_relInv_random s measurable_fst
  · exact (measurable_upperPoint.comp measurable_snd).add_const _
  · intro p
    exact CoordB.vert_mem_H (upperPoint_mem p.2) n

/-- At every nonexceptional point, the total readout is the continuous inverse
extension. No condition is imposed on its values elsewhere. -/
theorem inverseRead_eq (s : ℝ≥0) {r : RecData}
    (hΨ : Q3Rel.IsRetainedChartOff (Q3Rel.invHull (rdrv r) s) (relMap (rdrv r) s)
      (relInv (rdrv r) s) (Q3Rel.relLog (rdrv r) s) (Q3Rel.relBad (rdrv r) s))
    {z : ℂ} (hz : z ∈ invGood (Q3Rel.relBad (rdrv r) s)) :
    inverseRead s (r, z) = invExt (relInv (rdrv r) s) z := by
  have hb : z ∈ Hbar := by
    rw [← closure_H]
    exact invGood_subset_closure _ hz
  have hv : Tendsto (fun n => CoordB.vert n z) atTop (𝓝[H] z) :=
    tendsto_nhdsWithin_iff.2 ⟨CoordB.tendsto_vert z,
      Eventually.of_forall fun n => CoordB.vert_mem_H hb n⟩
  have ht := (tendsto_invExt hΨ hz).comp hv
  unfold inverseRead
  rw [upperPoint_eq hb]
  exact ht.limUnder_eq

/-- Borel inverse read-back of a safe physical point, including a real point. -/
theorem inverseRead_relBdry (s : ℝ≥0) {r : RecData}
    (hΨ : Q3Rel.IsRetainedChartOff (Q3Rel.invHull (rdrv r) s) (relMap (rdrv r) s)
      (relInv (rdrv r) s) (Q3Rel.relLog (rdrv r) s) (Q3Rel.relBad (rdrv r) s))
    {z : ℂ} (hz : z ∈ CoordB.relSafe (rdrv r) s)
    (hy : CoordB.relBdry (rdrv r) s z ∈ invGood (Q3Rel.relBad (rdrv r) s)) :
    inverseRead s (r, CoordB.relBdry (rdrv r) s z) = z := by
  rw [inverseRead_eq s hΨ hy]
  exact invExt_relBdry (continuous_rdrv r) (rdrv_zero r) s.coe_nonneg hΨ hz hy

end InteractingSLE.Supp8.GB6.ReadD
