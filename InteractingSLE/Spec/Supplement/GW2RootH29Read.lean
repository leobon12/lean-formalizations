/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH29Cover
import InteractingSLE.Spec.Supplement.GW2RootA22Read

/-!
# Borel hull, capacity and tip readers for the low-arc roots

Packet PROVE-T14-GW2ROOT2. Translate the physical hull before applying
the retained chart. Center the charted tip at the image of the actual
root. The readers are Borel on all records, also at a random own time;
live source prefixes prove their exact consistency under recording.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH29

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart RootC24 Supp8.GB6

/-- The physical hull of a piece based at the real root `x`. -/
def translatedHull (x : ℝ) (t : ℝ≥0) (r : RecData) : Set ℂ :=
  (fun z : ℂ => (x : ℂ) + z) '' QuantumZipper.fwdHull (rdrv r) t

/-- Translation by a real root preserves hitting measurability,
including random physical cutoffs. -/
theorem measurable_translatedHull_random {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (x : ℝ) {r : Ω → RecData} (hr : Measurable r) {t : Ω → ℝ≥0} (ht : Measurable t) :
    Measurable[mΩ, hittingSigma] fun ω => translatedHull x (t ω) (r ω) := by
  have hK := GW2JDetR4.measurable_fwdHull_rdrv_time hr ht
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have he : (fun ω => translatedHull x (t ω) (r ω)) ⁻¹'
      {A : Set ℂ | (A ∩ U).Nonempty} =
      (fun ω => QuantumZipper.fwdHull (rdrv (r ω)) (t ω)) ⁻¹'
        {A : Set ℂ | (A ∩ (fun z : ℂ => (x : ℂ) + z) ⁻¹' U).Nonempty} := by
    ext ω
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, hU⟩
      exact ⟨z, hz, hU⟩
    · rintro ⟨z, hz, hU⟩
      exact ⟨_, ⟨z, hz, rfl⟩, hU⟩
  rw [he]
  refine hK (LocalSets.measurableSet_hitting
    (hU.preimage (continuous_const.add continuous_id)) ?_)
  intro z hz
  have hH := hUH hz
  change 0 < ((x : ℂ) + z).im at hH
  change 0 < z.im
  simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hH

/-- The visible translated hull in the original retained joint chart. -/
def forwardHull (x : ℝ) (s t : ℝ≥0) (p : RecData × RecData) : Set ℂ :=
  relMap (rdrv p.1) s '' (translatedHull x t p.2 ∩ CoordB.relDomain (rdrv p.1) s)

/-- Half-capacity in that chart. Real recentering does not change the
hydrodynamic capacity used here. -/
def forwardCapacity (x : ℝ) (s t : ℝ≥0) (p : RecData × RecData) : ℝ :=
  (WholeField.hcapHit (forwardHull x s t p)).toReal / 2

theorem measurable_forwardCapacity_random {Ω : Type*} [MeasurableSpace Ω]
    (x : ℝ) (s : ℝ≥0) {p : Ω → RecData × RecData} (hp : Measurable p)
    {t : Ω → ℝ≥0} (ht : Measurable t) :
    Measurable fun ω => forwardCapacity x s (t ω) (p ω) := by
  have hm := RootZ21.measurable_image_relMap s (measurable_fst.comp hp)
    (measurable_translatedHull_random x (measurable_snd.comp hp) ht)
  exact ((WholeField.measurable_hcapHit.comp hm).ennreal_toReal).div_const 2

theorem forwardCapacity_nonneg (x : ℝ) (s t : ℝ≥0) (p : RecData × RecData) :
    0 ≤ forwardCapacity x s t p := div_nonneg ENNReal.toReal_nonneg (by norm_num)

/-- At zero this is exactly the landed clock reader, not a new convention. -/
theorem forwardCapacity_zero_root (s t : ℝ≥0) (p : RecData × RecData) :
    forwardCapacity 0 s t p = RootZ21.forwardCapacity s t p := by
  simp only [forwardCapacity, forwardHull, translatedHull, Complex.ofReal_zero,
    zero_add, Set.image_id', RootZ21.forwardCapacity, RootZ21.forwardHull]

/-- Earlier physical hull capacities are unchanged by a later live record. -/
theorem forwardCapacity_prefix_eq (x : ℝ) (s : ℝ≥0) (r : RecData)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    {v : ℝ≥0} (hv : (v : ℝ≥0∞) < e.2) {t : ℝ≥0} (htv : t ≤ v) :
    forwardCapacity x s t (r, recOf (v : ℝ≥0∞) e) =
      forwardCapacity x s t (r, recOf (t : ℝ≥0∞) e) := by
  unfold forwardCapacity forwardHull translatedHull
  rw [RootZ21.fwdHull_record_of_le_of_live he hv htv,
    RootZ21.fwdHull_record_of_live he ((ENNReal.coe_le_coe.mpr htv).trans_lt hv)]

/-- Boundary evaluation in the translated chart, centered at its root. -/
def rootChartRead (x : ℝ) (s : ℝ≥0) (p : RecData × ℂ) : ℂ :=
  RootA22.boundaryRead s (p.1, (x : ℂ) + p.2) -
    RootA22.boundaryRead s (p.1, (x : ℂ))

theorem measurable_rootChartRead (x : ℝ) (s : ℝ≥0) : Measurable (rootChartRead x s) :=
  ((RootA22.measurable_boundaryRead s).comp
    (measurable_fst.prodMk (measurable_const.add measurable_snd))).sub
      ((RootA22.measurable_boundaryRead s).comp (measurable_fst.prodMk measurable_const))

theorem rootChartRead_zero (x : ℝ) (s : ℝ≥0) (r : RecData) :
    rootChartRead x s (r, 0) = 0 := by
  simp only [rootChartRead, add_zero, sub_self]

/-- The physical-time relative tip based at the actual low-arc root. -/
def rootTipRead (x : ℝ) (s t : ℝ≥0) (p : RecData × RecData) : ℂ :=
  rootChartRead x s (p.1, RootA22.physicalTipRead (p.2, t))

theorem measurable_rootTipRead_random {Ω : Type*} [MeasurableSpace Ω]
    (x : ℝ) (s : ℝ≥0) {p : Ω → RecData × RecData} (hp : Measurable p)
    {t : Ω → ℝ≥0} (ht : Measurable t) :
    Measurable fun ω => rootTipRead x s (t ω) (p ω) :=
  (measurable_rootChartRead x s).comp ((measurable_fst.comp hp).prodMk
    (RootA22.measurable_physicalTipRead.comp ((measurable_snd.comp hp).prodMk ht)))

/-- The same original tip is read through any later live recording cutoff. -/
theorem rootTipRead_prefix_eq (x : ℝ) (s : ℝ≥0) (r : RecData)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace e.1 e.2 γ)
    {v t : ℝ≥0} (hv : (v : ℝ≥0∞) < e.2) (htv : t ≤ v) :
    rootTipRead x s t (r, recOf (v : ℝ≥0∞) e) =
      rootTipRead x s t (r, recOf (t : ℝ≥0∞) e) := by
  unfold rootTipRead
  rw [RootA22.physicalTipRead_recOf_eq he hγ hv htv,
    RootA22.physicalTipRead_recOf_eq he hγ
      ((ENNReal.coe_le_coe.mpr htv).trans_lt hv) le_rfl]

end InteractingSLE.Theorem14.GW2TipSystem.RootH29
