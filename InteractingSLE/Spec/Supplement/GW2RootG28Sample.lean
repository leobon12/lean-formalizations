/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootG28Actual
import InteractingSLE.Spec.Supplement.GW2RootE26Actual

/-!
# Killing the actual normalized sample at the geometric failure buffer

Packet PROVE-T14-GW2ROOT2. The sample is measurably killed at the
capacity of the constructed random physical buffer. Its reach event
is exactly physical entry before that buffer on protected source prefixes.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootG28

open Exist Staged StagedLaw Restart Supp8.GB6 RootD25 RootV7

/-- The actual normalized sample killed at the random geometric buffer. -/
def bufferedSample (a s v b : ℝ≥0) (m : ℕ) (p : RecData × RecData) : DriverRecord :=
  cutRecord (physicalClock a s (contactBuffer s v b m p) p) (relativeSample a s v p)

theorem measurable_bufferedSample (a s v b : ℝ≥0) (m : ℕ) :
    Measurable (bufferedSample a s v b m) := by
  have hclock : Measurable fun p => physicalClock a s (contactBuffer s v b m p) p :=
    measurable_const.mul
      (RootZ21.measurable_forwardCapacity_random s measurable_id
        (measurable_contactBuffer s v b m)).real_toNNReal
  exact measurable_cutRecord (measurable_coe_nnreal_ennreal.comp hclock)
    (measurable_relativeSample a s v)

/-- Buffer killing keeps precisely the original rational crossings
before the shorter lifetime. This uses the landed countable-passage formula. -/
theorem cutRecord_mem_reach_iff (L : ℝ≥0∞) (z : DriverRecord) :
    cutRecord L z ∈ reachSet ↔ entryCapacity z < min L z.1 := by
  change entryCapacity (cutRecord L z) < (cutRecord L z).1 ↔ _
  rw [entryCapacity_lt_iff, entryCapacity_lt_iff]
  constructor
  · rintro ⟨q, hq, _, hY⟩
    change ((q : ℝ≥0) : ℝ≥0∞) < min L z.1 at hq
    change 2 < (if ((q : ℝ≥0) : ℝ≥0∞) < min L z.1 then z.2 q else 0) at hY
    rw [ite_eq_left hq] at hY
    exact ⟨q, hq, hq.trans_le (min_le_right _ _), hY⟩
  · rintro ⟨q, hq, _, hY⟩
    refine ⟨q, hq, hq, ?_⟩
    change 2 < (if ((q : ℝ≥0) : ℝ≥0∞) < min L z.1 then z.2 q else 0)
    rwa [ite_eq_left hq]

/-- The sample's live rational driver readings remain exact everywhere. -/
theorem bufferedSample_read (a s v b : ℝ≥0) (m : ℕ) (p : RecData × RecData)
    {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ≥0∞) < (bufferedSample a s v b m p).1) :
    (bufferedSample a s v b m p).2 q = RootB23.scaledRelativeDriverRead a s v q p := by
  change (if ((q : ℝ≥0) : ℝ≥0∞) < (bufferedSample a s v b m p).1 then
    (relativeSample a s v p).2 q else 0) = _
  rw [ite_eq_left hq]
  exact relativeSample_read a s v p (hq.trans_le (min_le_right _ _))

/-- The reach identification for the sample killed at the constructed
random buffer follows from the proved original clock and entry identities. -/
theorem bufferedSample_mem_reach_iff {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
    {s : ℝ≥0} (hsH : α s ∈ H) {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace e.1 e.2 γ)
    {v : ℝ≥0} (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)
    {a : ℝ≥0} (ha : 0 < a) {b : ℝ≥0} (hbv : b ≤ v) (m : ℕ) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    bufferedSample a s v b m p ∈ reachSet ↔
      entryPhysical a s v p < contactBuffer s v b m p := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  have hFv := (contactBuffer_le s v b m p).trans hbv
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  obtain ⟨_, hm, _⟩ := RootE26.physicalClock_regular
    W ζ ω hα hW.continuousOn hW0 hs hsH he hγ hv ha
  have hclock : (physicalClock a s (contactBuffer s v b m p) p : ℝ≥0∞) ≤
      (relativeSample a s v p).1 := ENNReal.coe_le_coe.mpr
    (hm.monotoneOn ⟨zero_le, hFv⟩ ⟨zero_le, le_rfl⟩ hFv)
  change cutRecord _ _ ∈ reachSet ↔ _
  rw [cutRecord_mem_reach_iff, min_eq_left hclock]
  exact (RootE26.entryPhysical_lt_iff_capacity
    W ζ ω hα hW hW0 hζ hsH he hγ hv ha hFv).symm

end InteractingSLE.Theorem14.GW2TipSystem.RootG28
