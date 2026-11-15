/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootE26Read
import InteractingSLE.Spec.Supplement.GW2RootE26Passage

/-!
# The Borel past-crossing gate is the actual physical-entry gate

Packet PROVE-T14-GW2ROOT2. Strict increase of the actual clock compares
entry with any physical query, including the recording endpoint. The
countable gate therefore gives the actual gated physical driver and tip.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootE26

open Exist Staged StagedLaw Restart Supp8.GB6 RootB23 RootD25

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hsH : α s ∈ H)
  {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
  (hv : (v : ℝ≥0∞) < min
    (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)
  {a : ℝ≥0} (ha : 0 < a)

include hα hW hW0 hζ hsH he hγ hv ha

theorem entryPhysical_lt_iff_capacity {q : ℝ≥0} (hq : q ≤ v) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    entryPhysical a s v p < q ↔
      entryCapacity (relativeSample a s v p) < (physicalClock a s q p : ℝ≥0∞) := by
  dsimp only
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  let z := relativeSample a s v p
  change entryPhysical a s v p < q ↔ entryCapacity z < (physicalClock a s q p : ℝ≥0∞)
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  obtain ⟨_, hm, _⟩ := physicalClock_regular
    W ζ ω hα hW.continuousOn hW0 hs hsH he hγ hv ha
  by_cases hreach : z ∈ reachSet
  · have hS := (entryPhysical_spec_before_contact
      W ζ ω hα hW hW0 hζ hsH he hγ hv ha hreach).1
    have hτcoe : ((entryCapacity z).toNNReal : ℝ≥0∞) = entryCapacity z :=
      ENNReal.coe_toNNReal (ne_top_of_lt (hreach.trans ENNReal.coe_lt_top))
    have hclock := physicalClock_entryPhysical
      W ζ ω hα hW.continuousOn hW0 hs hsH he hγ hv ha hreach
    have hiff := (hm.lt_iff_lt ⟨zero_le, hS.le⟩ ⟨zero_le, hq⟩).symm
    rw [hclock] at hiff
    rw [← hτcoe]
    exact hiff.trans ENNReal.coe_lt_coe.symm
  · have hfail : z.1 ≤ entryCapacity z := not_lt.mp hreach
    have hclock := hm.monotoneOn ⟨zero_le, hq⟩ ⟨zero_le, le_rfl⟩ hq
    exact iff_of_false
      (by rw [entryPhysical_eq_cutoff hreach]; exact not_lt_of_ge hq)
      (not_lt_of_ge ((ENNReal.coe_le_coe.mpr hclock).trans hfail))

/-- Every strict entry comparison is a countable test of the past,
including at a successful finite recording cutoff. -/
theorem mem_crossedBefore_iff_entry {q : ℝ≥0} (hq : q ≤ v) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    p ∈ crossedBefore a s v q ↔ entryPhysical a s v p < q := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  obtain ⟨h0, hm, hc⟩ := physicalClock_regular
    W ζ ω hα hW.continuousOn hW0 hs hsH he hγ hv ha
  obtain ⟨_, hcdrv, _⟩ := relative_readers_generatingTrace_before_contact
    W ζ ω hα hW hW0 hζ hsH he hγ hv
  have hY : ContinuousOn (fun t => scaledRelativeDriverRead a s v t p)
      {t | (t : ℝ≥0∞) < (relativeSample a s v p).1} := by
    simpa only [relativeSample, physicalClock, scaledRelativeDriverRead, ENNReal.coe_mul]
      using Sec5.Prop59NodeTree.continuousOn_scale ha hcdrv
  have hdetect := entryCapacity_lt_clock_iff hY
    (fun r hr => relativeSample_read a s v p hr) h0 hm hc rfl hq
  exact hdetect.symm.trans
    (entryPhysical_lt_iff_capacity W ζ ω hα hW hW0 hζ hsH he hγ hv ha hq).symm

theorem cutoffObservationRead_eq_actual {q : ℝ≥0} (hq : q ≤ v) (F : ℝ≥0) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    cutoffObservationRead a s v F q p =
      if entryPhysical a s v p < q ∧ q < F then
        physicalObservationRead a s v q p else (0, 0) := by
  dsimp only
  have hgate := mem_crossedBefore_iff_entry W ζ ω hα hW hW0 hζ hsH he hγ hv ha hq
  dsimp only at hgate
  simp only [cutoffObservationRead, crossedObservationRead, hgate]
  by_cases hqF : q < F <;> by_cases hSq : entryPhysical a s v
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) < q <;>
    simp only [hqF, hSq, and_self, and_false, and_true, ↓reduceIte]

end InteractingSLE.Theorem14.GW2TipSystem.RootE26
