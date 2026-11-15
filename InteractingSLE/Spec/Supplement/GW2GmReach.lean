/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmClock

/-!
# Reach identification for J31's construction

Packet PROVE-GW2-GEOM2 (step R4). The field `reach_identification` of the open geometry asks that the
actual sample reaches the band (`RootD25.reachSet`) exactly when the physical entry is strictly before the
physical failure, up to null sets. J31 proves the direction `S < F → reach` everywhere
(`RootJ31.entry_lt_failure_imp_reach`). The converse uses the switched clock: the entry is the rational
supremum of the times whose capacity increment is below the entry capacity (`Restart.invClock`), and the
increment is continuous at the buffer (`GW2GmClock.ae_live_clock`), so the supremum stays strictly below
the buffer.

* `invClock_lt_of_continuousWithinAt`: a clock's rational inverse supremum at a level strictly below its
  value at the cap is strictly below the cap, when the clock is left-continuous at the cap;
* **`ae_reach_imp_entry_lt_failure`**: almost surely, a reached sample has entry strictly before failure;
* **`reach_identification`**: the field `reach_identification` of `ExperimentGeometryU` for
  `RootJ31.constructionFamily`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24

/-- **The rational inverse supremum stays below the cap.** If `a` is continuous at `F` within `[0, F]`,
`F > 0` and the level `u` is strictly below `a F`, then `invClock a F u < F`. -/
theorem invClock_lt_of_continuousWithinAt {a : ℝ≥0 → ℝ} {F u : ℝ≥0} (hF : 0 < F)
    (hc : ContinuousWithinAt a (Icc 0 F) F) (hu : (u : ℝ) < a F) :
    Restart.invClock a (F : ℝ≥0∞) u < F := by
  have hev : ∀ᶠ t in 𝓝[Icc 0 F] F, (u : ℝ) < a t := hc.eventually (lt_mem_nhds hu)
  obtain ⟨U, hU, hUS⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hev
  obtain ⟨l, hlF, hlU⟩ := exists_Ioc_subset_of_mem_nhds hU ⟨0, hF⟩
  refine lt_of_le_of_lt (ciSup_le fun q => ?_) hlF
  split_ifs with hq
  · by_contra hlt
    have hmem : (q : ℝ).toNNReal ∈ U ∩ Icc 0 F :=
      ⟨hlU ⟨lt_of_not_ge hlt, ENNReal.coe_le_coe.1 hq.2.1⟩,
        ⟨zero_le, ENNReal.coe_le_coe.1 hq.2.1⟩⟩
    exact absurd (hUS hmem) (not_lt.2 hq.2.2.le)
  · exact zero_le

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **A reached sample has its physical entry strictly before its physical failure**, almost surely,
for every history and candidate. -/
theorem ae_reach_imp_entry_lt_failure (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
      RootJ31.sourceSample c r l a ω ∈ RootD25.reachSet →
        RootJ31.sourceEntry c r l a ω < RootJ31.sourceFailure c r l a ω := by
  filter_upwards [ae_live_clock h13 c r] with ω hω l a hreach
  set T := RootJ31.historyTime c r l with hT
  set F := RootJ31.sourceBuffer c r l a ω with hF
  set p := RootJ31.futurePair c r l a ω with hp
  set z := RootJ31.sourceSample c r l a ω with hz
  have hz1 : 0 < z.1 := lt_of_le_of_lt bot_le hreach
  obtain ⟨-, -, -, -, hcont, -, -⟩ := hω l a hz1
  have hzF : z.1 = (RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s T F p : ℝ≥0∞) := rfl
  have hF0 : 0 < F := RootK32.sourceBuffer_pos_of_sample_life_pos c r l a ω hz1
  -- the increment is continuous at the buffer within `[0, F]`
  have hinc : ContinuousWithinAt
      (fun t => ((RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s T t p : ℝ≥0) : ℝ))
      (Icc 0 F) F := by
    have hmaps : MapsTo (fun t : ℝ≥0 => T + t) (Icc 0 F) (Icc 0 (T + F)) :=
      fun t ht => ⟨zero_le, add_le_add le_rfl ht.2⟩
    have hA : ContinuousWithinAt
        (fun t : ℝ≥0 => RootH29.forwardCapacity (rootPt r.1) c.s (T + t) p) (Icc 0 F) F :=
      (hcont (T + F) ⟨zero_le, le_rfl⟩).comp (continuous_const.add continuous_id).continuousWithinAt
        hmaps
    have h1 := hA.sub (continuousWithinAt_const
      (b := RootH29.forwardCapacity (rootPt r.1) c.s T p))
    have hg : Continuous fun y : ℝ => ((((2 : ℝ≥0) ^ r.2) ^ 2 * y.toNNReal : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (continuous_const.mul continuous_real_toNNReal)
    exact hg.continuousAt.comp_continuousWithinAt h1
  -- the entry capacity is a finite level strictly below the increment at the buffer
  have hfin : RootD25.entryCapacity z ≠ ⊤ := ne_top_of_lt hreach
  have hlev : ((RootD25.entryCapacity z).toNNReal : ℝ) <
      ((RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s T F p : ℝ≥0) : ℝ) := by
    have h := hreach
    change RootD25.entryCapacity z < z.1 at h
    rw [hzF, ← ENNReal.coe_toNNReal hfin, ENNReal.coe_lt_coe] at h
    exact_mod_cast h
  have hentry : RootJ31.switchedEntry (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s
      (T + RootJ31.candidateCap c r a) (rootEntry r.1).2 T F p < F := by
    have hr' : RootJ31.switchedSample (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s
        (T + RootJ31.candidateCap c r a) (rootEntry r.1).2 T F p ∈ RootD25.reachSet := hreach
    unfold RootJ31.switchedEntry
    simp only [hr', ↓reduceIte]
    exact invClock_lt_of_continuousWithinAt hF0 hinc hlev
  change ((T + _ : ℝ≥0) : ℝ) < ((T + F : ℝ≥0) : ℝ)
  exact NNReal.coe_lt_coe.2 (add_lt_add_right hentry T)

/-- **The field `reach_identification`** of the open geometry for J31's construction. -/
theorem reach_identification (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    (RootJ31.experiment c r).data.sample l a ⁻¹' (RootJ31.experiment c r).data.reach l a =ᵐ[c.P]
      {ω | (RootJ31.experiment c r).data.S l a ω < (RootJ31.experiment c r).data.F l a ω} := by
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [ae_reach_imp_entry_lt_failure h13 c r] with ω hω
  exact ⟨hω l a, RootJ31.entry_lt_failure_imp_reach c r l a ω⟩

end InteractingSLE.Theorem14.GW2TipSystem.Gm
