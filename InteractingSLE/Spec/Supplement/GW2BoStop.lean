/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RvSlow
import InteractingSLE.Spec.Supplement.GW2BnStop

/-!
# The near stop at a root: the exit, capped strictly below the instance cap (NearStopsX, generic)

Packet PROVE-GW2-BUF (round 12). A root-`x` stage stop must be strictly below the instance cap whenever it is finite
(`StageStop.GoodX.stop_lt`). So the near stop is the minimum of two stops:

* ROOTX's lower-cap stop `lowCapStopX` (round 6's `lowCapStop` at a root): `V_low − start` on the good records, read
  by the stage rule of a version rule;
* an exit rule `E` (any measurable path rule on (stage record, killed stage path)), e.g. D16's `GW2BnStop.shapeStop`.

**`nearStopX`** is this minimum. **`nearStopX_goodX`**: if the lower-cap stop is `GoodX` and the lower cap is finite and
below the instance's cap, then the near stop is `GoodX` for every measurable path rule `E`. The parts:
* `rule_meas`: the union of the two killed-path events (`GW2Bh.measurableSet_killPath_le` for `E`);
* `measurable_stop`: the stage record, driver and cap are measurable (`measurable_augRec`,
  `GW2Sde.measurable_stageEncRec`, ROOTX's `measurable_stgRX`/`measurable_stgVX`);
* `stop_eq`: from the lower-cap stop's;
* `stop_le` and `stop_lt`: the minimum is below the lower-cap stop, which is finite.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.HullId GW2TipSystem
  GW2TipSystem.RootC24 GW2Rd GW2Rz GW2Rv GW2Sde

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The near stop at a root**: the minimum of the lower-cap stop and an exit rule on the killed stage path. -/
def nearStopX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (I : StageInst Ω)
    (x₀ : ℝ) (Vlow : Ω → ℝ≥0∞) (ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) (E : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) :
    StageStop Ω where
  stop ω := min ((lowCapStopX c l I x₀ Vlow ρ).stop ω)
    (E (I.srecX c r l x₀ ω, killPath ((fun t => I.drvX c x₀ t ω), I.capX c x₀ ω)))
  rule y e := min ((lowCapStopX c l I x₀ Vlow ρ).rule y e) (E (y, killPath e))

/-- The killed stage path of a measurable driver and cap is measurable. -/
theorem measurable_killPath_comp {D : ℝ≥0 → Ω → ℝ} (hD : ∀ t, Measurable (D t)) {V : Ω → ℝ≥0∞} (hV : Measurable V) :
    Measurable fun ω => killPath ((fun t => D t ω), V ω) := by
  refine measurable_pi_iff.2 fun t => ?_
  unfold killPath
  exact Measurable.ite (measurableSet_lt measurable_const hV) (hD t) measurable_const

/-- **The near stop is a good root-`x` stage stop.** -/
theorem nearStopX_goodX [StandardBorelSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {l : List (EntryIdx c.Θ c.Q)} {x₀ : ℝ} {I : StageInst Ω} (hI : I.GoodX c r l x₀) {Vlow : Ω → ℝ≥0∞}
    {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hL : (lowCapStopX c l I x₀ Vlow ρ).GoodX I c r l x₀)
    (hVfin : ∀ ω, I.V ω ≠ ⊤) (hle : ∀ᵐ ω ∂c.P, Vlow ω ≤ I.V ω) {E : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hEp : IsPathRule E) (hEm : Measurable E) : (nearStopX c r l I x₀ Vlow ρ E).GoodX I c r l x₀ := by
  classical
  have hRm := hI.version.1
  have hRc := hI.version.2.1
  have hpre := hI.measurable_pre
  have hrec : Measurable (I.srecX c r l x₀) := measurable_augRec (measurable_stageEncRec c r l) hpre
  have hdrv : ∀ t, Measurable (I.drvX c x₀ t) := fun t => measurable_stgRX hRm hRc hpre t
  have hcap : Measurable (I.capX c x₀) := measurable_stgVX hI.version.2.2.2.2.1 hpre
  have hEω : Measurable fun ω => E (I.srecX c r l x₀ ω, killPath ((fun t => I.drvX c x₀ t ω), I.capX c x₀ ω)) :=
    hEm.comp (hrec.prodMk (measurable_killPath_comp hdrv hcap))
  -- the lower-cap stop is finite
  have hLfin : ∀ᵐ ω ∂c.P, (lowCapStopX c l I x₀ Vlow ρ).stop ω ≠ ⊤ := by
    filter_upwards [hle] with ω hω
    simp only [lowCapStopX]
    split_ifs
    · exact ne_top_of_le_ne_top (hVfin ω) (tsub_le_self.trans hω)
    · exact ENNReal.zero_ne_top
  refine ⟨fun y t => ?_, ?_, ?_, ?_, ?_⟩
  · have he : {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | (nearStopX c r l I x₀ Vlow ρ E).rule y e ≤ (t : ℝ≥0∞)} =
        {e | (lowCapStopX c l I x₀ Vlow ρ).rule y e ≤ (t : ℝ≥0∞)} ∪ {e | E (y, killPath e) ≤ (t : ℝ≥0∞)} := by
      ext e
      simp only [nearStopX, mem_ofPred_eq, mem_union, min_le_iff]
    rw [he]
    exact (hL.rule_meas y t).union (measurableSet_killPath_le hEp hEm y t)
  · exact hL.measurable_stop.min hEω
  · filter_upwards [hL.stop_eq] with ω hω
    show min _ _ = min _ _
    rw [hω]
  · filter_upwards [hL.stop_le] with ω hω hE
    exact (min_le_left _ _).trans (hω hE)
  · filter_upwards [hL.stop_lt, hLfin] with ω hω hfin hE _
    exact (min_le_left _ _).trans_lt (hω hE hfin)

end InteractingSLE.Theorem14.GW2Bh
