/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdeNeeds

/-!
# GW2's retained stopped SDE: the live stage records

Packet PROVE-GW2-SDE (round 3). The target `StageInst.Good.E_good` asks, on the stage record event `E`, a good
counterflow record and a LIVE stage (`stgStartM < V`). The cap of GB6's version is a path rule of the counterflow record
and the relative driver, `V = ρ(gb6Rec, R)`, so the event "the cap is reached by the stage start" is decided by the
augmented stage record: `{V ≤ stage start} = {ρ(augσ z, augPre z) ≤ augA z}` (the prefix `augPre` is the relative
driver up to the start `augA`). Hence the live part can be built into `E` itself:

* `aliveRec N s ρ`: the record event `{z | augσ N z ∈ gb6TS s ∧ augA z < ρ (augσ N z, augPre z)}`;
  `measurableSet_aliveRec`;
* **`StageInst.E_good_of_record`**: if `E ⊆ aliveRec`, then `E_good` holds as soon as the stage start is finite on the
  record event (`stgStartM ≠ ⊤`, i.e. the relative clock has not blown up before the stage start).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdf

open GW2Sde GW2Rd Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.HullId Supp8.RelSafe GW2TipSystem GW2TipSystem.RootC24
  Exist.StagedLaw

/-- **The live stage records**: a good counterflow record and the cap not reached by the stage start. -/
def aliveRec (N : ℕ) (s : ℝ≥0) (ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) : Set RecData :=
  {z | augσ N z ∈ gb6TS s ∧ (augA z : ℝ≥0∞) < ρ (augσ N z, augPre z)}

theorem measurableSet_aliveRec (N : ℕ) (s : ℝ≥0) {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : Measurable ρ) :
    MeasurableSet (aliveRec N s ρ) := by
  have hpre : Measurable fun z => augPre z := measurable_pi_iff.2 fun t => measurable_augPre t
  exact ((measurable_augσ N) (measurableSet_gb6TS s)).inter
    (measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_augA)
      (hρ.comp ((measurable_augσ N).prodMk hpre)))

/-- **`Good.E_good` from live stage records**: on `E ⊆ aliveRec`, the counterflow record is good and the stage is
live, wherever the stage start is finite. -/
theorem StageInst.E_good_of_record {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω}
    {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V) (hρ : IsPathRule I.ρ)
    (hVρ : ∀ᵐ ω ∂c.P, I.V ω = I.ρ (gb6Rec c.s c.W c.ζ ω, fun u => I.R u ω))
    (hE : I.E ⊆ aliveRec ((entryList l).length + 1) c.s I.ρ)
    (hfin : ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E → stgStartM c.s I.W c.W c.ζ I.GT I.V I.T ω ≠ ⊤) :
    ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E →
      gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s ∧ stgStartM c.s I.W c.W c.ζ I.GT I.V I.T ω < I.V ω := by
  filter_upwards [hVρ, hfin] with ω hV hf hEω
  obtain ⟨hd1, hd2, hd3⟩ := augDec_spec (s := c.s) (W := I.W) (Wα := c.W) (ζα := c.ζ) (GT := I.GT) (V := I.V)
    (T := I.T) (stgRecDec_stageEncRec c r l ω) (hv.2.1 ω) (hv.2.2.1 ω)
  obtain ⟨hgood, hlt⟩ := hE hEω
  rw [hd1] at hgood hlt
  refine ⟨hgood, ?_⟩
  have hS : ((stgStart c.s I.W c.W c.ζ I.GT I.V I.T ω : ℝ≥0) : ℝ≥0∞) = stgStartM c.s I.W c.W c.ζ I.GT I.V I.T ω :=
    ENNReal.coe_toNNReal (hf hEω)
  rw [← hS]
  by_contra hcon
  have hle : I.V ω ≤ (stgStart c.s I.W c.W c.ζ I.GT I.V I.T ω : ℝ≥0∞) := not_lt.1 hcon
  have hpr : I.ρ (gb6Rec c.s c.W c.ζ ω, augPre (I.srec c r l ω)) =
      I.ρ (gb6Rec c.s c.W c.ζ ω, fun u => I.R u ω) := by
    refine hρ _ _ _ fun u hu => ?_
    have hu' : (u : ℝ≥0∞) ≤ (stgStart c.s I.W c.W c.ζ I.GT I.V I.T ω : ℝ≥0∞) := (hV ▸ hu).trans hle
    exact (hd3 u (hd2 ▸ ENNReal.coe_le_coe.1 hu')).symm
  rw [hd2, hpr, ← hV] at hlt
  exact absurd (hlt.trans_le hle) (lt_irrefl _)

end InteractingSLE.Theorem14.GW2Sdf
