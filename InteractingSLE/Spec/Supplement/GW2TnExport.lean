/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TmZero
import InteractingSLE.Spec.Supplement.GW2SdeNeeds

/-!
# Decision D26, option (A′): the zero-lifetime candidate at the stage record, and the death family at every lifetime

Packet PROVE-GW2-RELDET (round 26). Under (A′) the zero-lifetime candidates are removed from the stage record event
(`E := E₀ \ launchBadRec c r l a`) instead of capping the versions at the stage start (that cap cannot be announced;
see the handoff). Exports:

* **`ae_srec_mem_launchBadRec_iff`**: for EVERY stage instance `I` (SDE's `GW2Sde.StageInst`), almost surely on the
  history's success, `I.srec c r l ω ∈ launchBadRec c r l a ↔ ζ = 0`;
* **`ae_life_pos_of_srec_notMem`**: off `launchBadRec` (on success) the candidate's lifetime is positive, so the
  candidate is launched at a non-threshold seed;
* **`exists_schedVersionsA_strict_death_all`**: RELDET's death family with the exhaustion clause at EVERY lifetime:
  on the history's success every relative clock value before the first contact and below the death clock is
  eventually below `V n`. At `0 < ζ` the caps are strictly below the death clock; at `ζ = 0` the launch gauge's life
  is `⊤`, so the family exhausts the whole pre-contact clock (decision D27's property of the version family).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId Supp8.GB6.SourceC
open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Sec5.Prop513Schedule

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- **The stage record of every instance identifies the zero-lifetime candidate**, almost surely on the history's
success. -/
theorem ae_srec_mem_launchBadRec_iff (I : GW2Sde.StageInst Ω) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω → (I.srec c r l ω ∈ launchBadRec c r l a ↔ candLife c r l a ω = 0) := by
  filter_upwards [ae_mem_launchBadRec_iff c r l a h13] with ω hω hold
  exact hω hold _

include h13 in
/-- **Off `launchBadRec` the candidate's lifetime is positive** (almost surely on the history's success). -/
theorem ae_life_pos_of_srec_notMem (I : GW2Sde.StageInst Ω) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω → I.srec c r l ω ∉ launchBadRec c r l a → 0 < candLife c r l a ω := by
  filter_upwards [ae_srec_mem_launchBadRec_iff h13 c r l a I] with ω hω hold hnot
  exact pos_iff_ne_zero.2 fun hz => hnot ((hω hold).2 hz)

include h13 in
/-- **RELDET's death family with exhaustion at every lifetime**: finite, monotone, strictly increasing on the record
event; at a positive lifetime the caps are strictly below the death clock; and on the history's success (at every
lifetime, including `0`) every relative clock value before the first contact and below the death clock is eventually
below `V n`. -/
theorem exists_schedVersionsA_strict_death_all (hs : 0 < c.s) (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧
      (∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → ∀ n, V n ω < V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → oldSuccess c r l ω → 0 < candLife c r l a ω →
        ∀ n, V n ω < deathClock c r l a ω) ∧
      ∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → oldSuccess c r l ω →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < deathClock c r l a ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < V n ω := by
  obtain ⟨R, V, hRV, hmono, hstrict, hfin, hlt, hex⟩ := exists_schedVersionsA_strict_launch h13 c r l a hs
  refine ⟨R, V, hRV, hmono, hstrict, hfin, ?_, ?_⟩
  · filter_upwards [hlt, ae_schedLaunchLife_eq h13 c r l a hord] with ω h1 h2 hrec hold hζ0 n
    rw [← h2 hold hζ0]
    exact h1 hrec n
  · filter_upwards [hex, ae_schedLaunchLife_eq h13 c r l a hord,
      ae_schedLaunchLife_eq_top_of_zero h13 c r l a hord] with ω h1 h2 h3 hs' hsH hold t ht htl
    refine h1 hs' hsH t ht ?_
    rcases eq_zero_or_pos (candLife c r l a ω) with hz | hpos
    · rw [h3 hold hz]
      exact ENNReal.ofReal_lt_top
    · rw [h2 hold hpos]
      exact htl

end InteractingSLE.Theorem14.GW2Rd
