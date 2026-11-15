/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BiCov
import InteractingSLE.Spec.Supplement.GW2SdiInst

/-!
# Decision D3's `VDriverId` for the schedule instance's stage driver (S1, root `0`)

Packet PROVE-GW2-BUF (S1, round 6). Under decision D3 the slow stage variable on member `n` of RELDET's family is the
schedule instance on an announced GB6 version `(R, V)`. Its stage driver is `stgDrv R start`, with the stage start
`start = min(physClock T, V)`.

* **`ae_stgStart_eq_histCap`**: on RELDET's good set, at every live sample whose history capacity is below `V`, the
  stage start is J32's history capacity `rootHistCap` (the physical clock is GB6's relative clock before contact,
  `RelSafe.physClock_eq_gb6Clock`);
* **`ae_j32DriverId_schedInstS`**: `VDriverId` in decision D3's indexed form for SDE's corrected schedule instance
  `GW2Sdi.schedInstS` with RELDET's good set. For every `u < rootGain` with `u < V − rootHistCap`,
  `j32Read (F_T + u) − j32Read F_T = (schedInstS …).drv c u`. A stop `V n − start` with `V n ≤ V` (the family is
  monotone) is below this bound.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.RelDrv GW2TipSystem GW2TipSystem.RootC24 GW2Rd

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The stage start is the history capacity** (root `0`, live samples, below the cap). -/
theorem ae_stgStart_eq_histCap (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) (V : Ω → ℝ≥0∞) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 → ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) < V ξ →
      stgStart c.s (schedW c r l a) c.W c.ζ (GW2Sdh.schedGT h13 c r l a) V (RootJ31.historyTime c r l) ξ =
        GW2Sdg.rootHistCap c r l a ξ := by
  obtain ⟨hgood, -, hGT⟩ := GW2Sdh.schedGT_spec h13 c r l a
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  filter_upwards [ae_exactPair_root0 h13 c r l a hroot, hGT, ae_gb6RecGood hfl hα c.s]
    with ξ hpair hGTξ hrec hlive hV
  obtain ⟨hsζ, hsH, hTc, -, hK⟩ := hpair hlive
  have hm : gb6Rec c.s c.W c.ζ ξ ∈ gb6TS c.s := (mem_gb6TS_iff hrec).1 ⟨hsζ, hsH⟩
  have hξ : ξ ∈ GW2Sdh.schedGT h13 c r l a := hGTξ.2 hm
  have hT : ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ξ :=
    (ENNReal.coe_le_coe.2 le_self_add).trans_lt hTc
  have hcl := RelSafe.physClock_eq_gb6Clock hgood hξ hT
  have hhist : GW2Sdg.rootHistCap c r l a ξ =
      (gb6Clock c.s (schedW c r l a) c.W ξ (RootJ31.historyTime c r l)).toNNReal := by
    unfold GW2Sdg.rootHistCap GW2Sdg.rootCapAt
    rw [GW2Bf.forwardCapacity_future_eq_exact c r l a ξ le_self_add, (hK _ le_self_add).2]
  have hle : ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ξ (RootJ31.historyTime c r l)) ≤ V ξ := by
    rw [ENNReal.ofReal, ← hhist]
    exact hV.le
  change (min (RelSafe.physClock c.s (schedW c r l a) c.W c.ζ (GW2Sdh.schedGT h13 c r l a)
    (RootJ31.historyTime c r l) ξ) (V ξ)).toNNReal = _
  rw [hcl, min_eq_left hle, hhist]
  rfl

/-- **Decision D3's `VDriverId` for the schedule instance's stage driver** (root `0`). -/
theorem ae_j32DriverId_schedInstS (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V)
    (ch : GW2Sdh.SchedChoice Ω) :
    ∀ᵐ ξ ∂c.P, ∀ u : ℝ≥0, u < GW2Sdg.rootGain c r l a ξ →
      (u : ℝ≥0∞) < V ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) →
      GW2Bf.j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ + u) ξ -
          GW2Bf.j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ) ξ =
        (GW2Sdi.schedInstS c r l a (GW2Sdh.schedGT h13 c r l a) hA ch).drv c u ξ := by
  filter_upwards [ae_j32DriverId_version_sub h13 c r l a hroot hA.1.1, ae_stgStart_eq_histCap h13 c r l a hroot V]
    with ξ hid hst u hu hV
  have hgain : 0 < GW2Sdg.rootGain c r l a ξ := lt_of_le_of_lt zero_le hu
  have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 := by
    rw [GW2Sdg.sourceSample_fst]
    exact ENNReal.mul_pos (pow_ne_zero _ (by norm_num)) (ENNReal.coe_ne_zero.2 hgain.ne')
  have hV0 : ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) < V ξ := by
    have h := lt_tsub_iff_left.1 hV
    exact (le_self_add).trans_lt h
  rw [hid u hu hV]
  change _ = stgDrv (fun u => R u ξ)
    (stgStart c.s (schedW c r l a) c.W c.ζ (GW2Sdh.schedGT h13 c r l a) V (RootJ31.historyTime c r l) ξ) u
  rw [hst hlive hV0]
  rfl

end InteractingSLE.Theorem14.GW2Bh
