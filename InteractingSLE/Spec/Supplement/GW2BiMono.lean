/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BiInst
import InteractingSLE.Spec.Supplement.GW2TgMono

/-!
# Decision D3's slow facts on RELDET's monotone exhausting versions (S1 and S3, root `0`)

Packet PROVE-GW2-BUF (round 6). RELDET's export `GW2Rd.exists_schedVersionsA_mono` gives announced GB6 versions
`(R n, V n)` of the schedule instance with finite caps, `V n ≤ V (n + 1)`, and coverage of every pre-contact relative
clock eventually in `n`. On this family:

* **`exists_schedVersions_slowFacts`**: decision D3's two slow facts at root `0`:
  * `VStopCovers` eventually in `n`: almost surely, eventually in `n`, `gain ≤ V n − rootHistCap`;
  * `VDriverId` for each `n`: for the schedule instance on version `n + 1` (SDE's `GW2Sdi.schedInstS`, RELDET's good
    set, any choices), J32's centred capacity driver is the stage driver for every `u < min(gain, V n − rootHistCap)`.
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

/-- **Decision D3's slow facts on RELDET's monotone exhausting versions** (root `0`). -/
theorem exists_schedVersions_slowFacts (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞)
      (hA : ∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)),
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ξ ∂c.P, ∀ᶠ n in atTop,
        (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) ≤ V n ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞)) ∧
      ∀ (ch : ℕ → GW2Sdh.SchedChoice Ω) (n : ℕ), ∀ᵐ ξ ∂c.P, ∀ u : ℝ≥0, u < GW2Sdg.rootGain c r l a ξ →
        (u : ℝ≥0∞) < V n ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) →
        GW2Bf.j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ + u) ξ -
            GW2Bf.j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ) ξ =
          (GW2Sdi.schedInstS c r l a (GW2Sdh.schedGT h13 c r l a) (hA (n + 1)) (ch n)).drv c u ξ := by
  obtain ⟨R, V, hA, hmono, hfin, hev⟩ := exists_schedVersionsA_mono h13 c r l a
  refine ⟨R, V, hA, hmono, hfin, ae_stopCovers_eventually h13 c r l a hroot hev, fun ch n => ?_⟩
  filter_upwards [ae_j32DriverId_schedInstS h13 c r l a hroot (hA (n + 1)) (ch n)] with ξ hid u hu hV
  exact hid u hu (hV.trans_le (tsub_le_tsub_right (hmono n ξ) _))

end InteractingSLE.Theorem14.GW2Bh
