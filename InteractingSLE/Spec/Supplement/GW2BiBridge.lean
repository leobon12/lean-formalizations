/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BiMono
import InteractingSLE.Spec.Supplement.GW2SdxPair

/-!
# SDE's indexed slow inputs from the version-level slow facts (decision D3, root `0`)

Packet PROVE-GW2-BUF (round 6). SDE's successor asks for `GW2Sdx.VDriverIdN V … n` and `GW2Sdx.VStopCoversN V …` about
the slow variables `slowVar l a n` of a version-indexed package. This file derives them from round 6's version-level
facts, for any package whose slow variable `n` is the schedule instance on an announced version, with a stop below
that version's bound:

* **`vDriverIdN_of_schedInstS`**: if `slowVar l a n` has the stage driver of `GW2Sdi.schedInstS` on a version `(R, V)`
  and its stop stays below `V − rootHistCap` up to the gain, then `VDriverIdN` holds for `n`;
* **`vStopCoversN_of_eventually`**: if eventually in `n` the stop dominates `V n − rootHistCap` for a family covering
  the gain eventually (`exists_schedVersions_slowFacts`), then `VStopCoversN` holds.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open GW2Sde GW2Sdg GW2Sdi GW2Sdx GW2TipSystem GW2TipSystem.RootC24 GW2Rd

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **`VDriverIdN` for a slow variable on the schedule instance** (root `0`). -/
theorem vDriverIdN_of_schedInstS (h13 : Exist.Theorem13Statement.{u}) {V : VPkgXFamily.{u}} (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ) (hroot : rootPt r.1 = 0)
    {R : ℝ≥0 → Ω → ℝ} {Vc : Ω → ℝ≥0∞}
    (hA : Supp8.Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R Vc)
    (ch : GW2Sdh.SchedChoice Ω)
    (hR : ∀ u ξ, ((V Ω c r).slowVar l a n).R u ξ =
      (schedInstS c r l a (GW2Sdh.schedGT h13 c r l a) hA ch).drv c u ξ)
    (hstop : ∀ᵐ ξ ∂c.P, ∀ u : ℝ≥0, u < rootGain c r l a ξ → (u : ℝ≥0∞) < ((V Ω c r).slowVar l a n).stop ξ →
      (u : ℝ≥0∞) < Vc ξ - (rootHistCap c r l a ξ : ℝ≥0∞)) :
    VDriverIdN V Ω c r l a n := by
  filter_upwards [ae_j32DriverId_schedInstS h13 c r l a hroot hA ch, hstop] with ξ hid hst _ u hu hV
  rw [hR]
  exact hid u hu (hst u hu hV)

/-- **`VStopCoversN` from an eventually covering family** (root `0`). -/
theorem vStopCoversN_of_eventually {V : VPkgXFamily.{u}} (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {Vn : ℕ → Ω → ℝ≥0∞}
    (hcov : ∀ᵐ ξ ∂c.P, ∀ᶠ n in atTop,
      (rootGain c r l a ξ : ℝ≥0∞) ≤ Vn n ξ - (rootHistCap c r l a ξ : ℝ≥0∞))
    (hstop : ∀ᵐ ξ ∂c.P, ∀ᶠ n in atTop,
      Vn n ξ - (rootHistCap c r l a ξ : ℝ≥0∞) ≤ ((V Ω c r).slowVar l a n).stop ξ) :
    VStopCoversN V Ω c r l a := by
  filter_upwards [hcov, hstop] with ξ h1 h2 _
  filter_upwards [h1, h2] with n hn1 hn2
  exact hn1.trans hn2

end InteractingSLE.Theorem14.GW2Bh
