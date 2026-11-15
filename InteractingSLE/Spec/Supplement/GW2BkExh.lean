/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BiSlowFam
import InteractingSLE.Spec.Supplement.GW2SdyCut

/-!
# The slow stops exhaust the gain (decision D3a's `VStopExhaustsN`, root `0`)

Packet PROVE-GW2-BUF (round 8). Decision D3a replaces `VStopCoversN` by SDE's `GW2Sdy.VStopExhaustsN` ("every
capacity below the gain is eventually below the stop of version `n`"). For the uncapped slow stage variables of round
6 it follows from the cover form. For a capped family `min (V n) (D n)` it follows from the cover of `V` and the
exhaustion of `D` (RELDET's announcing cap, a property of the family):

* `vStopExhaustsN_of_vStopCoversN`;
* **`vStopExhaustsN_slowStageVar`**, **`exists_slowStageVars_exhaust`** (RELDET's committed monotone family, no named
  input);
* **`vStopExhaustsN_of_capped`**: any version-indexed package whose stop `n` dominates `min (Vc n) (Dc n) − rootHistCap`
  on the gate, when `Vc` covers the gain eventually and `Dc` exhausts it.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 GW2Sde GW2Sdg GW2Sdi GW2Sdx GW2Sdy GW2Rd GW2TipSystem GW2TipSystem.RootC24

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The cover form gives the exhaust form. -/
theorem vStopExhaustsN_of_vStopCoversN {V : VPkgXFamily.{u}} {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {l : List (EntryIdx c.Θ c.Q)} {a : ℕ} (h : VStopCoversN V Ω c r l a) : VStopExhaustsN V Ω c r l a := by
  filter_upwards [h] with ξ hξ hG u hu
  filter_upwards [hξ hG] with n hn
  exact (ENNReal.coe_lt_coe.2 hu).trans_le hn

/-- **The uncapped slow stage variables exhaust the gain.** -/
theorem vStopExhaustsN_slowStageVar (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞}
    (hA : ∀ n, Supp8.Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n))
    (ch : ℕ → GW2Sdh.SchedChoice Ω) (hroot : rootPt r.1 = 0) (hmono : ∀ n ω, V n ω ≤ V (n + 1) ω)
    {Vp : VPkgXFamily.{u}} (hvar : ∀ n, (Vp Ω c r).slowVar l a n = slowStageVar h13 c r l a hA ch n)
    (hcov : ∀ᵐ ξ ∂c.P, ∀ᶠ n in atTop,
      (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) ≤ V n ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞)) :
    VStopExhaustsN Vp Ω c r l a :=
  vStopExhaustsN_of_vStopCoversN (vStopCoversN_slowStageVar h13 c r l a hA ch hroot hmono hvar hcov)

/-- **D3a's exhaust form on RELDET's monotone family** (root `0`, no named input). -/
theorem exists_slowStageVars_exhaust (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞)
      (hA : ∀ n, Supp8.Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)),
      ∀ (ch : ℕ → GW2Sdh.SchedChoice Ω) {Vp : VPkgXFamily.{u}},
        (∀ n, (Vp Ω c r).slowVar l a n = slowStageVar h13 c r l a hA ch n) →
        (∀ n, VDriverIdN Vp Ω c r l a n) ∧ VStopExhaustsN Vp Ω c r l a := by
  obtain ⟨R, V, hA, hmono, hfin, hev⟩ := exists_schedVersionsA_mono h13 c r l a
  refine ⟨R, V, hA, fun ch Vp hvar => ⟨fun n => vDriverIdN_slowStageVar h13 c r l a hA ch hroot hmono hfin n (hvar n),
    vStopExhaustsN_slowStageVar h13 c r l a hA ch hroot hmono hvar (ae_stopCovers_eventually h13 c r l a hroot hev)⟩⟩

/-- **The exhaust form for a capped family**: the stop `n` dominates `min (Vc n) (Dc n) − rootHistCap`, `Vc` covers
the gain eventually, and `Dc` exhausts it. -/
theorem vStopExhaustsN_of_capped {V : VPkgXFamily.{u}} {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {l : List (EntryIdx c.Θ c.Q)} {a : ℕ} {Vc Dc : ℕ → Ω → ℝ≥0∞}
    (hstop : ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ n,
      min (Vc n ξ) (Dc n ξ) - (rootHistCap c r l a ξ : ℝ≥0∞) ≤ ((V Ω c r).slowVar l a n).stop ξ)
    (hcov : ∀ᵐ ξ ∂c.P, ∀ᶠ n in atTop, (rootGain c r l a ξ : ℝ≥0∞) ≤ Vc n ξ - (rootHistCap c r l a ξ : ℝ≥0∞))
    (hD : ∀ᵐ ξ ∂c.P, ∀ u : ℝ≥0, u < rootGain c r l a ξ →
      ∀ᶠ n in atTop, ((rootHistCap c r l a ξ + u : ℝ≥0) : ℝ≥0∞) < Dc n ξ) :
    VStopExhaustsN V Ω c r l a := by
  filter_upwards [hstop, hcov, hD] with ξ hst hcv hDξ hG u hu
  filter_upwards [hcv, hDξ u hu] with n hn1 hn2
  have h1 : ((rootHistCap c r l a ξ + u : ℝ≥0) : ℝ≥0∞) < Vc n ξ := by
    have hlt : (u : ℝ≥0∞) < Vc n ξ - (rootHistCap c r l a ξ : ℝ≥0∞) := (ENNReal.coe_lt_coe.2 hu).trans_le hn1
    rw [ENNReal.coe_add]
    exact lt_tsub_iff_left.1 hlt
  have h2 : (u : ℝ≥0∞) < min (Vc n ξ) (Dc n ξ) - (rootHistCap c r l a ξ : ℝ≥0∞) := by
    rw [lt_tsub_iff_left, ← ENNReal.coe_add]
    exact lt_min h1 hn2
  exact h2.trans_le (hst hG n)

end InteractingSLE.Theorem14.GW2Bh
