/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzIface
import InteractingSLE.Spec.Supplement.SB2XyRun

/-!
# Sample facts for the identification under the upper kernel

Packet PROVE-SB2-LCMEAN, round 15 (item 4). Deterministic facts at one sample used by the assembly:

* `continuousOn_lift_inv_of_normalized`: a normalized chart has a continuous lift on `ℍ` (read through its inverse);
* `isDriverCodeMatch_congr`: a driver agreeing with a matched one before the common lifetime (and at `0`) matches;
* **`isNormalized_launchChart`**: the chart of a launch of a run with regular launched pieces is normalized;
* **`isNormalized_walkStageChart`**: B's stage charts are normalized when B's launched pieces are regular.

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Mz

open Exist Exist.Staged Exist.StagedLaw Restart Sec2.Assembly

/-- A normalized chart has a continuous lift read through its inverse on `ℍ`. -/
theorem continuousOn_lift_inv_of_normalized {c : Chart} (hN : WalkIntCanon.IsNormalized c) :
    ContinuousOn (fun w => c.2.2 (c.2.1 w)) H := by
  obtain ⟨L, hL, hlift⟩ := hN.derivLift
  have hdom : (c.dom : Set ℂ) = c.2.1 '' H := hN.conformal.coe_dom
  have hc : ContinuousOn c.2.2 (c.dom : Set ℂ) :=
    ((Complex.continuous_im.comp_continuousOn hL.1.continuousOn).congr fun z hz => hlift z hz)
  refine hc.comp hN.conformal.1.continuousOn fun w hw => ?_
  rw [hdom]
  exact mem_image_of_mem _ hw

/-- **A driver agreeing with a matched one before the common lifetime, and at `0`, matches.** -/
theorem isDriverCodeMatch_congr {p : PCode × ℝ≥0∞} {W W' : ℝ≥0 → ℝ} {L L' : ℝ≥0∞}
    (h : IsDriverCodeMatch p W L) (hL : L' = L) (h0 : W' 0 = W 0)
    (hagree : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → W' t = W t) : IsDriverCodeMatch p W' L' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hL.trans h1, h0.trans h2, fun n k hk => ?_⟩
  rw [hL] at hk
  rw [hagree _ hk, h3 n k hk]

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The chart of a launch of a run with regular launched pieces is normalized.** -/
theorem isNormalized_launchChart (spec : ExplSpec) {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : SB.LuM.RegLaunches κ b jumps spec D) {k : ℕ} {c : Chart} {θ : ℝ}
    (hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ)) : WalkIntCanon.IsNormalized c := by
  rw [(eq_launch_of_launches spec D hl).2.2]
  exact WalkIntCanon.isNormalized_runChart spec D k fun j _ c' θ' hl' => hreg j c' θ' hl'

/-- **B's stage charts are normalized** when B's launched pieces are regular. -/
theorem isNormalized_walkStageChart {Ω' : Type*} {E : ExplSpec → ℕ → Ω' → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω'}
    (hreg : SB.LuM.RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) (ℓ : ℕ) :
    WalkIntCanon.IsNormalized (Mn.walkStageChart κ b jumps E ℓ ω) :=
  WalkIntCanon.isNormalized_runChart _ _ ℓ fun j _ c' θ' hl' => hreg j c' θ' hl'

end InteractingSLE.Theorem14.SB.Mz
