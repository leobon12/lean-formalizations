/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmLive
import InteractingSLE.Spec.Supplement.GW2PsmCapX

/-!
# GW2's open lines: the readings of ROOTX's good event

Packet PROVE-GW2-STAGEMEAN, R121 round.

* **`physGoodX_tip_marks`**: on ROOTX's good event the counterflow's tip at `s` is interior and the record's seed
  images are nondegenerate (`markPos > 0 > markPosL`);
* **`ae_noContact_root0`**: at the root `0`, below the version's cap at `T + t`, no explored point up to `T + t` is
  a counterflow point up to `s` (`α v · γ u + 1 ≠ 0`, the hypothesis of `GW2Psm.pair_root0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Psm

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.ReadD GW2TipSystem GW2Rz

/-- **The good event's tip and seed images.** -/
theorem physGoodX_tip_marks {Ω : Type*} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {w : ℝ≥0 → Ω → ℝ} {γ α : Ω → ℝ≥0 → ℂ} {ω : Ω} (hg : PhysGoodX x s W' ζ' w γ α ω) :
    α ω s ∈ H ∧ 0 < markPos (rdrv (cfRec s W' ζ' ω)) (rtime (cfRec s W' ζ' ω)) 0 ∧
      markPosL (rdrv (cfRec s W' ζ' ω)) (rtime (cfRec s W' ζ' ω)) 0 < 0 := by
  obtain ⟨-, -, -, hrec, hgood⟩ := hg
  obtain ⟨⟨-, htr, hpos, hneg⟩, -⟩ := hgood
  refine ⟨?_, hpos, hneg⟩
  rw [← hrec s le_rfl]
  exact htr

section Live

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGoodX 0 s Wα ζα W γ α ω) (hs₀ : 0 < s)

include hGT hs₀ in
/-- **No physical contact below the version's cap** (root `0`). -/
theorem ae_noContact_root0 (hver : IsRelVersionX 0 s P Wα ζα W γ α R V) :
    ∀ᵐ ω ∂P, ω ∈ GT → ∀ T : ℝ≥0, min (physClockX 0 s Wα ζα W GT T ω) (V ω) < V ω →
      ∀ v ∈ Icc 0 s, ∀ u ≤ T, α ω v * γ ω u + 1 ≠ 0 := by
  filter_upwards [ae_lt_contactX_all hGT hs₀ le_rfl hver] with ω hω hωG T hlt
  exact mul_add_one_ne_zero_of_lt_contactX (hω hωG T hlt)

end Live

end InteractingSLE.Theorem14.GW2Psm
