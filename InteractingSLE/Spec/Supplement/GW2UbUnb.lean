/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NcRel

/-!
# A first contact at the tip with a bounded relative clock has an unbounded relative driver (statement)

Packet PROVE-GW2-RELDET (round 38, decisions D73 route (ii) and D81). At a first contact at the counterflow's tip the
relative trace tends to `∞` (the relative chart sends the tip to `∞`). If the relative clock is unbounded before the
contact, NEARIMG2's `GW2Ni.aliveRead_stgDrv_cDrv` and RELDET's `BadCode` exclude it. If the clock stays bounded, the
hulls of the glued relative driver `GW2Ni.cDrv` below the relative life are unbounded, so the driver is unbounded
there (a bounded driver on a finite time interval generates bounded hulls); RELDET's `BadFin` excludes that.

* **`TipUnbStatement`** (deterministic, one sample, in the setting of `GW2Rd.CanonContactStatement`): at a first
  contact at the tip with a bounded relative clock, `cDrv` is unbounded below the relative life. Proposed for
  PROVE-GW2-NEARIMG2 (the relative-chart limits at the contact are its `GW2Nc*` / `GW2NcLim`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart Supp8.GB6 GW2TipSystem GW2Rz

/-- **At a first contact at the tip with a bounded relative clock, the glued relative driver is unbounded below the
relative life** (one sample). -/
def TipUnbStatement : Prop :=
  ∀ {Ω : Type u} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) {α : ℝ≥0 → ℂ},
    IsGeneratingTrace (W · ω) ⊤ α → Continuous (W · ω) → W 0 ω = 0 → ζ ω = ⊤ →
    ∀ {s : ℝ≥0}, 0 < s → ∀ {x : ℝ}, 0 ≤ x → (∀ u ∈ Icc 0 s, x * ‖α u‖ < 1) →
    ∀ {w : ℝ≥0 → ℝ}, Continuous w → w 0 = 0 → ∀ {γ : ℝ≥0 → ℂ}, IsGeneratingTrace w ⊤ γ → α s ≠ 0 →
    ∀ τ : ℝ≥0, firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = (τ : ℝ≥0∞) →
    sphereInv (((x : ℂ) + γ τ : ℂ) : OnePoint ℂ) = ((α s : ℂ) : OnePoint ℂ) →
    (∃ M : ℝ, ∀ v : ℝ≥0, v < τ → GW2Ni.gClk x s (cfRec s W ζ ω) w v ≤ M) →
    ∀ B : ℝ, ∃ (u v : ℝ≥0), v < τ ∧ (u : ℝ) < GW2Ni.gClk x s (cfRec s W ζ ω) w v ∧
      B < |GW2Ni.cDrv x s (cfRec s W ζ ω) w τ u|

end InteractingSLE.Theorem14.GW2Rd
