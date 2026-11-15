/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BsDeath

/-!
# The cell exit fires strictly before the stage life (one sample)

Packet PROVE-GW2-BUF (round 16; steps B and C at one sample). At one sample:
* the near family at index `m` presents the raised base word `upW (θ χ) base` (SDE's `nearSelS_spec`);
* the record carries the family's shape and labels (D16's decoder) and the cell contains the initial state;
* the base word's jumps lie under the flowed root bounds of the canonical relative driver `Wc` at the stage start `S`
  (step A, `stageWord_jump_le`/`_ge`);
* the contact clause holds at the relative life `L` (the stage law, `GapVanishes`);
* at a death clock `d < L` the stage word has a continuation threshold along the stage path at `d − S` (the death
  input: `ζ = T_*`, read in the stage chart).

Then the cell exit on the stage path `stgDrv Wc S` fires strictly before `min (L, d) − S`:

* **`cellStop_add_lt_life`**: `exit + S < min (ofReal L) d`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist.StagedLaw MartChar.RealFlow Sec5.CrossCond.StagedRepLater GW2TipSystem
  GW2TipSystem.RootN4 GW2JDetR11 Supp12.DSReach

section Cell

variable {κ : ℝ} (f : NearCrossingFamily.{u} κ) (cell : RecData → NearCell) (posL posR : RecData → ℕ → ℝ)
  {y : RecData}

/-- **The cell exit fires strictly before the stage life.** -/
theorem cellStop_add_lt_life (hsh : famShapeB f = (cell y).1) (hL : ∀ i : Fin f.nL, f.xL i = posL y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posR y j) {base : BoundaryWord} {θ : ℝ} {scale c : ℝ≥0} (hc : 0 < c)
    (hsc : Real.sqrt scale = (c : ℝ)⁻¹) (flip : Bool) (m : ℕ)
    (hP : GW2Sdf.PresentsO κ (GW2Rd.upW (θ * chiC κ) base) scale flip f.xL (f.ρLs m) f.xR (f.ρRs m))
    (hmL : f.mL ≤ f.nL - 1) (hmR : f.mR ≤ f.nR - 1) {cap : ℝ≥0} (hcap : 0 < cap)
    {Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) (S : ℝ≥0)
    (h0 : GW2Sdg.imgState f.xL f.xR (scaledPath (c ^ 2) (GW2Sdy.nearSign flip * c) (GW2Rd.stgDrv Wc S)) 0 ∈
      cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2))
    {xR xL : ℝ} (hjR : ∀ z ∈ base.jumps, 0 < z → z ≤ rightImg (rp Wc) xR S - rp Wc S)
    (hjL : ∀ z ∈ base.jumps, z < 0 → -rightImg (fun v => -rp Wc v) (-xL) S - rp Wc S ≤ z) {L : ℝ}
    (hSL : (S : ℝ) < L)
    (hcon : (∀ δ : ℝ, 0 < δ → ∃ t : ℝ, (S : ℝ) < t ∧ t < L ∧ rightImg (rp Wc) xR t - rp Wc t < δ) ∨
      ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, (S : ℝ) < t ∧ t < L ∧
        rightImg (fun v => -rp Wc v) (-xL) t - -rp Wc t < δ)
    {d : ℝ≥0∞}
    (hdeath : d < ENNReal.ofReal L → ∃ u : ℝ≥0, (S : ℝ≥0∞) + u = d ∧
      ForceWord.ThresholdCondition
        (flowLineRhoL κ (GW2Rd.upW (θ * chiC κ) base).fn (GW2Rd.upW (θ * chiC κ) base).jumps 0 0)
        (flowLineRhoR κ (GW2Rd.upW (θ * chiC κ) base).fn (GW2Rd.upW (θ * chiC κ) base).jumps 0 0)
        (GW2Rd.stgDrv Wc S u)
        (fun i => -rightImg (fun v : ℝ => -GW2Rd.stgDrv Wc S v.toNNReal)
          (-flowLineXL (GW2Rd.upW (θ * chiC κ) base).fn (GW2Rd.upW (θ * chiC κ) base).jumps 0 i) u)
        (fun j => rightImg (fun v : ℝ => GW2Rd.stgDrv Wc S v.toNNReal)
          (flowLineXR (GW2Rd.upW (θ * chiC κ) base).fn (GW2Rd.upW (θ * chiC κ) base).jumps 0 j) u)) :
    cellStop cell posL posR (c ^ 2) (GW2Sdy.nearSign flip * c) cap (y, GW2Rd.stgDrv Wc S) + S <
      min (ENNReal.ofReal L) d := by
  set E := cellStop cell posL posR (c ^ 2) (GW2Sdy.nearSign flip * c) cap (y, GW2Rd.stgDrv Wc S) with hEdef
  have hjR' : ∀ z ∈ (GW2Rd.upW (θ * chiC κ) base).jumps, 0 < z → z ≤ rightImg (rp Wc) xR S - rp Wc S := hjR
  have hjL' : ∀ z ∈ (GW2Rd.upW (θ * chiC κ) base).jumps, z < 0 →
      -rightImg (fun v => -rp Wc v) (-xL) S - rp Wc S ≤ z := hjL
  have hcont : E < ENNReal.ofReal (L - S) :=
    cellStop_lt_of_contact f cell posL posR hsh hL hR hc hsc flip m hP hmL hmR hcap hWc S h0 hjR' hjL' hcon
  have hE : E ≠ ⊤ := ne_top_of_lt hcont
  -- exit before the contact
  have h1 : E + S < ENNReal.ofReal L := by
    have hL' : ENNReal.ofReal L = ENNReal.ofReal (L - S) + (S : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (by linarith) S.coe_nonneg]
      congr 1
      ring
    rw [hL']
    exact ENNReal.add_lt_add_right ENNReal.coe_ne_top hcont
  rcases lt_or_ge d (ENNReal.ofReal L) with hdL | hdL
  · obtain ⟨u, hu, hthr⟩ := hdeath hdL
    have hlt : E < u := cellStop_lt_of_stage_threshold f cell posL posR hsh hL hR hc hsc flip m hP hcap
      (GW2Rd.continuous_stgDrv hWc S) h0 u hthr
    rw [min_eq_right hdL.le, ← hu, add_comm (S : ℝ≥0∞)]
    exact ENNReal.add_lt_add_right ENNReal.coe_ne_top hlt
  · rw [min_eq_left hdL]
    exact h1

end Cell

end InteractingSLE.Theorem14.GW2Bh
