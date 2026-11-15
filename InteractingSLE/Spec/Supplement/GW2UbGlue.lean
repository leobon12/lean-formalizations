/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UbTip
import InteractingSLE.Spec.Supplement.GW2NjStage

/-!
# Every version is the glued relative driver of the contact

Packet PROVE-GW2-RELDET (round 38, decisions D73 route (ii) and D81). NEARIMG2's counterflow-side statement
(`GW2Ni.aliveRead_stgDrv_cDrv`) is about the stage driver `stgDrv (cDrv …) a₀` of NEARIMG2's glued relative driver of
the contact, `GW2Ni.cDrv`. This file identifies the versions with it (one sample of the good set, contact `τ`):

* **`version_eq_cDrv`**: a version is `cDrv` at every relative time up to its cap that lies below the clock of a
  horizon before the contact (both are J31's reader of that horizon: `GW2Rz.version_eq_reader`,
  `GW2Ni.cDrv_eq_read`);
* **`drvX_eq_stgDrv_cDrv`**: when the relative clock is unbounded before the contact, the stage driver of a version
  is `stgDrv cDrv a₀` below its stage cap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rv GW2Sde

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **A version is the glued relative driver of the contact** at every relative time up to its cap that lies below
the clock of a horizon before the contact (one sample). -/
theorem version_eq_cDrv (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    {GT : Set Ω} (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ξ : Ω} (hξ : ξ ∈ GT)
    (hR : VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V ξ) {τ : ℝ≥0}
    (hτ : contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ = τ) {u : ℝ≥0} (huV : (u : ℝ≥0∞) ≤ V ξ)
    {v : ℝ≥0} (hvτ : v < τ) (hu : (u : ℝ) < clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ) :
    R u ξ = GW2Ni.cDrv (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (fun t => schedW c r l a t ξ) τ u := by
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ξ hξ
  have hv0 : 0 < v := GW2Ni.pos_of_lt_gClk c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc hw0 hγ hτ hu
  have hvc : (v : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ := by
    rw [hτ]
    exact_mod_cast hvτ
  rw [version_eq_reader hGT hs hx hξ hR hv0 hvc hu huV]
  exact (GW2Ni.cDrv_eq_read c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc hw0 hγ hτ hvτ hu).symm

/-- **The stage driver of a version is the stage driver of `cDrv`** below the stage cap, when the relative clock is
unbounded before the contact (one sample). -/
theorem drvX_eq_stgDrv_cDrv (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    {GT : Set Ω} (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ξ : Ω} (hξ : ξ ∈ GT)
    (hR : VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V ξ) {τ : ℝ≥0}
    (hτ : contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ = τ)
    (hunb : ∀ y : ℝ, ∃ v : ℝ≥0, v < τ ∧ y < clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < stgVX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (RootJ31.historyTime c r l) ξ) :
    stgRX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT R V (RootJ31.historyTime c r l) u ξ =
      stgDrv (GW2Ni.cDrv (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (fun t => schedW c r l a t ξ) τ)
        (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (RootJ31.historyTime c r l) ξ) u := by
  set a₀ := stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (RootJ31.historyTime c r l) ξ with ha₀
  have hlt : ((a₀ + u : ℝ≥0) : ℝ≥0∞) < V ξ := by
    have h := lt_tsub_iff_left.1 hu
    rw [← ENNReal.coe_add] at h
    exact h
  have hle0 : ((a₀ : ℝ≥0) : ℝ≥0∞) ≤ V ξ := le_trans (ENNReal.coe_le_coe.2 le_self_add) hlt.le
  obtain ⟨v₁, hv₁, h₁⟩ := hunb ((a₀ + u : ℝ≥0) : ℝ)
  obtain ⟨v₂, hv₂, h₂⟩ := hunb (a₀ : ℝ)
  show R (a₀ + u) ξ - R a₀ ξ = _
  rw [version_eq_cDrv c r l a hGT hs hx hξ hR hτ hlt.le hv₁ h₁, version_eq_cDrv c r l a hGT hs hx hξ hR hτ hle0 hv₂ h₂]
  rfl

end InteractingSLE.Theorem14.GW2Rd
