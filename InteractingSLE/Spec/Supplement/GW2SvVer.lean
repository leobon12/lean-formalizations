/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdVer

/-!
# GW2's stage identity: announced GB6 versions for ANY explored curve with ANY cap gauge

Packet PROVE-GW2-RELDET, ruling R106. At a stage the version must be capped at the end of the current piece (its own
time `Δ_n` or its death), not at the lifetime of one flow line. Stage `0` (`GW2Rd.gw2RdVersionStatement_of_lifetime`)
combined five things:
* GB6's relative coordinates (`SourceC.exists_relative_driver`);
* the live readout without `κ < 4` (`GW2Rd.hasLiveReadout_nr`);
* one cap gauge, detecting the flow line's continuation threshold;
* the capped readout (`GW2Rd.exists_capReadout`);
* the capped announced versions (`GW2Rd.isGB6RelVersionA_capCoord`).

Only the cap gauge is specific to the explored curve. This file isolates the rest:

**`exists_versionsA_of_capGauge`**. Inputs:
* the retained curve: a flow-line driver with a generating trace and no return;
* the explored curve: measurable, almost surely continuous from `0`, with a transient generating trace on `[0, ∞)`
  (for a schedule: the joined canonical pieces, extended after the program end);
* a measurable, causal, nonnegative cap gauge `Gζ` with a life `Lζ`. Along EVERY relative coordinate process it must
  be, on the record event, continuous before the coordinates' life, positive before `Lζ` and zero at `Lζ`.

Outputs: announced R-form versions `(R m, V m)` whose stops stay below `Lζ`. Every relative clock value before the first
contact and below `Lζ` is below some stop (exhaustion). Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId Supp8.GB6.SourceC

/-- **Announced capped versions of GB6's relative exploration, for any explored curve and any cap gauge.** -/
theorem exists_versionsA_of_capGauge {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω → ℝ}
    {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hWm : ∀ t, Measurable (W t))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) (hs : 0 < s)
    {Gζ : GaugeReadout} (hGζm : ∀ t, Measurable (Gζ t)) (hGζc : IsCausal Gζ) (hGζ0 : ∀ t p, 0 ≤ Gζ t p)
    {Lζ : Ω → ℝ≥0∞}
    (hζ : ∀ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞), RelativeDriverCoordinates s P W Wα ζα γ α D L →
      ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → 0 < Lζ ω ∧
        ContinuousOn (fun t => Gζ t (gb6Rec s Wα ζα ω, fun u => D u ω)) {t | (t : ℝ≥0∞) < L ω} ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) < Lζ ω → 0 < Gζ t (gb6Rec s Wα ζα ω, fun u => D u ω)) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) = Lζ ω → Gζ t (gb6Rec s Wα ζα ω, fun u => D u ω) = 0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R m) (V m)) ∧
      (∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → ∀ m, V m ω < Lζ ω) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        ENNReal.ofReal (gb6Clock s W Wα ω t) < Lζ ω → ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω := by
  have hrecm : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hF s).2
  have hgoodrec := ae_gb6RecGood hF hα s
  have hW' : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) :=
    hW.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  -- relative coordinates
  obtain ⟨_, 𝓕α, _, _, _, _, hCα⟩ := id hF
  have hWa : AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) (fun _ => (⊤ : ℝ≥0∞)) W := by
    intro t A hA
    have e : {ω | (t : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) ω ∧ W t ω ∈ A} = W t ⁻¹' A := by
      ext ω
      simp only [mem_ofPred_eq, ENNReal.coe_lt_top, true_and, mem_preimage]
    rw [e]
    exact (hWm t) hA
  have hcfE : ∀ᵐ ω ∂P, (fun _ : Ω => (⊤ : ℝ≥0∞)) ω = ⊤ ∧ W 0 ω = 0 ∧ Continuous (W · ω) ∧
      IsGeneratingTrace (W · ω) ⊤ (γ ω) := hW'.mono fun _ h => ⟨rfl, h.2.1, h.1, h.2.2⟩
  have hflE : ∀ᵐ ω ∂P, Wα 0 ω = 0 ∧ ContinuousOn (Wα · ω) {t | (t : ℝ≥0∞) < ζα ω} ∧
      IsGeneratingTrace (Wα · ω) (ζα ω) (α ω) := by
    filter_upwards [Supp8.GB6.ae_driver_zero_continuousOn hF, hα] with ω hr ht using ⟨hr.1, hr.2, ht⟩
  obtain ⟨D, L, hC⟩ := SourceC.exists_relative_driver (P := P) hWa hCα.1.2.1 hcfE hflE s hs
  -- the live readout and the cap
  have hLive := hasLiveReadout_nr hF hα hNR hW s hs hC
  obtain ⟨D', L', Lg, g, G', hC', hrd, hle, -, hLg⟩ := exists_capReadout hC hrecm hgoodrec hLive hGζm hGζc hGζ0
    (hζ D L hC)
  refine ⟨fun m => coordDriver (D := D') (g := g) m, fun m ω => (coordStop (g := g) m ω : ℝ≥0∞),
    fun m => isGB6RelVersionA_capCoord hC' hrd hle m, ?_, ?_⟩
  · -- the cap
    filter_upwards [hLg] with ω hω hm m
    exact (coordStop_lt_cap hrd m ω).trans_le ((hω hm).le.trans (min_le_right _ _))
  · -- exhaustion below the cap before the first contact
    filter_upwards [hLg, hgoodrec, hC.relative] with ω hLgω hg hrel hs' hsH t ht htζ
    have hm : gb6Rec s Wα ζα ω ∈ gb6TS s := (mem_gb6TS_iff hg).1 ⟨hs', hsH⟩
    obtain ⟨-, hK⟩ := hrel hs' hsH
    obtain ⟨-, hlt, -⟩ := hK t ht
    have h1 : ENNReal.ofReal (gb6Clock s W Wα ω t) < Lg ω := by
      rw [hLgω hm]
      exact lt_min hlt htζ
    exact exists_lt_coordStop_cap hrd h1

end InteractingSLE.Theorem14.GW2Rd
