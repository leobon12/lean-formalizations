/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SgkStop
import InteractingSLE.Spec.Supplement.GB6PastStep

/-!
# GW2's stage stop `σ_k`, part 3: from the launch datum

Packet PROVE-GW2-STAGEMEAN, σ round. **`exists_stop_of_datum`**: under any probability measure `μ` (in use: the
conditional law at a launch), for a centred counterflow `W_k` of the stage field with a coupling `hX`, and the
clauses of the launch datum `GW2TipSystem.HasLaunchPairEq` (`ζ_k = ⊤`, a continuous strictly increasing clock onto the
times before the first visit of the retained prefix `A`, the tip relation through the launch chart `c`), together with
the regularity
of the original counterflow `W'` under `μ`: for every original time `s` and cap `N`, a stopping time `σ` of the driving
filtration of `hX`, finite and `≤ N`, with `σ = t₀` almost surely whenever `ℓ(t₀) = s` and `t₀ < N`. The regularity of
`W_k` is Theorem 1.3 (`GW2Later.ae_counterflow_regular`). This is the stop `σ_k` consumed by
`GW2Stm.exists_unionMean_gw2_stop` (with `hσ`, `hσt`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Sgk

/-- **The stage stop from the clauses of the launch datum.** -/
theorem exists_stop_of_datum (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {h' : Ω → DistOn upperHalfPlaneOpens}
    {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ μ h' Wk ζk) {nL nR : ℕ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hX : IsMeasurableKilledDriving Wk VL VR ζk)
    {W' : ℝ≥0 → Ω → ℝ}
    (hW' : ∀ᵐ ω ∂μ, Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      ∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ')
    {c : Chart} (hc : GW1P.HasProperBdryExt c) {ℓ : Ω → ℝ≥0 → ℝ≥0} {A : Set ℂ}
    (hd : ∀ᵐ ω ∂μ, ζk ω = ⊤ ∧ Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧
      range (ℓ ω) = {t : ℝ≥0 | (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) A} ∧
      ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt (fun s => Wk s ω) r z ↔
        infinitySourceChart.tipAt (fun s => W' s ω) (ℓ ω r) z)
    (s N : ℝ≥0) :
    ∃ σ : Ω → WithTop ℝ≥0, IsStoppingTime (drivingFiltration μ hX) σ ∧ (∀ ω, σ ω ≠ ⊤) ∧
      (∀ ω, σ ω ≤ (N : WithTop ℝ≥0)) ∧
      ∀ᵐ ω ∂μ, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → t₀ < N → σ ω = (t₀ : WithTop ℝ≥0) := by
  have hζ : ∀ᵐ ω ∂μ, ζk ω = ⊤ := hd.mono fun _ h => h.1
  refine exists_stop_of_clock (W' := W') μ hX hc s N ?_
  filter_upwards [hd, hW', GW2Later.ae_counterflow_regular h13 hκ hcf hζ] with ω hdω hW'ω hreg
  obtain ⟨hζω, hℓc, hℓm, hℓr, hiff⟩ := hdω
  obtain ⟨γ, hγ, hWc, hW0, -⟩ := hreg
  exact ⟨hζω, hWc, hW0, ⟨γ, hγ⟩, hW'ω.1, hW'ω.2.1, hW'ω.2.2, hℓc, hℓm, clock_zero_of_range hℓm hℓr, hiff⟩

end InteractingSLE.Theorem14.GW2Sgk
