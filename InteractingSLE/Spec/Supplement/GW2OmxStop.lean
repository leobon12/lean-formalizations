/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SgkDatum

/-!
# GW2's open lines: the stage stop `σ_k`, with its converse

Packet PROVE-GW2-STAGEMEAN, R120 round (localization). The stop `σ = min (capStop …) N` of
`GW2Sgk.exists_stop_of_datum` is `t₀` when the clock reaches the retained time at `t₀ < N`. The localization event
`{σ < N}` needs the converse: before the cap, the stop is a time at which the clock has passed `s`.

* **`exists_stop_of_datum_ext`**: the conclusion of `GW2Sgk.exists_stop_of_datum` (same construction, proof re-run)
  together with `σ < N ⇒ ∃ q, s < ℓ q` (the capacity read of the original hull is `2ℓ`, `GW2Sgk.capRead_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open GW2Sgk

/-- **The stage stop with its converse.** -/
theorem exists_stop_of_datum_ext (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {Ω : Type u}
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
      (∀ᵐ ω ∂μ, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → t₀ < N → σ ω = (t₀ : WithTop ℝ≥0)) ∧
      ∀ᵐ ω ∂μ, σ ω < (N : WithTop ℝ≥0) → ∃ q : ℝ≥0, s < ℓ ω q := by
  classical
  have hζ : ∀ᵐ ω ∂μ, ζk ω = ⊤ := hd.mono fun _ h => h.1
  have hae : ∀ᵐ ω ∂μ, ζk ω = ⊤ ∧ Continuous (fun t => Wk t ω) ∧ Wk 0 ω = 0 ∧
      (∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wk t ω) ⊤ γ) ∧
      Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧ (∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ') ∧
      Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧ ℓ ω 0 = 0 ∧
      ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt (fun t => Wk t ω) r z ↔
        infinitySourceChart.tipAt (fun t => W' t ω) (ℓ ω r) z := by
    filter_upwards [hd, hW', GW2Later.ae_counterflow_regular h13 hκ hcf hζ] with ω hdω hW'ω hreg
    obtain ⟨hζω, hℓc, hℓm, hℓr, hiff⟩ := hdω
    obtain ⟨γ, hγ, hWc, hW0, -⟩ := hreg
    exact ⟨hζω, hWc, hW0, ⟨γ, hγ⟩, hW'ω.1, hW'ω.2.1, hW'ω.2.2, hℓc, hℓm, clock_zero_of_range hℓm hℓr, hiff⟩
  obtain ⟨f, C, hf, hC⟩ := hc
  have hfc : ContinuousOn f Hbar := GW1P.continuousOn_of_tendsto hf
  refine ⟨fun ω => min (capStop f s Wk ζk ω) (N : ℝ≥0∞), isStoppingTime_capStop hfc μ hX s N,
    fun ω => ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _), fun ω => min_le_right _ _, ?_, ?_⟩
  · filter_upwards [hae] with ω hω t₀ ht₀ htN
    obtain ⟨hζω, hw, hw0, ⟨γ, hγ⟩, hw', hw'0, ⟨γ', hγ'⟩, hℓc, hℓm, hℓ0, hiff⟩ := hω
    have h1 := capStop_eq hf hC hζω hγ hw hw0 hγ' hw' hw'0 hℓc hℓm hℓ0 hiff ht₀
    show min (capStop f s Wk ζk ω) (N : ℝ≥0∞) = (t₀ : ℝ≥0∞)
    rw [h1]
    exact min_eq_left (ENNReal.coe_le_coe.2 htN.le)
  · filter_upwards [hae] with ω hω hσ
    obtain ⟨hζω, hw, hw0, ⟨γ, hγ⟩, hw', hw'0, ⟨γ', hγ'⟩, hℓc, hℓm, hℓ0, hiff⟩ := hω
    have hlt : capStop f s Wk ζk ω < ⊤ := by
      have h1 : min (capStop f s Wk ζk ω) (N : ℝ≥0∞) < (N : ℝ≥0∞) := hσ
      rcases lt_or_ge (capStop f s Wk ζk ω) (N : ℝ≥0∞) with h | h
      · exact h.trans ENNReal.coe_lt_top
      · rw [min_eq_right h] at h1
        exact absurd h1 (lt_irrefl _)
    unfold capStop at hlt
    obtain ⟨q, hq⟩ := iInf_lt_iff.1 hlt
    by_cases hcond : 0 ≤ q ∧ 2 * (s : ℝ≥0∞) < capRead f (q : ℝ).toNNReal (killedPath Wk ζk ω)
    · refine ⟨(q : ℝ).toNNReal, ?_⟩
      have hkill : killedPath Wk ζk ω = fun t => Wk t ω := funext fun r => by
        simp only [killedPath, hζω, ENNReal.coe_lt_top, ↓reduceIte]
      have hcap := capRead_eq hf hC hγ hw hw0 hγ' hw' hw'0 hℓc hℓm.monotone hℓ0 hiff (q : ℝ).toNNReal
      have h2 := hcond.2
      rw [hkill, hcap, show (2 : ℝ≥0∞) * (s : ℝ≥0∞) = ((2 * s : ℝ≥0) : ℝ≥0∞) by push_cast; ring,
        show (2 : ℝ≥0∞) * (ℓ ω (q : ℝ).toNNReal : ℝ≥0∞) = ((2 * ℓ ω (q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) by
          push_cast; ring, ENNReal.coe_lt_coe] at h2
      exact lt_of_mul_lt_mul_left h2 zero_le
    · simp only [hcond, ↓reduceIte] at hq
      exact absurd hq (lt_irrefl _)

end InteractingSLE.Theorem14.GW2Omx
