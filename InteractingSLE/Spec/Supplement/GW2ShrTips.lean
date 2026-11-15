/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SgkDatum

/-!
# GW2's stage stop `σ_k`, part 4: the stage's retained points are the original ones

Packet PROVE-GW2-STAGEMEAN, hull-reading round. The stage stop `σ_k` (`GW2Sgk.exists_stop_of_datum`) is the own time
of the conditional counterflow `W_k` at which the original counterflow `W'` reaches its fixed time `s`. At the level of
physical points (`Chart.tipSet`, the notion of GW2's retained sets `GW2TipSystem.contactSet`, `SB.prefixPhysSet`):

* **`tipSet_eq_of_clock`** (deterministic): if the tips of `W_k` through the launch chart `c` and the inversion are
  the tips of `W'` at the clock times `ℓ r` (`ℓ` continuous, increasing, `ℓ 0 = 0`) and `ℓ t₀ = s`, the physical
  points of `W_k` on `[0, t₀]` read through `c` are exactly the physical points of `W'` on `[0, s]`;
* **`exists_stop_tipSet_of_datum`**: the stop of `exists_stop_of_datum` carries, almost surely whenever the clock
  reaches `s` before the cap, the identity of the stage's retained physical points with the original counterflow's
  points up to `s`.

The identity of the FILLED retained hulls (`Q3Rel.invHull`) through the launch chart is `GW2ShrFill`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Shr

/-- **The physical points of the conditional counterflow up to `t₀`, read through the launch chart, are the
original counterflow's points up to `ℓ t₀`.** -/
theorem tipSet_eq_of_clock {c : Chart} {Wk W' : ℝ≥0 → ℝ} {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : Monotone ℓ)
    (hℓ0 : ℓ 0 = 0)
    (hiff : ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt Wk r z ↔
      infinitySourceChart.tipAt W' (ℓ r) z) {t₀ s : ℝ≥0} (ht₀ : ℓ t₀ = s) :
    (c.trans infinitySourceChart).tipSet Wk (t₀ : ℝ≥0∞) = infinitySourceChart.tipSet W' (s : ℝ≥0∞) := by
  rw [Chart.tipSet_eq_tipAt, Chart.tipSet_eq_tipAt]
  ext z
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨r, hr, htip⟩
    refine ⟨ℓ r, ?_, (hiff r z).1 htip⟩
    rw [← ht₀]
    exact ENNReal.coe_le_coe.2 (hℓm (ENNReal.coe_le_coe.1 hr))
  · rintro ⟨t, ht, htip⟩
    have hts : t ≤ ℓ t₀ := by rw [ht₀]; exact ENNReal.coe_le_coe.1 ht
    obtain ⟨r, hr, hrt⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t₀) hℓc.continuousOn
      (show t ∈ Icc (ℓ 0) (ℓ t₀) from ⟨by rw [hℓ0]; exact zero_le, hts⟩)
    refine ⟨r, ENNReal.coe_le_coe.2 hr.2, (hiff r z).2 ?_⟩
    rw [hrt]
    exact htip

/-- **The stage stop with the identity of the retained physical points.** -/
theorem exists_stop_tipSet_of_datum (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {Ω : Type u}
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
      ∀ᵐ ω ∂μ, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → t₀ < N → σ ω = (t₀ : WithTop ℝ≥0) ∧
        (c.trans infinitySourceChart).tipSet (fun t => Wk t ω) (σ ω : ℝ≥0∞) =
          infinitySourceChart.tipSet (fun t => W' t ω) (s : ℝ≥0∞) := by
  obtain ⟨σ, hσ, hσt, hσN, hσeq⟩ := GW2Sgk.exists_stop_of_datum h13 hκ μ hcf hX hW' hc hd s N
  refine ⟨σ, hσ, hσt, hσN, ?_⟩
  filter_upwards [hσeq, hd] with ω hω hdω t₀ ht₀ htN
  obtain ⟨-, hℓc, hℓm, hℓr, hiff⟩ := hdω
  have he := hω t₀ ht₀ htN
  refine ⟨he, ?_⟩
  rw [he]
  exact tipSet_eq_of_clock hℓc hℓm.monotone (GW2Sgk.clock_zero_of_range hℓm hℓr) hiff ht₀

end InteractingSLE.Theorem14.GW2Shr
