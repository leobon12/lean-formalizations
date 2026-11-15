/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopProcFstMain
import InteractingSLE.Spec.Supplement.AStopProcEndsMain

/-!
# Items 2–3 of `AStopSourceInputs` for both continuations (wiring)

Packet PROVE-T15-ASTOP-PROC. For a stop-line event `M` of ordinary pairs (almost surely), in the settings of
`RLC.OrdModel.RetOrdAStopSourceSndStatement` and `RLC.RetOrdAStopSourceFstSeedStatement`:

* **`exists_sndProcInputs`** (second continuation) and **`exists_fstProcInputs`** (first continuation at a stop-line
  measurable seed `τ`, `τ = tipPos` almost surely at ordinary pairs — the source's `(β ω).2`): a stop-line sub-event
  `M' ⊆ M` almost surely equal to `M`, and on it a filtration `𝓗` with `retSigma76 … d.u d.r ≤ 𝓗 0`, a driver `W`, end
  points `E`, a stop `V'` and a trace `γ'` with **every conjunct of items 2–3 of `AStopSourceInputs`** in its exact
  form (`W` continuous from `0` and `𝓗`-adapted; `V'` an `𝓗`-stopping time; `γ'` measurable, continuous on
  `[0, V']`, `0` at `0`; `E` `𝓗 0`-measurable; `V' = V` and `γ' = γ` on `[0, V]` almost surely on `M'` for the source
  statement's canonical `V`, `γ`), plus the generation `W ↦ γ'` (item 6's first conjunct), the identification
  `aStopSet (E ω) = I_A` (the chart reals over the retained union; item 3), and the explicit form of `𝓗`, `V'`, `γ'`,
  `W` (for items 4–6).

Replacing each event of the type partition by its good sub-event `M'` keeps the partition a measurable cover of the
ordinary pairs almost surely; every other conjunct of `AStopSourceInputs` is then to be proved on `M'` for these
objects. Lemma 7.5 (`Theorem15.Lemma75Statement`) is used for the capped history readers (as in RETPLUMB).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopProc

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F LocalSets OrdModel
open LQGMetric (DistOn)

universe v

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type v} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞} {d : RetData Ω}

/-- **Items 2–3 of `AStopSourceInputs` for the A-stopped second continuation** (see the module docstring). -/
theorem exists_sndProcInputs (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) :
    ∃ M' ⊆ M, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M' ∧ (∀ᵐ ω ∂P, ω ∈ M → ω ∈ M') ∧
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (E : Ω → Ends) (V' : Ω → ℝ≥0∞) (γ' : Ω → ℝ≥0 → ℂ),
      retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r ≤ 𝓗 0 ∧
      (∀ ω, Continuous (W · ω)) ∧ (∀ ω, W 0 ω = 0) ∧ StronglyAdapted 𝓗 W ∧
      (∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V' ω ≤ t}) ∧
      (∀ t, Measurable fun ω => γ' ω t) ∧ (∀ ω, ContinuousOn (γ' ω) {t | (t : ℝ≥0∞) ≤ V' ω}) ∧
      (∀ ω, γ' ω 0 = 0) ∧ Measurable[𝓗 0] E ∧
      (∀ᵐ ω ∂P, ω ∈ M' →
        V' ω = canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 →
          γ' ω t = canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 t) ∧
      (∀ᵐ ω ∂P, ω ∈ M' → IsGeneratingTrace (W · ω) (V' ω) (γ' ω)) ∧
      (∀ᵐ ω ∂P, ω ∈ M' →
        aStopSet (E ω) = {z : ℂ | z.im = 0 ∧ d.inv ω z ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r}) ∧
      ∃ η₂' : Ω → ℝ≥0 → ℂ, (∀ ω ∈ M', IsSndGood d η₁ η₂ η₂' ζ₁ ζ₂ x₂ ω) ∧
        (∃ hQa, 𝓗 = aFilt (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M' (sndChart d η₂' ζ₂) hQa) ∧
        V' = M'.indicator (aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂)) ∧
        γ' = aTrace M' (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ∧
        ∀ ω (q : ℝ≥0), (q : ℝ≥0∞) < V' ω → W q ω = aDriver (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) q ω := by
  obtain ⟨η₂', hm₂, ha₂⟩ := exists_measurable_version_of_isFlowLine hη₂
  obtain ⟨M', hM'M, hM', hMM', hMg⟩ := exists_subset_isSndGood hκ hκ4 hη₂ hd hag ha₂ (x₂ := x₂) hM hMord
  obtain ⟨E, hEm, hE⟩ := exists_retEnds_stop hL75 hκ hκ4 hb hx hh hη₁ hη₂ hd hag
  obtain ⟨𝓗, W, V', γ', h0, hWc, hW0, hWa, hV, hγm, hγc, hγ0, hcan, hgen, h𝓗, hV', hγ', hWe⟩ :=
    exists_sndProc hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hm₂ ha₂ hM' hMg
  have hMord' : ∀ᵐ ω ∂P, ω ∈ M' → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r := by
    filter_upwards [hMord] with ω hω hω' using hω (hM'M hω')
  refine ⟨M', hM'M, hM', hMM', 𝓗, W, E, V', γ', h0, hWc, hW0, hWa, hV, hγm, hγc, hγ0,
    hEm.mono h0 le_rfl, Eventually.of_forall fun ω hω => ?_, Eventually.of_forall hgen, ?_, η₂', hMg, h𝓗, hV',
    hγ', hWe⟩
  · obtain ⟨hl, hp⟩ := hcan ω hω
    exact ⟨hl, fun t ht => hp t ht⟩
  · filter_upwards [hE, hMord'] with ω hω hord hω'
    exact hω (hord hω')

/-- **Items 2–3 of `AStopSourceInputs` for the A-stopped first continuation at its seed** (see the module docstring;
the source's seed is `τ = (β ω).2`). -/
theorem exists_fstProcInputs (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {τ : Ω → ℝ} (hτm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] τ)
    (hτ : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → τ ω = tipPos d η₁ ω)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) :
    ∃ M' ⊆ M, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M' ∧ (∀ᵐ ω ∂P, ω ∈ M → ω ∈ M') ∧
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (E : Ω → Ends) (V' : Ω → ℝ≥0∞) (γ' : Ω → ℝ≥0 → ℂ),
      retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r ≤ 𝓗 0 ∧
      (∀ ω, Continuous (W · ω)) ∧ (∀ ω, W 0 ω = 0) ∧ StronglyAdapted 𝓗 W ∧
      (∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V' ω ≤ t}) ∧
      (∀ t, Measurable fun ω => γ' ω t) ∧ (∀ ω, ContinuousOn (γ' ω) {t | (t : ℝ≥0∞) ≤ V' ω}) ∧
      (∀ ω, γ' ω 0 = 0) ∧ Measurable[𝓗 0] E ∧ Measurable[𝓗 0] τ ∧
      (∀ᵐ ω ∂P, ω ∈ M' →
        V' ω = canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) →
          γ' ω t = canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
            (tipPos d η₁ ω) t - τ ω) ∧
      (∀ᵐ ω ∂P, ω ∈ M' → IsGeneratingTrace (W · ω) (V' ω) (γ' ω)) ∧
      (∀ᵐ ω ∂P, ω ∈ M' →
        aStopSet (E ω) = {z : ℂ | z.im = 0 ∧ d.inv ω (z + τ ω) ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r}) ∧
      ∃ η₁' : Ω → ℝ≥0 → ℂ, (∀ ω ∈ M', IsFstGood d η₁ η₂ η₁' ζ₁ ζ₂ x₁ τ ω) ∧
        (∃ hQa, 𝓗 = aFilt (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M' (fstChart d τ η₁' ζ₁) hQa) ∧
        V' = M'.indicator (aLife (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁)) ∧
        γ' = aTrace M' (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ∧
        ∀ ω (q : ℝ≥0), (q : ℝ≥0∞) < V' ω → W q ω = aDriver (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) q ω := by
  obtain ⟨η₁', hm₁, ha₁⟩ := exists_measurable_version_of_isFlowLine hη₁
  obtain ⟨M', hM'M, hM', hMM', hMg⟩ := exists_subset_isFstGood hκ hκ4 hη₁ hd hag ha₁ (x₁ := x₁) hτ hM hMord
  obtain ⟨E, hEm, hE⟩ := exists_retEnds_seed hL75 hκ hκ4 hb hx hh hη₁ hη₂ hd hag hτm
  obtain ⟨𝓗, W, V', γ', h0, hWc, hW0, hWa, hV, hγm, hγc, hγ0, hcan, hgen, h𝓗, hV', hγ', hWe⟩ :=
    exists_fstProc hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hm₁ ha₁ hτm hM' hMg
  have hMord' : ∀ᵐ ω ∂P, ω ∈ M' → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r := by
    filter_upwards [hMord] with ω hω hω' using hω (hM'M hω')
  refine ⟨M', hM'M, hM', hMM', 𝓗, W, E, V', γ', h0, hWc, hW0, hWa, hV, hγm, hγc, hγ0,
    hEm.mono h0 le_rfl, hτm.mono h0 le_rfl, Eventually.of_forall fun ω hω => ?_, Eventually.of_forall hgen, ?_, η₁',
    hMg, h𝓗, hV', hγ', hWe⟩
  · obtain ⟨hl, hp⟩ := hcan ω hω
    exact ⟨hl, fun t ht => hp t ht⟩
  · filter_upwards [hE, hMord'] with ω hω hord hω'
    exact hω (hord hω')

end InteractingSLE.RLC.AStopProc
