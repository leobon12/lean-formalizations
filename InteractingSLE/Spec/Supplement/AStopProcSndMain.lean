/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopProcSnd
import InteractingSLE.Spec.Restart.RetPlumbProofChart

/-!
# The A-stopped second continuation: filtration, driver, stop and trace (items 2 of `AStopSourceInputs`)

Packet PROVE-T15-ASTOP-PROC. In the setting of `RLC.OrdModel.RetOrdAStopSourceSndStatement` (two flow lines,
measurable good retained data `d` agreeing with them on the live event, Lemma 7.5):

* `IsSndGood`: the pathwise good event of a sample (live, chart event of `d`, a good measurable version `η₂'` of the
  second flow line, prefix agreements);
* **`exists_subset_isSndGood`**: every stop-line event `M` of ordinary pairs (a.s.) contains a stop-line event `M'`,
  almost surely equal to it, on which every sample is good;
* `aLife_aPath_snd_eq`: on good samples, the capacity lifetime and the trace are the canonical retained ones of the
  flow line (`canonRetLife`, `canonRetPath` with translation `0`), exactly as in the source statement;
* **`sndObs_of_flowLines`**: the processes are observed in RETPLUMB's physical filtration (the chart is measurable for
  the stop line's completed histories via `RetAux79.chart_measurability_retSigma76`);
* **`exists_sndProc`**: the time-changed filtration `𝓗` (with `retSigma76 ≤ 𝓗 0`), a globally continuous adapted
  driver from `0`, the stopping time `V'` and the trace `γ'` with every conjunct of item 2 of `AStopSourceInputs`,
  `V' = V`, `γ' = γ` on `[0, V]` at every sample of `M` (not only almost surely), the generation `W ↦ γ'` on `M`, and
  the explicit form of `𝓗`, `V'` and `W` (for the safe laws, item 5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopProc

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F LocalSets
open LQGMetric (DistOn)

universe v

section Defs

variable {Ω : Type*}

/-- **A good sample of the A-stopped second continuation** with the measurable version `η₂'` of the second flow line:
both prefixes alive, the chart event of `d`, `η₂'` a good path equal to `η₂` through its lifetime, and the prefixes of
`d` equal to those of the flow lines. -/
def IsSndGood (d : RetData Ω) (η₁ η₂ η₂' : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (x₂ : ℝ) (ω : Ω) : Prop :=
  (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ d.E ∧ IsPathGood (η₂' ω) (ζ₂ ω) x₂ ∧
    (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ (∀ s ≤ d.r, d.η₂ ω s = η₂ ω s) ∧
    ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s

variable {d : RetData Ω} {η₁ η₂ η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {x₂ : ℝ} {ω : Ω}

theorem IsSndGood.agree₂ (hg : IsSndGood d η₁ η₂ η₂' ζ₁ ζ₂ x₂ ω) : ∀ s ≤ d.r, d.η₂ ω s = η₂' ω s := fun s hs => by
  rw [hg.2.2.2.2.2.1 s hs, hg.2.2.2.2.2.2 s ((ENNReal.coe_le_coe.2 hs).trans hg.2.1.le)]

/-- **On good samples the capacity lifetime and the trace are the canonical retained ones of the flow line.** -/
theorem aLife_aPath_snd_eq (hg : IsSndGood d η₁ η₂ η₂' ζ₁ ζ₂ x₂ ω) :
    aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω =
        canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ∧
      aPath (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω =
        canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 := by
  obtain ⟨-, hr, -, -, h₁, -, h₂⟩ := hg
  have hK : sndSet d η₂' ω = η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r := by
    unfold sndSet
    rw [image_congr fun s hs => h₁ s hs.2,
      image_congr fun s hs => h₂ s ((ENNReal.coe_le_coe.2 hs.2).trans hr.le)]
  obtain ⟨hP, hL⟩ := canonRetPath_congr (D := d.D ω) (φ := d.fwd ω) (a := d.r)
    (K := η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (c := 0) h₂
  refine ⟨?_, ?_⟩
  · rw [← hL, canonRetLife_zero, ← hK]
    rfl
  · rw [← hP, canonRetPath_zero, ← hK]
    rfl

end Defs

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type v} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞} {d : RetData Ω}

/-- **Good sub-events.** Every stop-line event `M` of ordinary pairs (almost surely) contains a stop-line event `M'`,
almost surely equal to it, on which every sample is good. -/
theorem exists_subset_isSndGood (hκ : 0 < κ) (hκ4 : κ < 4) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {η₂' : Ω → ℝ≥0 → ℂ} (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) :
    ∃ M' ⊆ M, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M' ∧ (∀ᵐ ω ∂P, ω ∈ M → ω ∈ M') ∧
      ∀ ω ∈ M', IsSndGood d η₁ η₂ η₂' ζ₁ ζ₂ x₂ ω := by
  classical
  set Good : Set Ω := {ω | ω ∈ M → IsSndGood d η₁ η₂ η₂' ζ₁ ζ₂ x₂ ω} with hGood
  have hae : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [hMord, hag, ha₂, ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂]
      with ω hord hagω he hp hω
    have ho := hord hω
    obtain ⟨hG, a₁, a₂⟩ := hagω ho.1 ho.2.1
    exact ⟨ho.1, ho.2.1, hd.mem_E_of_ordinary hG a₁ a₂ ho, Supp7.IsPathGood.congr hp he, a₁, a₂, he⟩
  set G' : Set Ω := (toMeasurable P Goodᶜ)ᶜ with hG'
  have hG'sub : G' ⊆ Good := fun ω hω => by
    by_contra h'
    exact hω (subset_toMeasurable P _ h')
  have hG'm : MeasurableSet G' := (measurableSet_toMeasurable P _).compl
  have hG'ae : ∀ᵐ ω ∂P, ω ∈ G' := by
    rw [ae_iff]
    have : {ω | ¬ ω ∈ G'} = toMeasurable P Goodᶜ := by ext ω; simp [hG']
    rw [this, measure_toMeasurable]
    exact ae_iff.1 hae
  have hG'R : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] G' := by
    apply measurableSet_retSigma76_congr hG'm (@MeasurableSet.univ Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r))
    filter_upwards [hG'ae] with ω hω
    exact propext ⟨fun _ => trivial, fun _ => hω⟩
  refine ⟨M ∩ G', inter_subset_left, hM.inter hG'R, ?_, fun ω hω => hG'sub hω.2 hω.1⟩
  filter_upwards [hG'ae] with ω hω hM
  exact ⟨hM, hω⟩

/-- **The A-stopped second continuation is observed in RETPLUMB's physical filtration** on an event of good samples
(with the capped history readers of `RetAux79.exists_capped_version`, Lemma 7.5). -/
theorem sndObs_of_flowLines (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {η₂' : Ω → ℝ≥0 → ℂ} (hm₂ : ∀ t, Measurable fun ω => η₂' ω t)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMg : ∀ ω ∈ M, IsSndGood d η₁ η₂ η₂' ζ₁ ζ₂ x₂ ω) :
    AObs (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) := by
  classical
  have hζ₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζ₂ := measurable_lifetime_of_isFlowLine hη₂
  choose α₁ hc₁ hm₁ h0₁ _hk₁ hag₁ _hf₁ _hz₁ using fun t : ℝ≥0 =>
    exists_capped_version hL75 hκ hκ4 hb hh hη₁ (fun _ => 0) (capR d.u (d.r + t))
  choose α₂ hc₂ hmc₂ h0₂ _hk₂ hag₂ _hf₂ _hz₂ using fun t : ℝ≥0 =>
    exists_capped_version hL75 hκ hκ4 hb hh hη₂ (fun _ => 0) (capR d.u (d.r + t))
  -- the chart of `d` restricted to the live event
  set Lv : Set Ω := {ω | (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω} with hLv
  have hLvm : MeasurableSet Lv := (measurableSet_lt measurable_const hζ₁).inter (measurableSet_lt measurable_const hζ₂)
  set d₁ : RetData Ω := ⟨d.G ∩ Lv, d.η₁, d.η₂, d.u, d.r⟩ with hd₁def
  have hd₁ : d₁.IsMeasGood :=
    ⟨hd.measurableSet_G.inter hLvm, hd.meas₁, hd.meas₂, fun ω hω => hd.good ω hω.1⟩
  have hag' : ∀ᵐ ω ∂P, (d₁.u : ℝ≥0∞) < ζ₁ ω → (d₁.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d₁.G ∧
      (∀ s ≤ d₁.u, d₁.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d₁.r, d₁.η₂ ω t = η₂ ω t := by
    filter_upwards [hag] with ω hω hu hr
    obtain ⟨hG, a₁, a₂⟩ := hω hu hr
    exact ⟨⟨hG, hu, hr⟩, a₁, a₂⟩
  have hac₁ : ∀ᵐ ω ∂P, ∀ s, α₁ 0 ω s = η₁ ω (capTime (capR d₁.u d₁.r) (ζ₁ ω) s) := by
    simpa only [add_zero] using hag₁ 0
  have hac₂ : ∀ᵐ ω ∂P, ∀ s, α₂ 0 ω s = η₂ ω (capTime (capR d₁.u d₁.r) (ζ₂ ω) s) := by
    simpa only [add_zero] using hag₂ 0
  obtain ⟨hdom, hfwd, -⟩ := chart_measurability_retSigma76 hd₁ hζ₁ hζ₂ (fun ω hω => hω.2) hag'
    (hc₁ 0) (hc₂ 0) (hm₁ 0) (hmc₂ 0) (h0₁ 0) (h0₂ 0) hac₁ hac₂
  have hde (z : ℂ) : {ω | z ∈ (d₁.chart ω).dom} = {ω | z ∈ d₁.D ω} := by
    ext ω
    change z ∈ (d₁.chart ω).dom ↔ z ∈ d₁.D ω
    rw [← SetLike.mem_coe, hd₁.coe_dom_chart ω]
  have hagree : ∀ ω ∈ M, d₁.D ω = d.D ω ∧ (d₁.chart ω).1 = d.fwd ω := by
    intro ω hω
    obtain ⟨hu, hr, hE, -⟩ := hMg ω hω
    obtain ⟨hEiff, hD, hch⟩ := RetData.chart_eq_of_agree (d := d) (G' := d.G ∩ Lv) (η₁' := d.η₁) (η₂' := d.η₂)
      (RetData.E_subset_G hE) ⟨RetData.E_subset_G hE, hu, hr⟩ (fun _ _ => rfl) (fun _ _ => rfl)
    refine ⟨hD, ?_⟩
    have hch' : d₁.chart ω = d.chart ω := hch
    rw [hch', RetData.chart_of_mem hE]
  refine sndObs hd hM hζ₂ hm₂ hag ha₂ (x₂ := x₂)
    (fun ω hω => ⟨(hMg ω hω).1, (hMg ω hω).2.1, (hMg ω hω).2.2.1, (hMg ω hω).2.2.2.1, (hMg ω hω).agree₂⟩)
    α₁ α₂ hc₁ hc₂ hm₁ hmc₂ hag₁ hag₂ (D₁ := d₁.D) (φ₁ := fun ω => (d₁.chart ω).1) hd₁.isOpen_D
    (fun z => by rw [← hde z]; exact hdom z) (fun z => by rw [← hde z]; exact hfwd z)
    (fun ω hω => (hagree ω hω).1) (fun ω hω => (hagree ω hω).2)

/-- **Item 2 of `AStopSourceInputs` for the A-stopped second continuation.** On a stop-line event `M` of good samples:
a filtration `𝓗` containing the stop line's completed histories at time `0`, a globally continuous `𝓗`-adapted driver
`W` from `0`, an `𝓗`-stopping time `V'` and a trace `γ'` (measurable coordinates, continuous on `[0, V']`, `0` at `0`)
which at every sample of `M` are the canonical retained lifetime and path of the flow line (source statement's `V`,
`γ`) and are generated by `W`. Explicitly, `𝓗` is the time change of `retPhysFiltration` along the supported clock,
`V' = M.indicator (aLife …)`, `γ' = aTrace M …`, and `W = aDriver …` before `V'`. -/
theorem exists_sndProc (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {η₂' : Ω → ℝ≥0 → ℂ} (hm₂ : ∀ t, Measurable fun ω => η₂' ω t)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMg : ∀ ω ∈ M, IsSndGood d η₁ η₂ η₂' ζ₁ ζ₂ x₂ ω) :
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (V' : Ω → ℝ≥0∞) (γ' : Ω → ℝ≥0 → ℂ),
      retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r ≤ 𝓗 0 ∧
      (∀ ω, Continuous (W · ω)) ∧ (∀ ω, W 0 ω = 0) ∧ StronglyAdapted 𝓗 W ∧
      (∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V' ω ≤ t}) ∧
      (∀ t, Measurable fun ω => γ' ω t) ∧ (∀ ω, ContinuousOn (γ' ω) {t | (t : ℝ≥0∞) ≤ V' ω}) ∧
      (∀ ω, γ' ω 0 = 0) ∧
      (∀ ω ∈ M, V' ω = canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 →
          γ' ω t = canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 t) ∧
      (∀ ω ∈ M, IsGeneratingTrace (W · ω) (V' ω) (γ' ω)) ∧
      (∃ hQa, 𝓗 = aFilt (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M (sndChart d η₂' ζ₂) hQa) ∧
      V' = M.indicator (aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂)) ∧
      γ' = aTrace M (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ∧
      ∀ ω (q : ℝ≥0), (q : ℝ≥0∞) < V' ω → W q ω = aDriver (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) q ω := by
  have ho := sndObs_of_flowLines hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hm₂ ha₂ hM hMg
  have hg : ∀ ω ∈ M, IsAGood (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω := fun ω hω =>
    isAGood_snd hd (hMg ω hω).2.2.1 (hMg ω hω).2.2.2.1 (hMg ω hω).agree₂ (hMg ω hω).2.1
  obtain ⟨W, hWc, hW0, hWa, he, hV, hgen⟩ := ho.exists_driver hg
  refine ⟨aFilt _ M _ (ho.measurable_clock hg), W, M.indicator (aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂)),
    aTrace M (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂), ?_, hWc, hW0, hWa, hV, ho.measurable_aTrace hg,
    continuousOn_aTrace hg, aTrace_zero hg, ?_, hgen, ⟨_, rfl⟩, rfl, rfl, he⟩
  · have h0 : retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r 0 = retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r := by
      rw [retPhysFiltration_apply, add_zero]
    exact h0 ▸ le_aFilt_zero (ho.measurable_clock hg)
  · intro ω hω
    obtain ⟨hl, hp⟩ := aLife_aPath_snd_eq (hMg ω hω)
    refine ⟨by rw [indicator_of_mem hω, hl], fun t _ => by rw [aTrace_of_mem hω, hp]⟩

end InteractingSLE.RLC.AStopProc
