/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopProcFst
import InteractingSLE.Spec.Supplement.AStopProcSndMain

/-!
# The A-stopped first continuation at its seed: filtration, driver, stop and trace (item 2 of `AStopSourceInputs`)

Packet PROVE-T15-ASTOP-PROC. In the setting of `RLC.RetOrdAStopSourceFstSeedStatement`, with a stop-line measurable
seed `τ` equal to the first tip's chart point `tipPos` almost surely at ordinary pairs (the source's `(β ω).2`):

* `IsFstGood`, **`exists_subset_isFstGood`** (good sub-events, as for the second continuation);
* `aLife_aPath_fst_eq`: on good samples the capacity lifetime and the trace are the source statement's
  `canonRetLife … (tipPos)` and `canonRetPath … (tipPos) − τ` (`OrdDet.canonRetPath_shift`);
* **`fstObs_of_flowLines`** and **`exists_fstProc`**: the time change `𝓗` of `fstPhysFiltration` (lines `(u + t, r)`),
  `retSigma76 … d.u d.r ≤ 𝓗 0`, the adapted driver, stop and trace with every conjunct of item 2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopProc

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F LocalSets
open QuantumZipper (H)
open LQGMetric (DistOn)

universe v

section Defs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A good sample of the A-stopped first continuation** with the measurable version `η₁'` of the first flow line and
the seed `τ`. -/
def IsFstGood (d : RetData Ω) (η₁ η₂ η₁' : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (x₁ : ℝ) (τ : Ω → ℝ) (ω : Ω) :
    Prop :=
  (d.r : ℝ≥0∞) < ζ₂ ω ∧ IsFstPath d η₁' ζ₁ x₁ τ ω ∧ (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧
    (∀ s ≤ d.r, d.η₂ ω s = η₂ ω s) ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s

variable {d : RetData Ω} {η₁ η₂ η₁' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {x₁ : ℝ} {τ : Ω → ℝ} {ω : Ω}

omit [MeasurableSpace Ω] in
theorem tipPos_congr {η η' : Ω → ℝ≥0 → ℂ} (h : η' ω d.u = η ω d.u) : tipPos d η' ω = tipPos d η ω := by
  unfold tipPos
  rw [h]

omit [MeasurableSpace Ω] in
/-- **On good samples the capacity lifetime and the trace are the source statement's canonical ones.** -/
theorem aLife_aPath_fst_eq (hg : IsFstGood d η₁ η₂ η₁' ζ₁ ζ₂ x₁ τ ω) :
    aLife (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω =
        canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) ∧
      ∀ q, aPath (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω q =
        canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω) q - τ ω := by
  obtain ⟨-, hp, h₁, h₂, he⟩ := hg
  have hc : τ ω = tipPos d η₁ ω := hp.seed.trans (tipPos_congr (h₁ d.u le_rfl))
  have hK : fstSet d η₁' ω = η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r := by
    unfold fstSet
    rw [image_congr fun s hs => h₂ s hs.2, image_congr fun s hs => he s ((ENNReal.coe_le_coe.2 hs.2).trans hp.lt.le),
      union_comm]
  obtain ⟨hP, hL⟩ := canonRetPath_congr (D := d.D ω) (φ := fun z => d.fwd ω z - (τ ω : ℂ)) (a := d.u)
    (K := η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (c := 0) he
  refine ⟨?_, fun q => ?_⟩
  · rw [OrdDet.canonRetLife_shift, ← hc, ← hL, canonRetLife_zero, ← hK]
    rfl
  · rw [OrdDet.canonRetPath_shift, ← hc, add_sub_cancel_right, ← hP, canonRetPath_zero, ← hK]
    rfl

end Defs

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type v} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞} {d : RetData Ω}

/-- **Good sub-events of the first continuation.** -/
theorem exists_subset_isFstGood (hκ : 0 < κ) (hκ4 : κ < 4) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {η₁' : Ω → ℝ≥0 → ℂ} (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s) {τ : Ω → ℝ}
    (hτ : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → τ ω = tipPos d η₁ ω)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) :
    ∃ M' ⊆ M, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M' ∧ (∀ᵐ ω ∂P, ω ∈ M → ω ∈ M') ∧
      ∀ ω ∈ M', IsFstGood d η₁ η₂ η₁' ζ₁ ζ₂ x₁ τ ω := by
  classical
  set Good : Set Ω := {ω | ω ∈ M → IsFstGood d η₁ η₂ η₁' ζ₁ ζ₂ x₁ τ ω} with hGood
  have hae : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [hMord, hag, ha₁, hτ, ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁]
      with ω hord hagω he hτω hp hω
    have ho := hord hω
    obtain ⟨hG, a₁, a₂⟩ := hagω ho.1 ho.2.1
    have hi₂ : d.η₂ ω '' Icc 0 d.r = η₂ ω '' Icc 0 d.r := image_congr fun t ht => a₂ t ht.2
    refine ⟨ho.2.1, ⟨hd.mem_E_of_ordinary hG a₁ a₂ ho, Supp7.IsPathGood.congr hp he,
      fun s hs => (a₁ s hs).trans (he s ((ENNReal.coe_le_coe.2 hs).trans ho.1.le)).symm, ho.1, ?_, ?_, ?_, ?_, ?_⟩,
      a₁, a₂, he⟩
    · rw [a₁ d.u le_rfl]; exact ho.2.2.1
    · rw [a₁ d.u le_rfl, hi₂]; exact ho.2.2.2.2.2.1
    · rw [a₁ d.u le_rfl, activeDomain_congr_Icc (fun s hs => a₁ s hs.2) (fun t ht => a₂ t ht.2)]
      exact ho.2.2.2.2.2.2.1
    · intro s hs hne
      rw [a₁ s hs.le, a₁ d.u le_rfl] at hne
      exact (ne_of_lt hs) (hp.1 (show (s : ℝ≥0∞) ≤ ζ₁ ω from (ENNReal.coe_le_coe.2 hs.le).trans ho.1.le)
        (show (d.u : ℝ≥0∞) ≤ ζ₁ ω from ho.1.le) hne)
    · rw [hτω ho, tipPos_congr (a₁ d.u le_rfl)]
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

/-- **The A-stopped first continuation is observed in its physical filtration** on an event of good samples, for a
stop-line measurable seed `τ` (the capped history readers of `RetAux79.exists_capped_version`, Lemma 7.5). -/
theorem fstObs_of_flowLines (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {η₁' : Ω → ℝ≥0 → ℂ} (hm₁ : ∀ t, Measurable fun ω => η₁' ω t)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s) {τ : Ω → ℝ}
    (hτm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] τ)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMg : ∀ ω ∈ M, IsFstGood d η₁ η₂ η₁' ζ₁ ζ₂ x₁ τ ω) :
    AObs (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) := by
  classical
  have hζ₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζ₂ := measurable_lifetime_of_isFlowLine hη₂
  choose α₁ hc₁ hmc₁ h0₁ _hk₁ hag₁ _hf₁ _hz₁ using fun t : ℝ≥0 =>
    exists_capped_version hL75 hκ hκ4 hb hh hη₁ (fun _ => 0) (capR (d.u + t) d.r)
  choose α₂ hc₂ hmc₂ h0₂ _hk₂ hag₂ _hf₂ _hz₂ using fun t : ℝ≥0 =>
    exists_capped_version hL75 hκ hκ4 hb hh hη₂ (fun _ => 0) (capR (d.u + t) d.r)
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
    (hc₁ 0) (hc₂ 0) (hmc₁ 0) (hmc₂ 0) (h0₁ 0) (h0₂ 0) hac₁ hac₂
  have hde (z : ℂ) : {ω | z ∈ (d₁.chart ω).dom} = {ω | z ∈ d₁.D ω} := by
    ext ω
    change z ∈ (d₁.chart ω).dom ↔ z ∈ d₁.D ω
    rw [← SetLike.mem_coe, hd₁.coe_dom_chart ω]
  have hdom₁ : ∀ z, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] {ω | z ∈ d₁.D ω} := fun z => by
    rw [← hde z]; exact hdom z
  have hfwd₁ : ∀ z, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r]
      ({ω | z ∈ d₁.D ω}.indicator fun ω => (d₁.chart ω).1 z) := fun z => by
    rw [← hde z]; exact hfwd z
  have hfwd' : ∀ z, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r]
      ({ω | z ∈ d₁.D ω}.indicator fun ω => (d₁.chart ω).1 z - (τ ω : ℂ)) := by
    intro z
    have e : ({ω | z ∈ d₁.D ω}.indicator fun ω => (d₁.chart ω).1 z - (τ ω : ℂ)) =
        ({ω | z ∈ d₁.D ω}.indicator fun ω => (d₁.chart ω).1 z) -
          ({ω | z ∈ d₁.D ω}.indicator fun ω => (τ ω : ℂ)) := by
      funext ω
      by_cases hω : ω ∈ {ω | z ∈ d₁.D ω}
      · simp only [Pi.sub_apply, indicator_of_mem hω]
      · simp only [Pi.sub_apply, indicator_of_notMem hω, sub_zero]
    rw [e]
    exact (hfwd₁ z).sub ((Complex.measurable_ofReal.comp hτm).indicator (hdom₁ z))
  have hagree : ∀ ω ∈ M, d₁.D ω = d.D ω ∧ (d₁.chart ω).1 = d.fwd ω := by
    intro ω hω
    have hE := (hMg ω hω).2.1.mem_E
    obtain ⟨-, hD, hch⟩ := RetData.chart_eq_of_agree (d := d) (G' := d.G ∩ Lv) (η₁' := d.η₁) (η₂' := d.η₂)
      (RetData.E_subset_G hE) ⟨RetData.E_subset_G hE, (hMg ω hω).2.1.lt, (hMg ω hω).1⟩
      (fun _ _ => rfl) (fun _ _ => rfl)
    refine ⟨hD, ?_⟩
    have hch' : d₁.chart ω = d.chart ω := hch
    rw [hch', RetData.chart_of_mem hE]
  refine fstObs hd hM hζ₁ hm₁ hag ha₁ (x₁ := x₁) (τ := τ) (fun ω hω => ⟨(hMg ω hω).1, (hMg ω hω).2.1⟩)
    α₁ α₂ hc₁ hc₂ hmc₁ hmc₂ hag₁ hag₂ (D₁ := d₁.D) (φ₁ := fun ω z => (d₁.chart ω).1 z - (τ ω : ℂ))
    hd₁.isOpen_D hdom₁ hfwd' (fun ω hω => (hagree ω hω).1) (fun ω hω => by rw [(hagree ω hω).2])

/-- **Item 2 of `AStopSourceInputs` for the A-stopped first continuation at its seed.** As `exists_sndProc`, with
the physical filtration `fstPhysFiltration` (lines `(u + t, r)`), the chart recentred at the seed `τ`, and, at every
sample of `M`, the source statement's lifetime `canonRetLife … (tipPos)` and path `canonRetPath … (tipPos) − τ`. -/
theorem exists_fstProc (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {η₁' : Ω → ℝ≥0 → ℂ} (hm₁ : ∀ t, Measurable fun ω => η₁' ω t)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s) {τ : Ω → ℝ}
    (hτm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] τ)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMg : ∀ ω ∈ M, IsFstGood d η₁ η₂ η₁' ζ₁ ζ₂ x₁ τ ω) :
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (V' : Ω → ℝ≥0∞) (γ' : Ω → ℝ≥0 → ℂ),
      retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r ≤ 𝓗 0 ∧
      (∀ ω, Continuous (W · ω)) ∧ (∀ ω, W 0 ω = 0) ∧ StronglyAdapted 𝓗 W ∧
      (∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V' ω ≤ t}) ∧
      (∀ t, Measurable fun ω => γ' ω t) ∧ (∀ ω, ContinuousOn (γ' ω) {t | (t : ℝ≥0∞) ≤ V' ω}) ∧
      (∀ ω, γ' ω 0 = 0) ∧
      (∀ ω ∈ M, V' ω = canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) →
          γ' ω t = canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
            (tipPos d η₁ ω) t - τ ω) ∧
      (∀ ω ∈ M, IsGeneratingTrace (W · ω) (V' ω) (γ' ω)) ∧
      (∃ hQa, 𝓗 = aFilt (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M (fstChart d τ η₁' ζ₁) hQa) ∧
      V' = M.indicator (aLife (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁)) ∧
      γ' = aTrace M (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ∧
      ∀ ω (q : ℝ≥0), (q : ℝ≥0∞) < V' ω → W q ω = aDriver (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) q ω := by
  have ho := fstObs_of_flowLines hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hm₁ ha₁ hτm hM hMg
  have hg : ∀ ω ∈ M, IsAGood (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω := fun ω hω =>
    (hMg ω hω).2.1.isAGood hd
  obtain ⟨W, hWc, hW0, hWa, he, hV, hgen⟩ := ho.exists_driver hg
  refine ⟨aFilt _ M _ (ho.measurable_clock hg), W, M.indicator (aLife (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁)),
    aTrace M (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁), ?_, hWc, hW0, hWa, hV, ho.measurable_aTrace hg,
    continuousOn_aTrace hg, aTrace_zero hg, ?_, hgen, ⟨_, rfl⟩, rfl, rfl, he⟩
  · have h0 : fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r 0 = retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r := by
      rw [fstPhysFiltration_apply, add_zero]
    exact h0 ▸ le_aFilt_zero (ho.measurable_clock hg)
  · intro ω hω
    obtain ⟨hl, hp⟩ := aLife_aPath_fst_eq (hMg ω hω)
    refine ⟨by rw [indicator_of_mem hω, hl], fun t _ => by rw [aTrace_of_mem hω, hp]⟩

end InteractingSLE.RLC.AStopProc
