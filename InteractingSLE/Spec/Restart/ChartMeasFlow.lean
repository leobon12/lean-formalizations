/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartMeas
import InteractingSLE.Spec.Restart.ChartDataLim
import InteractingSLE.Spec.Supplement.LPTrace

/-!
# The measurable first-contact chart of two flow lines

Packet PROVE-RESTART-CPL4. The frozen `IsFlowLine` makes the path `η` only almost surely equal to the generating trace
of its driver, so `η` itself need not be measurable. Its **measurable version** is the trace reconstructed from the
recorded driving history by PROVE-LP's measurable map `LP.drivingTrace` (`exists_measurable_version_of_isFlowLine`);
the lifetime is measurable since the driver is adapted before it (`measurable_lifetime_of_isFlowLine`). With
Lemma 7.7's confinement (`Supp10.Lemma77Statement`) this gives the data of `ChartMeas.lean` for two flow lines on a
measurable full-measure event (`exists_pairData_of_isFlowLine`).

The chart only reads the paths on their closed available intervals (`isFirstContact_congr`, `prefixSet_congr`,
`isFirstContactChart_congr`), so at every first contact of the **original** paths (on the full-measure event) the
measurable chart is a first-contact chart of the original paths and the measurable chart field is its transport
(`IsMeasGood.chart_spec_of_agree`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart

/-! ### Measurable versions of flow lines -/

section Flow

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- The lifetime of a process adapted before it is measurable. -/
theorem measurable_of_adaptedBefore {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X) :
    Measurable ζ := by
  refine measurable_of_Ioi fun a => ?_
  induction a using ENNReal.recTopCoe with
  | top => simp
  | coe t =>
    have h := 𝓕.le t _ (hX t univ MeasurableSet.univ)
    simp only [mem_univ, and_true] at h
    exact h

/-- A process adapted before `ζ`, set to `0` from `ζ` on, is measurable at each time. -/
theorem measurable_ite_of_adaptedBefore {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X)
    (t : ℝ≥0) : Measurable fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else 0 := by
  classical
  intro B hB
  have hT : MeasurableSet {ω | (t : ℝ≥0∞) < ζ ω} := by
    have := 𝓕.le t _ (hX t univ MeasurableSet.univ)
    simpa only [mem_univ, and_true] using this
  have heq : (fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else 0) ⁻¹' B =
      {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ B} ∪ ({ω | (t : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ B}) := by
    ext ω
    by_cases ht : (t : ℝ≥0∞) < ζ ω <;> simp [ht]
  rw [heq]
  exact (𝓕.le t _ (hX t B hB)).union (hT.compl.inter (MeasurableSet.const _))

/-- **The lifetime of a flow line is measurable.** -/
theorem measurable_lifetime_of_isFlowLine (hη : IsFlowLine κ b jumps x θ P h η ζ) : Measurable ζ := by
  obtain ⟨_, 𝓕, W, _, _, _, -, hcoup, -⟩ := hη
  exact measurable_of_adaptedBefore hcoup.1.2.1

/-- **A measurable version of a flow line**: a path, measurable at every fixed time, that agrees almost surely with
the flow line on its closed available interval (the trace reconstructed from the driving history, `LP.drivingTrace`). -/
theorem exists_measurable_version_of_isFlowLine (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∃ η' : Ω → ℝ≥0 → ℂ, (∀ t, Measurable fun ω => η' ω t) ∧
      ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ ω → η' ω s = η ω s := by
  classical
  have hζ := measurable_lifetime_of_isFlowLine hη
  obtain ⟨_, 𝓕, W, _, _, _, -, hcoup, htr⟩ := hη
  have hW := hcoup.1.2.1
  set W' : ℝ≥0 → Ω → ℝ := fun t ω => if (t : ℝ≥0∞) < ζ ω then W t ω else 0 with hW'
  have hW'm : ∀ t, Measurable (W' t) := fun t => measurable_ite_of_adaptedBefore hW t
  have hpm : Measurable fun ω => (ζ ω, fun s => W' s ω) :=
    hζ.prodMk (measurable_pi_iff.2 fun s => hW'm s)
  refine ⟨fun ω t => (x : ℂ) + (LP.drivingTrace (ζ ω, fun s => W' s ω)).2 t, fun t => ?_, ?_⟩
  · exact measurable_const.add
      ((measurable_pi_apply t).comp (measurable_snd.comp (LP.measurable_drivingTrace.comp hpm)))
  · filter_upwards [htr, hcoup.1.2.2.2.2] with ω hω hpath s hs
    obtain ⟨hw0, -, -, hcw, -⟩ := hpath
    have he := LP.drivingTrace_eq hω hcw hw0 (w' := fun s => W' s ω) fun r hr => by
      simp only [hW', hr, ↓reduceIte]
    rw [he]
    simp only [min_eq_left hs, ENNReal.toNNReal_coe]
    ring

end Flow

/-! ### The chart reads the paths only on their available intervals -/

section Congr

variable {η₁ η₁' η₂ η₂' : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

theorem hasContact_congr (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → η₁' s = η₁ s)
    (ha₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → η₂' t = η₂ t) :
    HasContact η₁' ζ₁ η₂' ζ₂ ↔ HasContact η₁ ζ₁ η₂ ζ₂ := by
  constructor
  · rintro ⟨s, t, hs, ht, he⟩; exact ⟨s, t, hs, ht, by rw [← ha₁ s hs, ← ha₂ t ht, he]⟩
  · rintro ⟨s, t, hs, ht, he⟩; exact ⟨s, t, hs, ht, by rw [ha₁ s hs, ha₂ t ht, he]⟩

theorem isFirstContact_congr (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → η₁' s = η₁ s)
    (ha₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → η₂' t = η₂ t) {s₀ t₀ : ℝ≥0} :
    IsFirstContact η₁' ζ₁ η₂' ζ₂ s₀ t₀ ↔ IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀ := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, by rw [← ha₁ s₀ h1, ← ha₂ t₀ h2, h3], fun s t hs ht he => h4 s t hs ht ?_⟩
    rw [ha₁ s hs, ha₂ t ht, he]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, by rw [ha₁ s₀ h1, ha₂ t₀ h2, h3], fun s t hs ht he => h4 s t hs ht ?_⟩
    rw [← ha₁ s hs, ← ha₂ t ht, he]

theorem image_Icc_congr (ha : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → η₁' s = η₁ s) {s₀ : ℝ≥0} (hs₀ : (s₀ : ℝ≥0∞) ≤ ζ₁) :
    η₁' '' Icc 0 s₀ = η₁ '' Icc 0 s₀ :=
  image_congr fun s hs => ha s ((ENNReal.coe_le_coe.2 hs.2).trans hs₀)

theorem prefixSet_congr (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → η₁' s = η₁ s)
    (ha₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → η₂' t = η₂ t) {s₀ t₀ : ℝ≥0} (hs₀ : (s₀ : ℝ≥0∞) ≤ ζ₁)
    (ht₀ : (t₀ : ℝ≥0∞) ≤ ζ₂) : prefixSet η₁' s₀ η₂' t₀ = prefixSet η₁ s₀ η₂ t₀ := by
  rw [prefixSet, prefixSet, image_Icc_congr ha₁ hs₀, image_Icc_congr ha₂ ht₀]

theorem activeDomain_congr (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → η₁' s = η₁ s)
    (ha₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → η₂' t = η₂ t) {s₀ t₀ : ℝ≥0} (hs₀ : (s₀ : ℝ≥0∞) ≤ ζ₁)
    (ht₀ : (t₀ : ℝ≥0∞) ≤ ζ₂) : activeDomain η₁' s₀ η₂' t₀ = activeDomain η₁ s₀ η₂ t₀ := by
  rw [activeDomain, activeDomain, image_Icc_congr ha₁ hs₀, image_Icc_congr ha₂ ht₀]

theorem isFirstContactChart_congr (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → η₁' s = η₁ s)
    (ha₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → η₂' t = η₂ t) {s₀ t₀ : ℝ≥0} (hs₀ : (s₀ : ℝ≥0∞) ≤ ζ₁)
    (ht₀ : (t₀ : ℝ≥0∞) ≤ ζ₂) {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ} :
    IsFirstContactChart η₁' s₀ η₂' t₀ φ ψ lift ↔ IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift := by
  have e₁ := activeDomain_congr ha₁ ha₂ hs₀ ht₀
  have e₂ := prefixSet_congr ha₁ ha₂ hs₀ ht₀
  have e₃ : η₁' s₀ = η₁ s₀ := ha₁ s₀ hs₀
  unfold IsFirstContactChart IsChartRegularPoint
  rw [e₁, e₂, e₃]

theorem isChartGood_congr (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → η₁' s = η₁ s)
    (ha₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → η₂' t = η₂ t) (hG : IsChartGood η₁ ζ₁ η₂ ζ₂) :
    IsChartGood η₁' ζ₁ η₂' ζ₂ := by
  obtain ⟨hc₁, hc₂, hH₁, hH₂, h0₁, h0₂, hfc⟩ := hG
  refine ⟨hc₁.congr fun s hs => ha₁ s hs, hc₂.congr fun t ht => ha₂ t ht,
    fun s hs => ha₁ s hs ▸ hH₁ s hs, fun t ht => ha₂ t ht ▸ hH₂ t ht,
    by rw [ha₁ 0 (by simp)]; exact h0₁, by rw [ha₂ 0 (by simp)]; exact h0₂, fun hc => ?_⟩
  obtain ⟨s₀, t₀, h, hcl⟩ := hfc ((hasContact_congr ha₁ ha₂).1 hc)
  refine ⟨s₀, t₀, (isFirstContact_congr ha₁ ha₂).2 h, ?_⟩
  rw [activeDomain_congr ha₁ ha₂ h.1 h.2.1, ha₁ s₀ h.1]
  exact hcl

end Congr

/-! ### The data for two flow lines -/

section FlowPair

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The measurable chart data of two flow lines** (with Lemma 7.7's confinement): measurable versions of the paths,
their lifetimes, and a measurable full-measure good event. -/
theorem exists_pairData_of_isFlowLine (h77 : Supp10.Lemma77Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    [IsProbabilityMeasure P] (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∃ d : PairData Ω, d.IsMeasGood ∧ d.ζ₁ = ζ₁ ∧ d.ζ₂ = ζ₂ ∧
      ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t := by
  obtain ⟨η₁', hm₁, ha₁⟩ := exists_measurable_version_of_isFlowLine hη₁
  obtain ⟨η₂', hm₂, ha₂⟩ := exists_measurable_version_of_isFlowLine hη₂
  set Good : Set Ω := {ω | (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s) ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω t = η₂ ω t) ∧ IsChartGood (η₁' ω) (ζ₁ ω) (η₂' ω) (ζ₂ ω)} with hGood
  have haeGood : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [ha₁, ha₂, Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂,
      ae_mem_Hbar_of_isFlowLine hη₁, ae_mem_Hbar_of_isFlowLine hη₂, Supp10.ae_apply_zero_of_isFlowLine hη₁,
      Supp10.ae_apply_zero_of_isFlowLine hη₂,
      h77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂] with
      ω e₁ e₂ hc₁ hc₂ hH₁ hH₂ h0₁ h0₂ h7
    refine ⟨e₁, e₂, isChartGood_congr e₁ e₂ ⟨hc₁, hc₂, hH₁, hH₂, by rw [h0₁]; simp, by rw [h0₂]; simp,
      fun hc => ?_⟩⟩
    obtain ⟨s₀, t₀, hf, hconf₁, -⟩ := h7 hc
    exact ⟨s₀, t₀, hf, hconf₁ s₀ le_rfl hf.1⟩
  set G : Set Ω := (toMeasurable P Goodᶜ)ᶜ with hG
  have hGsub : G ⊆ Good := fun ω hω => by
    by_contra h'
    exact hω (subset_toMeasurable P _ h')
  refine ⟨⟨G, η₁', ζ₁, η₂', ζ₂⟩, ⟨(measurableSet_toMeasurable P _).compl, hm₁, hm₂,
    measurable_lifetime_of_isFlowLine hη₁, measurable_lifetime_of_isFlowLine hη₂,
    fun ω hω => (hGsub hω).2.2⟩, rfl, rfl, ?_⟩
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    have : {ω | ¬ ω ∈ G} = toMeasurable P Goodᶜ := by ext ω; simp [hG]
    rw [this, measure_toMeasurable]
    exact ae_iff.1 haeGood
  filter_upwards [hGae] with ω hω
  exact ⟨hω, (hGsub hω).1, (hGsub hω).2.1⟩

end FlowPair

/-! ### The chart at a first contact of the original paths -/

namespace PairData

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

/-- At a first contact of paths agreeing with the measurable ones on their available intervals (at `ω ∈ G`), the
measurable chart is a first-contact chart of the original paths. -/
theorem IsMeasGood.chart_spec_of_agree (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.G) {η₁ η₂ : ℝ≥0 → ℂ}
    (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ s)
    (ha₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω t = η₂ t) {s₀ t₀ : ℝ≥0}
    (hfc : IsFirstContact η₁ (d.ζ₁ ω) η₂ (d.ζ₂ ω) s₀ t₀) :
    ω ∈ d.E ∧ d.s₀ ω = s₀ ∧ d.t₀ ω = t₀ ∧ d.chart ω = (d.fwd ω, d.inv ω, d.lift ω) ∧
      IsFirstContactChart η₁ s₀ η₂ t₀ (d.fwd ω) (d.inv ω) (d.lift ω) := by
  have hfc' := (isFirstContact_congr ha₁ ha₂).2 hfc
  obtain ⟨hE, hs, ht⟩ := eq_of_isFirstContact hω hfc'
  refine ⟨hE, hs, ht, chart_of_mem hE, ?_⟩
  have hC := (hd.isFirstContactChart hE).2
  rw [hs, ht] at hC
  exact (isFirstContactChart_congr ha₁ ha₂ hfc.1 hfc.2.1).1 hC

end PairData

end Restart

end InteractingSLE
