/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ClockFlow

/-!
# The canonical W8.1 clock data of two flow lines (measurable, almost surely the clock data)

Packet PROVE-RESTART-CPL5. For two flow lines as in `FirstContactKernelCanonStatement` and measurable pair data `d`
(CPL4), the chart paths of the two continuations read in their relative capacity clocks,

  `γ₁ = cGamma d E₁ s₀ η₁ ζ₁`, `U₁ = cLife d E₁ s₀ η₁ ζ₁` (and the same for the second path),

are measurable, continuous on `[0, Uᵢ]` for every `ω`, almost surely the canonical forward-limit chart paths in
relative capacity time (`PairData.IsCanonClock`), and almost surely give CPL4's clock data `IsChartClockData` at every
first contact with two nonempty continuations (`exists_canonClock`). The events `Eᵢ` are measurable full-measure
modifications of the first-contact events on which Lemma 7.7's confinement, Aux. lemma 25's simplicity and the
generating-trace facts hold.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart

variable {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s₀ t₀ : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

/-- **Forward chart limits at every continuation point** (the chart's regular points: the contact point, and points
off the old union by no return). -/
theorem IsContinuationGood.exists_limit (hg : IsContinuationGood η₁ ζ₁ s₀ η₂ ζ₂ t₀)
    (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) (h0₂ : (η₂ 0).im = 0) {s : ℝ≥0} (hs : s₀ ≤ s)
    (hsζ : (s : ℝ≥0∞) ≤ ζ₁) :
    ∃ w ∈ Hbar, Tendsto φ (𝓝[activeDomain η₁ s₀ η₂ t₀] (η₁ s)) (𝓝 w) ∧ ψ w = η₁ s ∧
      ∀ w' ∈ Hbar, ψ w' = η₁ s → w' = w := by
  have hfc := hg.firstContact
  have hc₁ := hg.continuousOn₁_Icc hfc.1
  have hc₂ := hg.continuousOn₂_Icc
  refine hC.2.2.2.2.2.2.2.2.2.2 _ (hg.conf s hs hsζ) (Or.inr ?_)
  rcases hs.lt_or_eq with hlt | rfl
  · exact isUnboundedLinked_of_notMem hc₁ hc₂ hg.seed₁ hfc.2.2.1
      ((Sec7.IsFirstContact.no_return hg.injOn₁ hg.injOn₂ hfc).1 s hlt hsζ)
  · refine isUnboundedLinked_firstContact hc₁ hc₂ hg.seed₁ h0₂ hfc.2.2.1 (fun s hs h => ?_) fun t ht h => ?_
    · exact absurd (hg.injOn₁ ((ENNReal.coe_le_coe.2 hs.le).trans hfc.1) hfc.1 h) hs.ne
    · have := (hfc.2.2.2 s₀ t hfc.1 ((ENNReal.coe_le_coe.2 ht.le).trans hfc.2.1) (by rw [h])).2
      exact absurd this (not_le.2 ht)

/-- The clock data only read the paths on their available intervals. -/
theorem isChartClockData_congr {η₁' η₂' : ℝ≥0 → ℂ} (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → η₁' s = η₁ s)
    (ha₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → η₂' t = η₂ t) {γ₁ γ₂ : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞}
    (h : IsChartClockData ψ η₁' ζ₁ s₀ η₂' ζ₂ t₀ γ₁ γ₂ U₁ U₂) : IsChartClockData ψ η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁ γ₂ U₁ U₂ := by
  obtain ⟨c₁, c₂, hm₁, hi₁, hm₂, hi₂, hH₁, hH₂, he₁, he₂⟩ := h
  refine ⟨c₁, c₂, hm₁, hi₁, hm₂, hi₂, hH₁, hH₂, fun u hu => ?_, fun u hu => ?_⟩
  · have hc : c₁ u ∈ {s : ℝ≥0 | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁} := hi₁ ▸ mem_image_of_mem c₁ hu
    rw [← ha₁ _ hc.2]; exact he₁ u hu
  · have hc : c₂ u ∈ {t : ℝ≥0 | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂} := hi₂ ▸ mem_image_of_mem c₂ hu
    rw [← ha₂ _ hc.2]; exact he₂ u hu

/-! ### The canonical clock data on `Ω` -/

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The canonical W8.1 clock data**, almost surely: at a first contact with a nonempty continuation, the chart path
`γᵢ` is the canonical forward-limit chart path of the continuation (`cPath d univ …`) read through its inverse
relative capacity clock, and `Uᵢ` is its capacity lifetime. -/
def PairData.IsCanonClock (d : PairData Ω) (P : Measure Ω) (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ d.E →
    ((d.s₀ ω : ℝ≥0∞) < d.ζ₁ ω →
      (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ ω → γ₁ ω u = cPath d univ d.s₀ d.η₁ d.ζ₁ ω
        (invClock (chartClock (cPath d univ d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω) u)) ∧
      U₁ ω = capLife (chartClock (cPath d univ d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω)) ∧
    ((d.t₀ ω : ℝ≥0∞) < d.ζ₂ ω →
      (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ ω → γ₂ ω u = cPath d univ d.t₀ d.η₂ d.ζ₂ ω
        (invClock (chartClock (cPath d univ d.t₀ d.η₂ d.ζ₂ ω)) (d.ζ₂ ω - d.t₀ ω) u)) ∧
      U₂ ω = capLife (chartClock (cPath d univ d.t₀ d.η₂ d.ζ₂ ω)) (d.ζ₂ ω - d.t₀ ω))

/-- **The W8.1 clocks, measurably** (Aux. lemma 76, (W8.1)): for two flow lines and measurable pair data agreeing
with them, there are measurable chart paths `γᵢ` with measurable capacity lifetimes `Uᵢ`, continuous on `[0, Uᵢ]` for
every `ω`, almost surely canonical (`IsCanonClock`), which almost surely give the clock data `IsChartClockData` in
the canonical chart inverse at every first contact with two nonempty continuations. -/
theorem exists_canonClock (hA : Theorem15.Aux25Statement.{u}) (h77 : Supp10.Lemma77Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t) :
    ∃ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞), (∀ t, Measurable fun ω => γ₁ ω t) ∧
      (∀ t, Measurable fun ω => γ₂ ω t) ∧ Measurable U₁ ∧ Measurable U₂ ∧
      (∀ ω, ContinuousOn (γ₁ ω) {u | (u : ℝ≥0∞) ≤ U₁ ω}) ∧
      (∀ ω, ContinuousOn (γ₂ ω) {u | (u : ℝ≥0∞) ≤ U₂ ω}) ∧ d.IsCanonClock P γ₁ γ₂ U₁ U₂ ∧
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        IsChartClockData (d.inv ω) (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ (γ₁ ω) (γ₂ ω) (U₁ ω) (U₂ ω) := by
  subst hζ₁ hζ₂
  classical
  -- the almost sure good event and a measurable full-measure part of it
  set Good : Set Ω := {ω | ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω t = η₂ ω t) ∧ IsPathGood (η₁ ω) (d.ζ₁ ω) x₁ ∧
      IsPathGood (η₂ ω) (d.ζ₂ ω) x₂ ∧
      ((∃ s t : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω ∧ (t : ℝ≥0∞) ≤ d.ζ₂ ω ∧ η₁ ω s = η₂ ω t) →
        ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (d.ζ₁ ω) (η₂ ω) (d.ζ₂ ω) s₀ t₀ ∧
          (∀ s : ℝ≥0, s₀ ≤ s → (s : ℝ≥0∞) ≤ d.ζ₁ ω →
            η₁ ω s ∈ closure (activeDomain (η₁ ω) s₀ (η₂ ω) t₀)) ∧
          ∀ t : ℝ≥0, t₀ ≤ t → (t : ℝ≥0∞) ≤ d.ζ₂ ω →
            η₂ ω t ∈ closure (activeDomain (η₁ ω) s₀ (η₂ ω) t₀))} with hGood
  have haeGood : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [hae, ae_isPathGood_of_isFlowLine hA hκ hκ4 hη₁, ae_isPathGood_of_isFlowLine hA hκ hκ4 hη₂,
      h77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ d.ζ₁ d.ζ₂ hη₁ hη₂] with ω h1 h2 h3 h4
    exact ⟨h1.1, h1.2.1, h1.2.2, h2, h3, h4⟩
  set G' : Set Ω := (toMeasurable P Goodᶜ)ᶜ with hG'
  have hG'm : MeasurableSet G' := (measurableSet_toMeasurable P _).compl
  have hG'sub : G' ⊆ Good := fun ω hω => by
    by_contra h'
    exact hω (subset_toMeasurable P _ h')
  have hG'ae : ∀ᵐ ω ∂P, ω ∈ G' := by
    rw [ae_iff]
    have : {ω | ¬ ω ∈ G'} = toMeasurable P Goodᶜ := by ext ω; simp [hG']
    rw [this, measure_toMeasurable]
    exact ae_iff.1 haeGood
  -- the clock hypotheses for `d`'s paths at `d`'s first contact
  have hcg : ∀ ω ∈ G' ∩ d.E,
      IsContinuationGood (d.η₁ ω) (d.ζ₁ ω) (d.s₀ ω) (d.η₂ ω) (d.ζ₂ ω) (d.t₀ ω) ∧
      IsContinuationGood (d.η₂ ω) (d.ζ₂ ω) (d.t₀ ω) (d.η₁ ω) (d.ζ₁ ω) (d.s₀ ω) := by
    rintro ω ⟨hωG, hωE⟩
    obtain ⟨-, ha₁, ha₂, hp₁, hp₂, h7⟩ := hG'sub hωG
    have hfd := hd.isFirstContact hωE
    have hfo := (isFirstContact_congr ha₁ ha₂).1 hfd
    obtain ⟨s₀', t₀', hf', hc₁, hc₂⟩ := h7 ⟨_, _, hfo.1, hfo.2.1, hfo.2.2.1⟩
    obtain ⟨rfl, rfl⟩ := Sec7.IsFirstContact.unique hf' hfo
    have g₁ := isContinuationGood_of_isPathGood hp₁ hp₂ hf' hc₁
    have g₂ := isContinuationGood_of_isPathGood hp₂ hp₁ (IsFirstContact.swap hf') fun t ht htζ => by
      rw [activeDomain_comm]; exact hc₂ t ht htζ
    exact ⟨g₁.congr ha₁ ha₂, g₂.congr ha₂ ha₁⟩
  set E₁ : Set Ω := G' ∩ d.E ∩ {ω | (d.s₀ ω : ℝ≥0∞) < d.ζ₁ ω} with hE₁
  set E₂ : Set Ω := G' ∩ d.E ∩ {ω | (d.t₀ ω : ℝ≥0∞) < d.ζ₂ ω} with hE₂
  have hchart : ∀ ω ∈ d.E,
      IsFirstContactChart (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) (d.fwd ω) (d.inv ω) (d.lift ω) :=
    fun ω hω => (hd.isFirstContactChart hω).2
  have hseed : ∀ ω ∈ d.E, (d.η₁ ω 0).im = 0 ∧ (d.η₂ ω 0).im = 0 := fun ω hω =>
    ⟨(hd.good ω hω.1).2.2.2.2.1, (hd.good ω hω.1).2.2.2.2.2.1⟩
  have hp : ∀ ω ∈ d.E, d.η₁ ω (d.s₀ ω) = d.η₂ ω (d.t₀ ω) := fun ω hω => (hd.isFirstContact hω).2.2.1
  have hs₁ : IsContSpec d E₁ d.s₀ d.η₁ d.ζ₁ := by
    refine ⟨(hG'm.inter hd.measurableSet_E).inter
      (measurableSet_lt (measurable_coe_nnreal_ennreal.comp hd.measurable_s₀) hd.measζ₁),
      fun ω hω => hω.1.2, hd.measurable_s₀, hd.measζ₁, hd.meas₁, fun ω hω => (hd.good ω hω.1.2.1).1,
      fun ω hω => hω.2, fun ω hω s hs hsζ => ?_, fun ω hω s hs hsζ => ?_, fun ω hω => ?_⟩
    · rw [hd.D_of_mem hω.1.2]; exact (hcg ω hω.1).1.conf s hs hsζ
    · rw [hd.D_of_mem hω.1.2]
      exact (hcg ω hω.1).1.exists_limit (hchart ω hω.1.2) (hseed ω hω.1.2).2 hs hsζ
    · exact (hchart ω hω.1.2).2.2.2.2.2.2.2.2.1
  have hs₂ : IsContSpec d E₂ d.t₀ d.η₂ d.ζ₂ := by
    refine ⟨(hG'm.inter hd.measurableSet_E).inter
      (measurableSet_lt (measurable_coe_nnreal_ennreal.comp hd.measurable_t₀) hd.measζ₂),
      fun ω hω => hω.1.2, hd.measurable_t₀, hd.measζ₂, hd.meas₂, fun ω hω => (hd.good ω hω.1.2.1).2.1,
      fun ω hω => hω.2, fun ω hω s hs hsζ => ?_, fun ω hω s hs hsζ => ?_, fun ω hω => ?_⟩
    · rw [hd.D_of_mem hω.1.2, ← activeDomain_comm]; exact (hcg ω hω.1).2.conf s hs hsζ
    · rw [hd.D_of_mem hω.1.2, ← activeDomain_comm]
      exact (hcg ω hω.1).2.exists_limit ((hchart ω hω.1.2).swap (hp ω hω.1.2)) (hseed ω hω.1.2).1 hs hsζ
    · rw [← hp ω hω.1.2]; exact (hchart ω hω.1.2).2.2.2.2.2.2.2.2.1
  have hgm : ∀ ω ∈ d.E, IsMapOut (fillH (prefixSet (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω))) (d.g ω) :=
    fun ω hω => by
      have h1 : IsMapOut (fillH (d.K ω)) (d.g ω) := ConformalImage.isMapOut_mapOut (hd.isHPHull ω)
      rwa [PairData.K_of_mem hω] at h1
  have hx₀ : ∀ ω ∈ d.E, (d.shift ω).im = 0 := fun ω hω => by
    obtain ⟨x₀, hx⟩ := (hd.isFirstContactChart hω).1
    rw [hx]; simp
  have hclk₁ : ∀ ω ∈ E₁, IsClockOn (chartClock (cPath d E₁ d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω) := by
    intro ω hω
    obtain ⟨-, ha₁, -, hp₁, -, -⟩ := hG'sub hω.1.1
    exact (hcg ω hω.1).1.isClockOn_chartClock (hchart ω hω.1.2) (hgm ω hω.1.2) (fun z => rfl)
      (hx₀ ω hω.1.2) (hseed ω hω.1.2).2
      (fun s hs => by rw [image_Icc_congr ha₁ hs.le]; exact hp₁.hcapSet hs) hω.2
      (hs₁.continuous_cPath hd ω).continuousOn (fun r _ => (hs₁.cPath_spec hω r).1)
      (fun r hr => by rw [(hs₁.cPath_spec hω r).2.2.1, contTime_of_le hr]) (hs₁.cPath_zero hω)
  have hclk₂ : ∀ ω ∈ E₂, IsClockOn (chartClock (cPath d E₂ d.t₀ d.η₂ d.ζ₂ ω)) (d.ζ₂ ω - d.t₀ ω) := by
    intro ω hω
    obtain ⟨-, -, ha₂, -, hp₂, -⟩ := hG'sub hω.1.1
    exact (hcg ω hω.1).2.isClockOn_chartClock ((hchart ω hω.1.2).swap (hp ω hω.1.2))
      (by rw [prefixSet_comm]; exact hgm ω hω.1.2) (fun z => rfl) (hx₀ ω hω.1.2) (hseed ω hω.1.2).1
      (fun s hs => by rw [image_Icc_congr ha₂ hs.le]; exact hp₂.hcapSet hs) hω.2
      (hs₂.continuous_cPath hd ω).continuousOn (fun r _ => (hs₂.cPath_spec hω r).1)
      (fun r hr => by rw [(hs₂.cPath_spec hω r).2.2.1, contTime_of_le hr]) (hs₂.cPath_zero hω)
  obtain ⟨m₁, mU₁, c₁, e₁⟩ := hs₁.clockData hd hclk₁
  obtain ⟨m₂, mU₂, c₂, e₂⟩ := hs₂.clockData hd hclk₂
  refine ⟨cGamma d E₁ d.s₀ d.η₁ d.ζ₁, cGamma d E₂ d.t₀ d.η₂ d.ζ₂, cLife d E₁ d.s₀ d.η₁ d.ζ₁,
    cLife d E₂ d.t₀ d.η₂ d.ζ₂, m₁, m₂, mU₁, mU₂, c₁, c₂, ?_, ?_⟩
  · filter_upwards [hG'ae] with ω hω hE
    refine ⟨fun hlt => ?_, fun hlt => ?_⟩
    · have hω₁ : ω ∈ E₁ := ⟨⟨hω, hE⟩, hlt⟩
      have hpu : cPath d E₁ d.s₀ d.η₁ d.ζ₁ ω = cPath d univ d.s₀ d.η₁ d.ζ₁ ω := funext fun r => by
        rw [cPath_of_mem hω₁, cPath_of_mem (mem_univ ω)]
      obtain ⟨hγ, hU⟩ := e₁ ω hω₁
      rw [hpu] at hγ hU
      exact ⟨fun u _ => by rw [hγ], hU⟩
    · have hω₂ : ω ∈ E₂ := ⟨⟨hω, hE⟩, hlt⟩
      have hpu : cPath d E₂ d.t₀ d.η₂ d.ζ₂ ω = cPath d univ d.t₀ d.η₂ d.ζ₂ ω := funext fun r => by
        rw [cPath_of_mem hω₂, cPath_of_mem (mem_univ ω)]
      obtain ⟨hγ, hU⟩ := e₂ ω hω₂
      rw [hpu] at hγ hU
      exact ⟨fun u _ => by rw [hγ], hU⟩
  · filter_upwards [hG'ae] with ω hω s₀ t₀ hfc hs₀ ht₀
    obtain ⟨hωd, ha₁, ha₂, -, -, -⟩ := hG'sub hω
    obtain ⟨hωE, rfl, rfl, -⟩ := hd.chart_spec_of_agree hωd ha₁ ha₂ hfc
    have hω₁ : ω ∈ E₁ := ⟨⟨hω, hωE⟩, hs₀⟩
    have hω₂ : ω ∈ E₂ := ⟨⟨hω, hωE⟩, ht₀⟩
    have hdata := isChartClockData_of_isClockOn (ψ := d.inv ω) (η₁ := d.η₁ ω) (η₂ := d.η₂ ω)
      (hclk₁ ω hω₁) (hclk₂ ω hω₂) hs₀.le ht₀.le
      (fun r _ => (hs₁.cPath_spec hω₁ r).1) (fun r _ => (hs₂.cPath_spec hω₂ r).1)
      (fun r hr => by rw [(hs₁.cPath_spec hω₁ r).2.2.1, contTime_of_le hr])
      (fun r hr => by rw [(hs₂.cPath_spec hω₂ r).2.2.1, contTime_of_le hr])
    rw [← (e₁ ω hω₁).1, ← (e₁ ω hω₁).2, ← (e₂ ω hω₂).1, ← (e₂ ω hω₂).2] at hdata
    exact isChartClockData_congr ha₁ ha₂ hdata

end Restart

end InteractingSLE
