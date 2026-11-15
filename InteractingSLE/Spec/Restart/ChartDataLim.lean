/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartReduce
import InteractingSLE.Spec.Restart.ChartDataPath
import InteractingSLE.Spec.Sec7.ContinuityProb2Join

/-!
# The restart carrier with chart limits from the first-contact chart data

Packet PROVE-RESTART-CPL3. The landed target `Theorem15D5.FirstContactRestartLimStatement` (D.5, interface 2 with the
active prime end; `planning/handoffs/PROVE-T15-D5.md`) is reduced, exactly as PROVE-RESTART-CPL2 reduced
`Restart.FirstContactRestartStatement`, to one Ω-level named proposition `FirstContactChartDataLimStatement`: the
first-contact chart data `IsFirstContactChartData` with `Theorem15D5.IsChartContinuationLim` in place of
`IsChartContinuation` in the pathwise conjunct (`firstContactRestartLimStatement_of_chartDataLim`).

The chart limits themselves cost nothing once the chart is the first-contact chart of `ChartDataChart.lean`:
`isChartContinuationLim_of_isFirstContactChart` derives them from the plain chart continuation relation
`ηᵢ ∘ cᵢ = ψ ∘ γᵢ`, with `γᵢ` in `ℍ̄`, the confinement of Lemma 7.7 and simple prefixes (Aux. 25).

## Main results

* `IsChartContinuationLim.congr_paths`: the chart limits see the chart paths only on `[0, Uᵢ]`;
* `IsFirstContactChartDataLim`, `FirstContactChartDataLimStatement`;
* **`firstContactRestartLimStatement_of_chartDataLim`**;
* `firstContactChartDataStatement_of_lim`: the Lim form implies PROVE-RESTART-CPL2's chart data;
* **`isChartContinuationLim_of_isFirstContactChart`**;
* `ae_mem_Hbar_of_isFlowLine`; **`ae_exists_isChartContinuationLim`**: for flow lines, from Lemma 7.7's confinement and
  Aux. 25, almost surely at every first contact the chart exists and every chart field and clocks give chart paths
  with `IsChartContinuationLim`;
* `IsChartContinuationFC`, `FirstContactChartDataFCStatement`, **`firstContactChartDataLimStatement_of_fc`**: the chart
  limits cost nothing once the chart is a first-contact chart (given Lemma 7.7's confinement and Aux. 25).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart

open Theorem15D5

/-- The chart continuation with chart limits sees the chart paths only on their closed available intervals. -/
theorem IsChartContinuationLim.congr_paths {κ : ℝ} {h H : LQGMetric.DistOn upperHalfPlaneOpens}
    {η₁ : ℝ≥0 → ℂ} {ζ₁ : ℝ≥0∞} {s₀ : ℝ≥0} {η₂ : ℝ≥0 → ℂ} {ζ₂ : ℝ≥0∞} {t₀ : ℝ≥0}
    {γ₁ γ₂ γ₁' γ₂' : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞}
    (hC : IsChartContinuationLim κ h H η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁ γ₂ U₁ U₂)
    (h₁ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → γ₁' u = γ₁ u) (h₂ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → γ₂' u = γ₂ u) :
    IsChartContinuationLim κ h H η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁' γ₂' U₁ U₂ := by
  obtain ⟨φ, ψ, lift, c₁, c₂, hA, hB, hφψ, hψ, hl, hd, hT, hm₁, hi₁, hm₂, hi₂, he₁, he₂, hL₁, hL₂⟩ := hC
  exact ⟨φ, ψ, lift, c₁, c₂, hA, hB, hφψ, hψ, hl, hd, hT, hm₁, hi₁, hm₂, hi₂,
    fun u hu => by rw [h₁ u hu]; exact he₁ u hu, fun u hu => by rw [h₂ u hu]; exact he₂ u hu,
    fun u hu => by rw [h₁ u hu.le]; exact hL₁ u hu, fun u hu => by rw [h₂ u hu.le]; exact hL₂ u hu⟩

/-- **The first-contact chart data with chart limits**: `IsFirstContactChartData` (PROVE-RESTART-CPL2) with the
pathwise conjunct strengthened to `Theorem15D5.IsChartContinuationLim`. Binder order as in `IsFirstContactChartData`
(`𝒢` before the ambient `mΩ`). -/
def IsFirstContactChartDataLim (κ θ₁ θ₂ : ℝ) {Ω : Type*} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord) (Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞) {E : Type*} [MeasurableSpace E] (Y : Ω → E)
    (K : Kernel BoundaryWord (RestartSpace × E)) : Prop :=
  𝒢 ≤ mΩ ∧ MeasurableSet[𝒢] M ∧ Measurable[𝒢] β ∧ (∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted) ∧
    Measurable Hc ∧ (∀ t : ℝ≥0, Measurable fun ω => γ₁ ω t) ∧ (∀ t : ℝ≥0, Measurable fun ω => γ₂ ω t) ∧
    Measurable U₁ ∧ Measurable U₂ ∧ Measurable Y ∧
    (∀ᵐ ω ∂P, ω ∈ M → ContinuousOn (γ₁ ω) {u | (u : ℝ≥0∞) ≤ U₁ ω} ∧
      ContinuousOn (γ₂ ω) {u | (u : ℝ≥0∞) ≤ U₂ ω}) ∧
    (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ) ∧
    IsMarkovKernel K ∧
    (P.restrict M).map (fun ω => (β ω, (RestartSpace.mk' (Hc ω) (γ₁ ω) (U₁ ω) (γ₂ ω) (U₂ ω), Y ω))) =
      (P.restrict M).map β ⊗ₘ K ∧
    (∀ᵐ c ∂(P.restrict M).map β,
      IsFlowLine κ c.fn c.jumps 0 θ₁ (K c) (fun s => s.1.field) (fun s => s.1.path₁) (fun s => s.1.life₁) ∧
      IsFlowLine κ c.fn c.jumps 0 θ₂ (K c) (fun s => s.1.field) (fun s => s.1.path₂) (fun s => s.1.life₂)) ∧
    ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
      (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
      ω ∈ M ∧ IsChartContinuationLim κ (h ω) (Hc ω) (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀
        (γ₁ ω) (γ₂ ω) (U₁ ω) (U₂ ω)

/-- **Named input: the first-contact chart data with chart limits** (Lemma 7.8, p. 290; Theorem W8, pp. 538–541;
Aux. 80; D.5, interface 2). Same binders and witnesses as `FirstContactChartDataStatement`, with
`IsFirstContactChartDataLim`. -/
def FirstContactChartDataLimStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∃ (𝒢 : MeasurableSpace Ω) (M : Set Ω) (β : Ω → BoundaryWord)
      (Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞)
      (E : Type) (_ : MeasurableSpace E) (Y : Ω → E) (K : Kernel BoundaryWord (RestartSpace × E)),
      IsFirstContactChartDataLim κ θ₁ θ₂ 𝒢 P h η₁ η₂ ζ₁ ζ₂ M β Hc γ₁ γ₂ U₁ U₂ Y K

/-- **The restart carrier with chart limits from the chart data with chart limits** (the proof of
`firstContactRestartStatement_of_chartData`, with the chart limits carried along). -/
theorem firstContactRestartLimStatement_of_chartDataLim (hD : FirstContactChartDataLimStatement.{u}) :
    FirstContactRestartLimStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  obtain ⟨𝒢, M, β, Hc, γ₁, γ₂, U₁, U₂, E, _, Y, K, h𝒢, hM, hβ, hsort, hHc, hγ₁, hγ₂, hU₁, hU₂, hY, hcont,
    hG, hK, hlaw, hflow, hpath⟩ := hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  -- the ambient σ-algebra is again the most recent instance
  let _ : MeasurableSpace Ω := mΩ
  set X : Ω → RestartSpace × E := fun ω => (RestartSpace.mk' (Hc ω) (γ₁ ω) (U₁ ω) (γ₂ ω) (U₂ ω), Y ω)
    with hXdef
  have hX : Measurable X := (RestartSpace.measurable_mk' hHc hγ₁ hγ₂ hU₁ hU₂).prodMk hY
  have hR1 := ae_isGFFWithBoundaryData_of_condExp h𝒢 hM hβ hsort hX (H := fun s => s.1.field)
    measurable_fst.fst hlaw hG
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := isRestartCoordinates_restartSpace
  refine ⟨RestartSpace × E, inferInstance, fun s => s.1.field, fun s => s.1.path₁, fun s => s.1.path₂,
    fun s => s.1.life₁, fun s => s.1.life₂, M, β, X, K,
    ⟨hc1.comp measurable_fst, hc2.comp measurable_fst, hc3.comp measurable_fst,
      fun t => (hc4 t).comp measurable_fst, fun t => (hc5 t).comp measurable_fst, fun s => hc6 s.1,
      fun s => hc7 s.1⟩, h𝒢 _ hM, hβ.mono h𝒢 le_rfl, hX, hK, hlaw, ?_, ?_⟩
  · filter_upwards [hR1, hflow] with c h1 h2
    exact ⟨h1, h2.1, h2.2⟩
  · filter_upwards [hpath, hcont] with ω hω hcω
    intro s₀ t₀ hfc hs ht
    obtain ⟨hωM, hC⟩ := hω s₀ t₀ hfc hs ht
    refine ⟨hωM, IsChartContinuationLim.congr_paths hC (fun u hu => ?_) (fun u hu => ?_)⟩
    · exact RestartSpace.path₁_mk' _ (hcω hωM).1 _ _ hu
    · exact RestartSpace.path₂_mk' _ _ _ (hcω hωM).2 hu

/-- The chart data with chart limits gives PROVE-RESTART-CPL2's chart data. -/
theorem firstContactChartDataStatement_of_lim (hD : FirstContactChartDataLimStatement.{u}) :
    FirstContactChartDataStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  obtain ⟨𝒢, M, β, Hc, γ₁, γ₂, U₁, U₂, E, mE, Y, K, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, hpath⟩ := hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  let _ : MeasurableSpace Ω := mΩ
  refine ⟨𝒢, M, β, Hc, γ₁, γ₂, U₁, U₂, E, mE, Y, K, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, ?_⟩
  filter_upwards [hpath] with ω hω s₀ t₀ hfc hs ht
  obtain ⟨hωM, hC⟩ := hω s₀ t₀ hfc hs ht
  exact ⟨hωM, hC.isChartContinuation⟩

/-! ### Chart limits from the first-contact chart -/

/-- **Chart limits come with the first-contact chart.** If the chart `(φ, ψ, lift)` is a first-contact chart
(`IsFirstContactChart`), `H` its chart field, `cᵢ` clocks onto the available continuations, and the chart paths
`γᵢ` (in `ℍ̄`) satisfy `ηᵢ ∘ cᵢ = ψ ∘ γᵢ` on `[0, Uᵢ]`, and if the continuations stay in the closure of the active
domain (Lemma 7.7's confinement) whose points are all regular (true for simple prefixes,
`isChartRegularPoint_of_injOn`), then the chart continuation with chart limits holds. -/
theorem isChartContinuationLim_of_isFirstContactChart {κ : ℝ} {h H : LQGMetric.DistOn upperHalfPlaneOpens}
    {η₁ : ℝ≥0 → ℂ} {ζ₁ : ℝ≥0∞} {s₀ : ℝ≥0} {η₂ : ℝ≥0 → ℂ} {ζ₂ : ℝ≥0∞} {t₀ : ℝ≥0} {γ₁ γ₂ : ℝ≥0 → ℂ}
    {U₁ U₂ : ℝ≥0∞} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ} {c₁ c₂ : ℝ≥0 → ℝ≥0}
    (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift)
    (hT : IsChartTransport (φ, ψ, lift) 1 0 (QuantumZipper.chiC κ) h H)
    (hs₀ : (s₀ : ℝ≥0∞) < ζ₁) (ht₀ : (t₀ : ℝ≥0∞) < ζ₂)
    (hreg : ∀ z ∈ closure (activeDomain η₁ s₀ η₂ t₀), IsChartRegularPoint η₁ s₀ η₂ t₀ z)
    (hconf₁ : ∀ s : ℝ≥0, s₀ ≤ s → (s : ℝ≥0∞) ≤ ζ₁ → η₁ s ∈ closure (activeDomain η₁ s₀ η₂ t₀))
    (hconf₂ : ∀ t : ℝ≥0, t₀ ≤ t → (t : ℝ≥0∞) ≤ ζ₂ → η₂ t ∈ closure (activeDomain η₁ s₀ η₂ t₀))
    (hm₁ : StrictMonoOn c₁ {u | (u : ℝ≥0∞) ≤ U₁})
    (hi₁ : c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁})
    (hm₂ : StrictMonoOn c₂ {u | (u : ℝ≥0∞) ≤ U₂})
    (hi₂ : c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂})
    (hγ₁ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → γ₁ u ∈ Hbar) (hγ₂ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → γ₂ u ∈ Hbar)
    (he₁ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → η₁ (c₁ u) = ψ (γ₁ u))
    (he₂ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → η₂ (c₂ u) = ψ (γ₂ u)) :
    IsChartContinuationLim κ h H η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁ γ₂ U₁ U₂ := by
  obtain ⟨-, -, hcl₁⟩ := clock_facts hm₁ hi₁ hs₀
  obtain ⟨-, -, hcl₂⟩ := clock_facts hm₂ hi₂ ht₀
  have hlimit : ∀ z : ℂ, z ∈ closure (activeDomain η₁ s₀ η₂ t₀) →
      ∀ w ∈ Hbar, ψ w = z → Tendsto φ (𝓝[activeDomain η₁ s₀ η₂ t₀] z) (𝓝 w) := by
    intro z hz w hw hψw
    obtain ⟨w₀, -, hlim, -, huniq⟩ := hC.2.2.2.2.2.2.2.2.2.2 z hz (hreg z hz)
    rwa [huniq w hw hψw]
  obtain ⟨hact, hbij, hφψ, hoff, hlc, hderiv, -⟩ := hC
  refine ⟨φ, ψ, lift, c₁, c₂, hact, hbij, hφψ, hoff, hlc, hderiv, hT, hm₁, hi₁, hm₂, hi₂, he₁, he₂,
    fun u hu => ?_, fun u hu => ?_⟩
  · exact hlimit _ (hconf₁ _ (hcl₁ u hu).1 (hcl₁ u hu).2.1.le) _ (hγ₁ u hu.le) (he₁ u hu.le).symm
  · exact hlimit _ (hconf₂ _ (hcl₂ u hu).1 (hcl₂ u hu).2.1.le) _ (hγ₂ u hu.le) (he₂ u hu.le).symm

/-! ### Flow lines: the pathwise chart data almost surely -/

/-- A flow line lies almost surely in `ℍ̄` on its closed available interval (its translate is a generating trace of
a driver that starts at `0` and is continuous before the lifetime). -/
theorem ae_mem_Hbar_of_isFlowLine {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ∈ Hbar := by
  obtain ⟨_, _, W, _, _, _, -, hcoup, htr⟩ := hη
  filter_upwards [htr, hcoup.1.2.2.2.2] with ω hω hpath t ht
  have := Sec7.IsGeneratingTrace.mem_Hbar hω hpath.2.2.2.1 hpath.1 ht
  have him : (η ω t - x).im = (η ω t).im := by simp
  show 0 ≤ (η ω t).im
  rw [← him]; exact this

/-- **The pathwise first-contact chart data for flow lines, almost surely** (Lemma 7.8, p. 290; Theorem W8 and
(W8.1); Aux. 80; D.5, interface 2), from Lemma 7.7's confinement (`Supp10.Lemma77Statement`) and simplicity
(`Theorem15.Aux25Statement`): almost surely, at every first contact with two nonempty continuations, the active
domain has a first-contact chart, and every chart field in it and all continuous clocks onto the available
continuations come with continuous chart paths satisfying `Theorem15D5.IsChartContinuationLim`. -/
theorem ae_exists_isChartContinuationLim (h77 : Supp10.Lemma77Statement.{u})
    (hA25 : Theorem15.Aux25Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} (h₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (h₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
      (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
      ∃ (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ), IsFirstContactChart (η₁ ω) s₀ (η₂ ω) t₀ φ ψ lift ∧
        ∀ (H : LQGMetric.DistOn upperHalfPlaneOpens) (c₁ c₂ : ℝ≥0 → ℝ≥0) (U₁ U₂ : ℝ≥0∞),
          IsChartTransport (φ, ψ, lift) 1 0 (QuantumZipper.chiC κ) (h ω) H →
          StrictMonoOn c₁ {u | (u : ℝ≥0∞) ≤ U₁} → ContinuousOn c₁ {u | (u : ℝ≥0∞) ≤ U₁} →
          c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁ ω} →
          StrictMonoOn c₂ {u | (u : ℝ≥0∞) ≤ U₂} → ContinuousOn c₂ {u | (u : ℝ≥0∞) ≤ U₂} →
          c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂ ω} →
          ∃ γ₁ γ₂ : ℝ≥0 → ℂ, ContinuousOn γ₁ {u | (u : ℝ≥0∞) ≤ U₁} ∧
            ContinuousOn γ₂ {u | (u : ℝ≥0∞) ≤ U₂} ∧
            IsChartContinuationLim κ (h ω) H (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ γ₁ γ₂ U₁ U₂ := by
  filter_upwards [h77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    Sec7.ae_continuousOn_of_isFlowLine h₁, Sec7.ae_continuousOn_of_isFlowLine h₂,
    ae_mem_Hbar_of_isFlowLine h₁, ae_mem_Hbar_of_isFlowLine h₂,
    Supp10.ae_apply_zero_of_isFlowLine h₁, Supp10.ae_apply_zero_of_isFlowLine h₂,
    Theorem15.ae_injOn_of_isFlowLine hA25 hκ hκ4 h₁, Theorem15.ae_injOn_of_isFlowLine hA25 hκ hκ4 h₂] with
    ω h7 hc₁ hc₂ hH₁ hH₂ h0₁ h0₂ hi₁ hi₂
  intro s₀ t₀ hfc hs₀ ht₀
  obtain ⟨s₀', t₀', hfc', hconf₁, hconf₂⟩ := h7 ⟨s₀, t₀, hfc.1, hfc.2.1, hfc.2.2.1⟩
  obtain ⟨rfl, rfl⟩ := Sec7.IsFirstContact.unique hfc' hfc
  have hI₁ : Icc 0 s₀' ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ ζ₁ ω} := fun s hs =>
    (ENNReal.coe_le_coe.2 hs.2).trans hfc.1
  have hI₂ : Icc 0 t₀' ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₂ ω} := fun t ht =>
    (ENNReal.coe_le_coe.2 ht.2).trans hfc.2.1
  exact exists_isChartContinuationLim hc₁ hc₂ hH₁ hH₂ (by rw [h0₁]; simp) (by rw [h0₂]; simp) hfc hs₀ ht₀
    hconf₁ hconf₂ (hi₁.mono hI₁) (hi₂.mono hI₂)

/-! ### The chart limits cost nothing: chart data in a first-contact chart -/

/-- **Chart continuation in a first-contact chart** (no limits): the chart is a first-contact chart
(`IsFirstContactChart`), `H` its chart field, `cᵢ` clocks onto the available continuations, and the chart paths
lie in `ℍ̄` with `ηᵢ ∘ cᵢ = ψ ∘ γᵢ` on `[0, Uᵢ]`. -/
def IsChartContinuationFC (κ : ℝ) (h H : LQGMetric.DistOn upperHalfPlaneOpens) (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞)
    (s₀ : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (t₀ : ℝ≥0) (γ₁ γ₂ : ℝ≥0 → ℂ) (U₁ U₂ : ℝ≥0∞) : Prop :=
  ∃ (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) (c₁ c₂ : ℝ≥0 → ℝ≥0),
    IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift ∧ IsChartTransport (φ, ψ, lift) 1 0 (QuantumZipper.chiC κ) h H ∧
    StrictMonoOn c₁ {u | (u : ℝ≥0∞) ≤ U₁} ∧
    c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁} ∧
    StrictMonoOn c₂ {u | (u : ℝ≥0∞) ≤ U₂} ∧
    c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂} ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → γ₁ u ∈ Hbar) ∧ (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → γ₂ u ∈ Hbar) ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → η₁ (c₁ u) = ψ (γ₁ u)) ∧
    ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → η₂ (c₂ u) = ψ (γ₂ u)

/-- **Named input: the first-contact chart data in a first-contact chart** (no chart limits): as
`FirstContactChartDataLimStatement`, with the pathwise conjunct `IsChartContinuationFC`. -/
def FirstContactChartDataFCStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∃ (𝒢 : MeasurableSpace Ω) (M : Set Ω) (β : Ω → BoundaryWord)
      (Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞)
      (E : Type) (_ : MeasurableSpace E) (Y : Ω → E) (K : Kernel BoundaryWord (RestartSpace × E)),
      IsFirstContactChartData κ θ₁ θ₂ 𝒢 P h η₁ η₂ ζ₁ ζ₂ M β Hc γ₁ γ₂ U₁ U₂ Y K ∧
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        IsChartContinuationFC κ (h ω) (Hc ω) (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ (γ₁ ω) (γ₂ ω) (U₁ ω) (U₂ ω)

/-- **The chart limits from a first-contact chart, for flow lines**: with Lemma 7.7's confinement and Aux. 25,
the chart data in a first-contact chart gives the chart data with chart limits. -/
theorem firstContactChartDataLimStatement_of_fc (hD : FirstContactChartDataFCStatement.{u})
    (h77 : Supp10.Lemma77Statement.{u}) (hA25 : Theorem15.Aux25Statement.{u}) :
    FirstContactChartDataLimStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  obtain ⟨𝒢, M, β, Hc, γ₁, γ₂, U₁, U₂, E, mE, Y, K, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, hpath⟩, hfc⟩ := hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  let _ : MeasurableSpace Ω := mΩ
  refine ⟨𝒢, M, β, Hc, γ₁, γ₂, U₁, U₂, E, mE, Y, K, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, ?_⟩
  filter_upwards [hpath, hfc, h77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂,
    Supp10.ae_apply_zero_of_isFlowLine hη₁, Supp10.ae_apply_zero_of_isFlowLine hη₂,
    Theorem15.ae_injOn_of_isFlowLine hA25 hκ hκ4 hη₁, Theorem15.ae_injOn_of_isFlowLine hA25 hκ hκ4 hη₂] with
    ω hω hFC h7 hc₁ hc₂ h0₁ h0₂ hi₁ hi₂
  intro s₀ t₀ hf hs₀ ht₀
  refine ⟨(hω s₀ t₀ hf hs₀ ht₀).1, ?_⟩
  obtain ⟨s₀', t₀', hf', hconf₁, hconf₂⟩ := h7 ⟨s₀, t₀, hf.1, hf.2.1, hf.2.2.1⟩
  obtain ⟨rfl, rfl⟩ := Sec7.IsFirstContact.unique hf' hf
  obtain ⟨φ, ψ, lift, c₁, c₂, hC, hT, hm₁, hc₁', hm₂, hc₂', hγ₁, hγ₂, he₁, he₂⟩ := hFC s₀' t₀' hf hs₀ ht₀
  have hI₁ : Icc 0 s₀' ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ ζ₁ ω} := fun s hs =>
    (ENNReal.coe_le_coe.2 hs.2).trans hf.1
  have hI₂ : Icc 0 t₀' ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₂ ω} := fun t ht =>
    (ENNReal.coe_le_coe.2 ht.2).trans hf.2.1
  have hmeet : ∀ s t : ℝ≥0, s ≤ s₀' → t ≤ t₀' → η₁ ω s = η₂ ω t → s = s₀' ∧ t = t₀' := fun s t hs ht he => by
    have := hf.2.2.2 s t ((ENNReal.coe_le_coe.2 hs).trans hf.1) ((ENNReal.coe_le_coe.2 ht).trans hf.2.1) he
    exact ⟨le_antisymm hs this.1, le_antisymm ht this.2⟩
  have hreg := isChartRegularPoint_of_injOn (hc₁.mono hI₁) (hc₂.mono hI₂) (by rw [h0₁]; simp)
    (by rw [h0₂]; simp) hf.2.2.1 (hi₁.mono hI₁) (hi₂.mono hI₂) hmeet
  exact isChartContinuationLim_of_isFirstContactChart hC hT hs₀ ht₀ (fun z _ => hreg z) hconf₁ hconf₂ hm₁ hc₁'
    hm₂ hc₂' hγ₁ hγ₂ he₁ he₂

end Restart

end InteractingSLE
