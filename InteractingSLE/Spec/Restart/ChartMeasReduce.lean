/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartMeasFlow

/-!
# `FirstContactChartDataFCStatement` with the measurable chart supplied

Packet PROVE-RESTART-CPL4. CPL3 reduced `Theorem15D5.FirstContactRestartLimStatement` to
`FirstContactChartDataFCStatement` (with Lemma 7.7 and Aux. 25). Here the **measurable choice of the chart and of the
chart field** (item 1 of CPL3's "What remains") is supplied: `FirstContactChartDataFCStatement` follows from Lemma
7.7's confinement and the named input `FirstContactKernelCanonStatement`, which is the same statement with

* the chart field fixed to the canonical measurable one, `Hc = hd.chartField κ h` (`ChartMeas.lean`), for any
  measurable versions `d` of the paths (`ChartMeasFlow.lean`), and
* the pathwise conjunct reduced to the **clock data** `IsChartClockData` in the canonical chart inverse `d.inv`
  (clocks, chart paths in `ℍ̄`, `ηᵢ ∘ cᵢ = ψ ∘ γᵢ`): the first-contact chart and the chart transport are proved here
  (`IsMeasGood.chart_spec_of_agree`, `IsMeasGood.isChartTransport_chartField`).

The named input keeps exactly CPL3's remaining items 2–3: the chart paths with the relative capacity clocks (W8.1) and
their measurability, (R1) on `Ω` (Lemma 7.8's kernel) and (R2′).

## Main results

* `IsChartClockData`, `isChartContinuationFC_of_clockData`, `isChartContinuation_of_clockData`;
* `IsFirstContactKernelData`, `FirstContactKernelCanonStatement`;
* **`firstContactChartDataFCStatement_of_canon`**:
  `Supp10.Lemma77Statement.{u} → FirstContactKernelCanonStatement.{u} → FirstContactChartDataFCStatement.{u}`;
* `firstContactRestartLimStatement_of_canon`: with Aux. 25, the D.5 interface
  `Theorem15D5.FirstContactRestartLimStatement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart

/-! ### Clock data and the chart continuations -/

/-- **The clock data of the two chart continuations** in a chart with inverse `ψ`: clocks `cᵢ` strictly increasing
on `[0, Uᵢ]` onto the available continuation intervals, chart paths in `ℍ̄`, and `ηᵢ ∘ cᵢ = ψ ∘ γᵢ`. -/
def IsChartClockData (ψ : ℂ → ℂ) (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (s₀ : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (t₀ : ℝ≥0)
    (γ₁ γ₂ : ℝ≥0 → ℂ) (U₁ U₂ : ℝ≥0∞) : Prop :=
  ∃ c₁ c₂ : ℝ≥0 → ℝ≥0,
    StrictMonoOn c₁ {u | (u : ℝ≥0∞) ≤ U₁} ∧ c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁} ∧
    StrictMonoOn c₂ {u | (u : ℝ≥0∞) ≤ U₂} ∧ c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂} ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → γ₁ u ∈ Hbar) ∧ (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → γ₂ u ∈ Hbar) ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → η₁ (c₁ u) = ψ (γ₁ u)) ∧ ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → η₂ (c₂ u) = ψ (γ₂ u)

variable {κ : ℝ} {h H : LQGMetric.DistOn upperHalfPlaneOpens} {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s₀ t₀ : ℝ≥0}
  {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ} {γ₁ γ₂ : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞}

theorem isChartContinuationFC_of_clockData (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift)
    (hT : IsChartTransport (φ, ψ, lift) 1 0 (QuantumZipper.chiC κ) h H)
    (hk : IsChartClockData ψ η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁ γ₂ U₁ U₂) :
    IsChartContinuationFC κ h H η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁ γ₂ U₁ U₂ := by
  obtain ⟨c₁, c₂, hm₁, hi₁, hm₂, hi₂, hγ₁, hγ₂, he₁, he₂⟩ := hk
  exact ⟨φ, ψ, lift, c₁, c₂, hC, hT, hm₁, hi₁, hm₂, hi₂, hγ₁, hγ₂, he₁, he₂⟩

theorem isChartContinuation_of_clockData (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift)
    (hT : IsChartTransport (φ, ψ, lift) 1 0 (QuantumZipper.chiC κ) h H)
    (hk : IsChartClockData ψ η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁ γ₂ U₁ U₂) :
    IsChartContinuation κ h H η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁ γ₂ U₁ U₂ := by
  obtain ⟨c₁, c₂, hm₁, hi₁, hm₂, hi₂, -, -, he₁, he₂⟩ := hk
  obtain ⟨hA, hB, hφψ, hψ, hl, hd, -⟩ := hC
  exact ⟨φ, ψ, lift, c₁, c₂, hA, hB, hφψ, hψ, hl, hd, hT, hm₁, hi₁, hm₂, hi₂, he₁, he₂⟩

/-! ### The kernel data -/

/-- **The kernel part of the first-contact chart data** (`IsFirstContactChartData` without the measurability of the
chart field and without its pathwise conjunct): the retained history `𝒢`, the meeting branch `M`, the sorted datum
`β`, measurable chart paths and lifetimes, an extra coordinate `Y`, continuity of the chart paths, (R1) on `Ω`, the
disintegrating kernel `K` and (R2′). Same binder order `(𝒢) {mΩ}` as `IsFirstContactChartData`. -/
def IsFirstContactKernelData (κ θ₁ θ₂ : ℝ) {Ω : Type*} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (M : Set Ω) (β : Ω → BoundaryWord) (Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞) {E : Type*} [MeasurableSpace E] (Y : Ω → E)
    (K : Kernel BoundaryWord (RestartSpace × E)) : Prop :=
  𝒢 ≤ mΩ ∧ MeasurableSet[𝒢] M ∧ Measurable[𝒢] β ∧ (∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted) ∧
    (∀ t : ℝ≥0, Measurable fun ω => γ₁ ω t) ∧ (∀ t : ℝ≥0, Measurable fun ω => γ₂ ω t) ∧
    Measurable U₁ ∧ Measurable U₂ ∧ Measurable Y ∧
    (∀ᵐ ω ∂P, ω ∈ M → ContinuousOn (γ₁ ω) {u | (u : ℝ≥0∞) ≤ U₁ ω} ∧
      ContinuousOn (γ₂ ω) {u | (u : ℝ≥0∞) ≤ U₂ ω}) ∧
    (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ) ∧
    IsMarkovKernel K ∧
    (P.restrict M).map (fun ω => (β ω, (RestartSpace.mk' (Hc ω) (γ₁ ω) (U₁ ω) (γ₂ ω) (U₂ ω), Y ω))) =
      (P.restrict M).map β ⊗ₘ K ∧
    ∀ᵐ c ∂(P.restrict M).map β,
      IsFlowLine κ c.fn c.jumps 0 θ₁ (K c) (fun s => s.1.field) (fun s => s.1.path₁) (fun s => s.1.life₁) ∧
      IsFlowLine κ c.fn c.jumps 0 θ₂ (K c) (fun s => s.1.field) (fun s => s.1.path₂) (fun s => s.1.life₂)

/-- **Named input: the first-contact kernel data in the canonical measurable chart** (Lemma 7.8, p. 290; Theorem W8,
pp. 538–541; (W8.1)). For two flow lines as in `FirstContactChartDataFCStatement` and **any** measurable versions `d`
of them (`PairData.IsMeasGood`, agreeing almost surely on the available intervals, the good event of full measure),
there are kernel data (`IsFirstContactKernelData`) for the canonical chart field `Hc = hd.chartField κ h` and chart
paths `γᵢ` with lifetimes `Uᵢ` such that, almost surely, at every first contact with two nonempty continuations,
`ω ∈ M` and the clock data hold in the canonical chart inverse `d.inv ω` (W8.1: the relative capacity clocks). -/
def FirstContactKernelCanonStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : PairData Ω) (hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t) →
    ∀ Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens, Hc = hd.chartField κ h →
    ∃ (𝒢 : MeasurableSpace Ω) (M : Set Ω) (β : Ω → BoundaryWord) (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞)
      (E : Type) (_ : MeasurableSpace E) (Y : Ω → E) (K : Kernel BoundaryWord (RestartSpace × E)),
      IsFirstContactKernelData κ θ₁ θ₂ 𝒢 P M β Hc γ₁ γ₂ U₁ U₂ Y K ∧
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        ω ∈ M ∧ IsChartClockData (d.inv ω) (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ (γ₁ ω) (γ₂ ω) (U₁ ω) (U₂ ω)

/-- **`FirstContactChartDataFCStatement` from the canonical kernel data**: the measurable chart, the measurable chart
field and the pathwise first-contact chart are supplied (with Lemma 7.7's confinement). -/
theorem firstContactChartDataFCStatement_of_canon (h77 : Supp10.Lemma77Statement.{u})
    (hR : FirstContactKernelCanonStatement.{u}) : FirstContactChartDataFCStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  obtain ⟨d, hd, hζ₁, hζ₂, hae⟩ := exists_pairData_of_isFlowLine h77 hκ hκ4 hb hx hθ hh hη₁ hη₂
  obtain ⟨𝒢, M, β, γ₁, γ₂, U₁, U₂, E, mE, Y, K, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩,
    hpath⟩ := hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae _ rfl
  let _ : MeasurableSpace Ω := mΩ
  -- the pathwise chart at every first contact
  have hchart : ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
      (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
      ω ∈ M ∧ IsFirstContactChart (η₁ ω) s₀ (η₂ ω) t₀ (d.fwd ω) (d.inv ω) (d.lift ω) ∧
        IsChartTransport (d.fwd ω, d.inv ω, d.lift ω) 1 0 (QuantumZipper.chiC κ) (h ω) (hd.chartField κ h ω) ∧
        IsChartClockData (d.inv ω) (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ (γ₁ ω) (γ₂ ω) (U₁ ω) (U₂ ω) := by
    filter_upwards [hae, hpath] with ω hω hp s₀ t₀ hfc hs₀ ht₀
    obtain ⟨hG, ha₁, ha₂⟩ := hω
    rw [← hζ₁] at ha₁ hfc
    rw [← hζ₂] at ha₂ hfc
    obtain ⟨-, -, -, hch, hC⟩ := hd.chart_spec_of_agree hG ha₁ ha₂ hfc
    rw [hζ₁, hζ₂] at hfc
    obtain ⟨hM, hk⟩ := hp s₀ t₀ hfc hs₀ ht₀
    have hT := hd.isChartTransport_chartField κ h ω
    rw [hch] at hT
    exact ⟨hM, hC, hT, hk⟩
  refine ⟨𝒢, M, β, hd.chartField κ h, γ₁, γ₂, U₁, U₂, E, mE, Y, K,
    ⟨h1, h2, h3, h4, hd.measurable_chartField κ hh.1, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ?_⟩, ?_⟩
  · filter_upwards [hchart] with ω hω s₀ t₀ hfc hs₀ ht₀
    obtain ⟨hM, hC, hT, hk⟩ := hω s₀ t₀ hfc hs₀ ht₀
    exact ⟨hM, isChartContinuation_of_clockData hC hT hk⟩
  · filter_upwards [hchart] with ω hω s₀ t₀ hfc hs₀ ht₀
    obtain ⟨-, hC, hT, hk⟩ := hω s₀ t₀ hfc hs₀ ht₀
    exact isChartContinuationFC_of_clockData hC hT hk

/-- **The D.5 restart-with-limits interface from the canonical kernel data** (with CPL3's reductions): Lemma 7.7,
Aux. 25 and `FirstContactKernelCanonStatement` give `Theorem15D5.FirstContactRestartLimStatement`. -/
theorem firstContactRestartLimStatement_of_canon (h77 : Supp10.Lemma77Statement.{u})
    (hA25 : Theorem15.Aux25Statement.{u}) (hR : FirstContactKernelCanonStatement.{u}) :
    Theorem15D5.FirstContactRestartLimStatement.{u} :=
  firstContactRestartLimStatement_of_chartDataLim
    (firstContactChartDataLimStatement_of_fc (firstContactChartDataFCStatement_of_canon h77 hR) h77 hA25)

end Restart

end InteractingSLE
