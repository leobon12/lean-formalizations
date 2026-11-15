/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import InteractingSLE.Frozen.Spec.IsChartTransport
import InteractingSLE.Frozen.Spec.IsActiveChart
import InteractingSLE.Frozen.Spec.activeDomain
import InteractingSLE.Spec.Restart.Datum

/-!
# The first-contact restart carrier (Lemma 7.8 / Theorem W8 under the conditional law)

Packet PROVE-RESTART-CPL. The chart-level propositions of Theorem 1.5 (`Supp10.CommonFlowAfterFirstContactStatement`,
`Supp10.ChartInteriorExclusionStatement`, `Supp10.ChartOrderAfterCrossingStatement`) each apply a theorem about
canonical flow lines to the **conditional** field of the first-contact chart and integrate the result back. Theorem
W8 (supplement pp. 538–541) supplies the conditional coupling: "On a finite meeting branch it has the canonical
surviving finite-word mean in its joint unbounded component. Every nonempty available continuation is the
corresponding angle flow of that same conditional field, with its actual original stopping rule reconstructed in
relative capacity" (W8.1); Lemma 7.8 (p. 290) at the first contact.

This file states that conclusion as a first-order proposition about one regular conditional law, the **restart
carrier** `FirstContactRestartStatement`:

* a canonical space `S` with coordinates: the chart field `H`, the two chart continuations `γᵢ` and their relative
  available lifetimes `Uᵢ` (`IsRestartCoordinates`: measurable coordinates, continuous paths on `[0, Uᵢ]`);
* on the meeting branch `M`, a measurable chart datum `β : Ω → BoundaryWord` and the restart variable `X : Ω → S`,
  with a Markov kernel `K` that is the conditional law of `X` given `β`:
  `(P|M).map (β, X) = (P|M).map β ⊗ₘ K`;
* **(R1) + (R2′)** (`IsConditionalFlowPair`): for almost every datum `c`, under `K c` the field `H` is a GFF on `ℍ`
  with boundary datum `c` and `γᵢ` (lifetime `Uᵢ`) is its angle-`θᵢ` flow line from `0` (frozen `IsGFFWithBoundaryData`,
  `IsFlowLine`);
* **pathwise** (`IsChartContinuation`): at the first contact, a common active chart `φ` of the active domain `D`, its
  inverse `ψ : ℍ → D` (with boundary values off `D`), the chart field `H(X ω)` of `h ω` (frozen `IsChartTransport`
  with a continuous branch of `arg φ′`), and capacity clocks `cᵢ` mapping `[0, Uᵢ]` increasingly onto `[s₀, ζ₁]`,
  `[t₀, ζ₂]` with `ηᵢ ∘ cᵢ = ψ ∘ γᵢ`.

It is the design of `planning/handoffs/PROVE-SUPP10-B.md` with (R2) in kernel form: instead of a jointly measurable
universal flow-line map, the continuations are flow lines of the conditional field under the conditional law. This
is not a second-order "transfer" statement (pitfall of that handoff): it is a property of one kernel, and only
**measurable** events are integrated back (`ae_mem_of_compProd_eq`).

The proof of the carrier from the frozen coupling is left to later packets (handoff of PROVE-RESTART-CPL).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

/-! ### Integrating a kernel event back -/

/-- **Integrating a measurable event of the conditional law.** If `K` is the conditional law of `X` given `β` on `M`
(`(P|M).map (β, X) = (P|M).map β ⊗ₘ K`) and a measurable event `E` has `K c`-probability one for almost every value
`c` of `β`, then almost surely on `M`, `X ∈ E`. -/
theorem ae_mem_of_compProd_eq {Ω C S : Type*} [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace S]
    {P : Measure Ω} [IsFiniteMeasure P] {M : Set Ω} (hM : MeasurableSet M) {β : Ω → C} {X : Ω → S}
    (hβ : Measurable β) (hX : Measurable X) {K : Kernel C S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    {E : Set S} (hE : MeasurableSet E) (hK : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), s ∈ E) :
    ∀ᵐ ω ∂P, ω ∈ M → X ω ∈ E := by
  have hKc : ∀ᵐ c ∂(P.restrict M).map β, K c Eᶜ = 0 := by
    filter_upwards [hK] with c hc
    exact (ae_iff.1 hc)
  have hzero : (P.restrict M) (X ⁻¹' Eᶜ) = 0 := by
    have hpre : (fun ω => (β ω, X ω)) ⁻¹' (univ ×ˢ Eᶜ) = X ⁻¹' Eᶜ := by
      ext ω
      simp
    rw [← hpre, ← Measure.map_apply (hβ.prodMk hX) (MeasurableSet.univ.prod hE.compl), hlaw,
      Measure.compProd_apply_prod MeasurableSet.univ hE.compl, Measure.restrict_univ]
    exact lintegral_eq_zero_of_ae_eq_zero hKc
  rw [← ae_restrict_iff' hM]
  exact ae_iff.2 hzero

/-! ### The carrier -/

/-- The restart coordinates on the canonical space `S`: the chart field `H`, the chart continuations `γᵢ` and their
relative available lifetimes `Uᵢ` are measurable (each time coordinate of `γᵢ`), and every continuation is continuous
on its closed available interval `[0, Uᵢ]` (its finite endpoint included, as for the frozen `IsGeneratingTrace`). -/
def IsRestartCoordinates {S : Type*} [MeasurableSpace S]
    (H : S → LQGMetric.DistOn upperHalfPlaneOpens) (γ₁ γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) : Prop :=
  Measurable H ∧ Measurable U₁ ∧ Measurable U₂ ∧ (∀ t : ℝ≥0, Measurable fun s => γ₁ s t) ∧
    (∀ t : ℝ≥0, Measurable fun s => γ₂ s t) ∧
    (∀ s, ContinuousOn (γ₁ s) {u | (u : ℝ≥0∞) ≤ U₁ s}) ∧
    ∀ s, ContinuousOn (γ₂ s) {u | (u : ℝ≥0∞) ≤ U₂ s}

/-- **(R1) + (R2′), the conditional coupling at one datum** (W8, p. 539: "On a finite meeting branch it has the
canonical surviving finite-word mean in its joint unbounded component. Every nonempty available continuation is the
corresponding angle flow of that same conditional field"): under the law `Q`, the field `H` is a GFF on `ℍ` whose
boundary datum is the word `c`, and `γᵢ`, with available lifetime `Uᵢ`, is its angle-`θᵢ` flow line from the common
seed `0`. -/
def IsConditionalFlowPair (κ θ₁ θ₂ : ℝ) (c : BoundaryWord) {S : Type*} [MeasurableSpace S]
    (Q : Measure S) (H : S → LQGMetric.DistOn upperHalfPlaneOpens) (γ₁ γ₂ : S → ℝ≥0 → ℂ)
    (U₁ U₂ : S → ℝ≥0∞) : Prop :=
  IsGFFWithBoundaryData Q H c.fn c.jumps ∧ IsFlowLine κ c.fn c.jumps 0 θ₁ Q H γ₁ U₁ ∧
    IsFlowLine κ c.fn c.jumps 0 θ₂ Q H γ₂ U₂

/-- **The pathwise part of the restart at a first contact** `(s₀, t₀)` (Lemma 7.8, p. 290: "`φ : D → ℍ` fix
infinity"; W7–W8, pp. 538–541; (W8.1)). With `D = activeDomain η₁ s₀ η₂ t₀`:
* `φ` is a common active chart of `D` centred at the contact point, and `ψ` is its inverse on `ℍ`, a bijection
  `ℍ → D`, whose values off `ℍ` lie off `D` (boundary values of the inverse chart);
* `H` is the field `h` written in the chart (frozen `IsChartTransport` with `σ = 1`, `a = 0`, `k = χ`, coordinate
  rule (1.4)), for a continuous branch `lift` of `arg φ′` on `D`;
* the capacity clocks `cᵢ` are strictly increasing and map `[0, Uᵢ]` onto the physical available continuations
  `[s₀, ζ₁]`, `[t₀, ζ₂]`, and the physical continuations are the inverse-chart images of the chart continuations:
  `ηᵢ ∘ cᵢ = ψ ∘ γᵢ` on `[0, Uᵢ]`. -/
def IsChartContinuation (κ : ℝ) (h H : LQGMetric.DistOn upperHalfPlaneOpens) (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞)
    (s₀ : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (t₀ : ℝ≥0) (γ₁ γ₂ : ℝ≥0 → ℂ) (U₁ U₂ : ℝ≥0∞) : Prop :=
  ∃ (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) (c₁ c₂ : ℝ≥0 → ℝ≥0),
    IsActiveChart (activeDomain η₁ s₀ η₂ t₀) (η₁ s₀) φ ∧
    BijOn ψ QuantumZipper.H (activeDomain η₁ s₀ η₂ t₀) ∧ (∀ w ∈ QuantumZipper.H, φ (ψ w) = w) ∧
    (∀ w ∉ QuantumZipper.H, ψ w ∉ activeDomain η₁ s₀ η₂ t₀) ∧
    ContinuousOn lift (activeDomain η₁ s₀ η₂ t₀) ∧
    (∀ z ∈ activeDomain η₁ s₀ η₂ t₀,
      deriv φ z = (‖deriv φ z‖ : ℂ) * Complex.exp (Complex.I * (lift z : ℂ))) ∧
    IsChartTransport (φ, ψ, lift) 1 0 (QuantumZipper.chiC κ) h H ∧
    StrictMonoOn c₁ {u | (u : ℝ≥0∞) ≤ U₁} ∧
    c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁} ∧
    StrictMonoOn c₂ {u | (u : ℝ≥0∞) ≤ U₂} ∧
    c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂} ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → η₁ (c₁ u) = ψ (γ₁ u)) ∧
    ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → η₂ (c₂ u) = ψ (γ₂ u)

/-- **The first-contact restart carrier** (Lemma 7.8, p. 290, and Theorem W8, pp. 538–541, at the first contact,
for the original flows stopped at their available lifetimes `ζᵢ`). For flow lines from `x₂ < x₁` with
`θ₁ < θ₂ + π` there are a canonical space `S` with restart coordinates `(H, γ₁, γ₂, U₁, U₂)`, a measurable event `M`
containing the meeting branch (first contact with two nonempty continuations), a measurable chart datum `β` and
restart variable `X`, and a Markov kernel `K`, such that:
* `K` is the conditional law of `X` given `β` on `M`;
* for almost every datum `c`, under `K c` the chart field is a GFF with datum `c` and the continuations are its
  angle-`θ₁` and angle-`θ₂` flow lines from `0` (`IsConditionalFlowPair`);
* almost surely, at every first contact with two nonempty continuations, `ω ∈ M` and the chart, inverse chart,
  chart field and capacity clocks of `IsChartContinuation` exist for `X ω`.

The canonical space is `Type` (universe `0`): it is built from standard Borel coordinate spaces. -/
def FirstContactRestartStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∃ (S : Type) (_ : MeasurableSpace S) (H : S → LQGMetric.DistOn upperHalfPlaneOpens)
      (γ₁ γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord) (X : Ω → S)
      (K : Kernel BoundaryWord S),
      IsRestartCoordinates H γ₁ γ₂ U₁ U₂ ∧ MeasurableSet M ∧ Measurable β ∧ Measurable X ∧
      IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β, IsConditionalFlowPair κ θ₁ θ₂ c (K c) H γ₁ γ₂ U₁ U₂) ∧
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        ω ∈ M ∧ IsChartContinuation κ (h ω) (H (X ω)) (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀
          (γ₁ (X ω)) (γ₂ (X ω)) (U₁ (X ω)) (U₂ (X ω))

end Restart

end InteractingSLE
