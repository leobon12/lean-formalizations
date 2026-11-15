/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartGauss
import InteractingSLE.Spec.Restart.ChartSpace

/-!
# The restart carrier from the first-contact chart data

Packet PROVE-RESTART-CPL2. This file proves the restart carrier `FirstContactRestartStatement` (`Carrier.lean`) from
one named proposition, `FirstContactChartDataStatement`, which keeps only what is specific to the first contact and
states it on the original probability space, without any canonical space or kernel construction:

* the **retained first-contact history** `𝒢` (a sub-σ-algebra), the meeting branch `M ∈ 𝒢`, the chart datum `β`
  (`𝒢`-measurable, a sorted word on `M`), the chart field `Hc` and the two chart continuations `γᵢ` with their relative
  lifetimes `Uᵢ` (measurable; almost surely on `M` continuous on `[0, Uᵢ]`);
* **(pathwise)** almost surely, at every first contact with two nonempty continuations, `ω ∈ M` and the chart
  continuation (`IsChartContinuation`) holds for `(Hc ω, γᵢ ω, Uᵢ ω)` (Lemma 7.7, Aux. 73, 75, 76, 80, (W8.1));
* **(R1) on `Ω`**: conditionally on `𝒢`, on `M`, the chart field has the Gaussian characteristic functional of the
  GFF on `ℍ` with datum `β` (Lemma 7.8, p. 290; W8, p. 539; "The selected Gaussian kernel and canonical finite
  word", p. 540–541), for every test function;
* **(R2′)**: a Markov kernel disintegrating the joint law of `β` and the coded restart variable on `M` (together with an
  extra coordinate `Y` of the input's choice, room for the witnesses of the flow lines, such as relative driver codes)
  under which, for almost every datum, the two coded continuations are the angle-`θᵢ` flow lines of the coded field
  ("The actual stopped continuation kernels", W8, p. 541).

Everything else in the carrier is proved here: the canonical space `RestartSpace × E` with restart coordinates at
every point (`ChartSpace.lean`), the measurability of the restart variable, and (R1) under the kernel from (R1) on
`Ω` (`ae_isGFFWithBoundaryData_of_condExp`, `ChartGauss.lean`).

## Main results

* `IsChartContinuation.congr_paths`: the chart continuation sees the chart paths only on `[0, Uᵢ]`;
* `FirstContactChartDataStatement`: the named first-contact input;
* **`firstContactRestartStatement_of_chartData`**:
  `FirstContactChartDataStatement.{u} → FirstContactRestartStatement.{u}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

/-- The chart continuation sees the chart paths only on their closed available intervals. -/
theorem IsChartContinuation.congr_paths {κ : ℝ} {h H : LQGMetric.DistOn upperHalfPlaneOpens}
    {η₁ : ℝ≥0 → ℂ} {ζ₁ : ℝ≥0∞} {s₀ : ℝ≥0} {η₂ : ℝ≥0 → ℂ} {ζ₂ : ℝ≥0∞} {t₀ : ℝ≥0}
    {γ₁ γ₂ γ₁' γ₂' : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞}
    (hC : IsChartContinuation κ h H η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁ γ₂ U₁ U₂)
    (h₁ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → γ₁' u = γ₁ u) (h₂ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → γ₂' u = γ₂ u) :
    IsChartContinuation κ h H η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁' γ₂' U₁ U₂ := by
  obtain ⟨φ, ψ, lift, c₁, c₂, hA, hB, hφψ, hψ, hl, hd, hT, hm₁, hi₁, hm₂, hi₂, he₁, he₂⟩ := hC
  exact ⟨φ, ψ, lift, c₁, c₂, hA, hB, hφψ, hψ, hl, hd, hT, hm₁, hi₁, hm₂, hi₂,
    fun u hu => by rw [h₁ u hu]; exact he₁ u hu, fun u hu => by rw [h₂ u hu]; exact he₂ u hu⟩

/-- **The first-contact chart data** for given objects (the conjuncts of `FirstContactChartDataStatement`): `𝒢` is a
sub-σ-algebra of the ambient `mΩ` (declared after `𝒢`, so that it is the instance used for measurability on `Ω`),
`M ∈ 𝒢`, the datum `β` is `𝒢`-measurable and sorted on `M`, the chart field `Hc`, the chart continuations `γᵢ` and
their lifetimes `Uᵢ` are measurable and the continuations almost surely on `M` continuous on `[0, Uᵢ]`; (R1 on `Ω`)
the conditional characteristic functional given `𝒢` of the chart field is Gaussian with the word mean of `β` on
`M`; `K` disintegrates the joint law of `β` and the coded restart variable on `M`, together with an extra measurable
coordinate `Y` (room for the witnesses of the flow lines under the kernel, e.g. codes of the relative drivers);
(R2′) under almost every `K c` the coded continuations are the flow lines of the coded field with datum `c`;
(pathwise) almost surely at every first contact with nonempty continuations, `ω ∈ M` and the chart continuation
holds. -/
def IsFirstContactChartData (κ θ₁ θ₂ : ℝ) {Ω : Type*} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
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
      ω ∈ M ∧ IsChartContinuation κ (h ω) (Hc ω) (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀
        (γ₁ ω) (γ₂ ω) (U₁ ω) (U₂ ω)

/-- **Named input: the first-contact chart data** (Lemma 7.8, p. 290, and Theorem W8, pp. 538–541, at the first
contact; the source inputs are listed in the module docstring). Same binders as `FirstContactRestartStatement`: the
retained first-contact history `𝒢`, the meeting branch, the chart datum, the chart field, the chart continuations
with their lifetimes, an extra coordinate `Y` in a space `E : Type` and the restart kernel exist with
`IsFirstContactChartData`. -/
def FirstContactChartDataStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∃ (𝒢 : MeasurableSpace Ω) (M : Set Ω) (β : Ω → BoundaryWord)
      (Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞)
      (E : Type) (_ : MeasurableSpace E) (Y : Ω → E) (K : Kernel BoundaryWord (RestartSpace × E)),
      IsFirstContactChartData κ θ₁ θ₂ 𝒢 P h η₁ η₂ ζ₁ ζ₂ M β Hc γ₁ γ₂ U₁ U₂ Y K

/-- **The restart carrier from the first-contact chart data.** The canonical space is `RestartSpace × E`, the
restart variable is the code of the chart field and the chart continuations together with the extra coordinate, and
(R1) under the kernel is `ae_isGFFWithBoundaryData_of_condExp`. -/
theorem firstContactRestartStatement_of_chartData (hD : FirstContactChartDataStatement.{u}) :
    FirstContactRestartStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  obtain ⟨𝒢, M, β, Hc, γ₁, γ₂, U₁, U₂, E, _, Y, K, h𝒢, hM, hβ, hsort, hHc, hγ₁, hγ₂, hU₁, hU₂, hY, hcont,
    hG, hK, hlaw, hflow, hpath⟩ := hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  -- the ambient σ-algebra is again the most recent instance (the obtained `𝒢` would otherwise be used)
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
    refine ⟨hωM, hC.congr_paths (fun u hu => ?_) (fun u hu => ?_)⟩
    · exact RestartSpace.path₁_mk' _ (hcω hωM).1 _ _ hu
    · exact RestartSpace.path₂_mk' _ _ _ (hcω hωM).2 hu

end Restart

end InteractingSLE
