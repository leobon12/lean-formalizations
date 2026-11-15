/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GStepZero

/-! # Positive-time mean identification from constructed initial data

The actual time-zero harmonic distribution and the stored correction imply
(K-b) at zero. The landed old-boundary theorem then supplies growth and old
boundary cancellation; the glued slit comparison identifies every actual
conditional mean at the later time.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Complex Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GStep
open Aux61GCont Aux61FibData
open Aux61Fib (FibData FibCode)
open Aux61ChLoc (IsChartGaussAt IsChartMeanAt)
open Aux61UnionK (canonMean chartHull)
open Aux61Conf2 (IsGluedSlitSample)

universe u v
variable {X : Type u} {𝒢₀ 𝒢 : MeasurableSpace X} [mX : MeasurableSpace X]
  {β : Type*} [MeasurableSpace β] {μ : Measure X} [IsFiniteMeasure μ]
  {Z : X → β} {B : Set β} {Y : X → FibCode} {q : ℝ≥0}
  {d : FibData} {T₀ : β → DistOn upperHalfPlaneOpens} {h₁ : X → DistOn upperHalfPlaneOpens}

/-- Constructed initial data replace the time-zero (K-b) input in the
positive-time glued mean theorem. Thus the full canonical mean identity
is derived from actual Gaussian decompositions and the slit comparison. -/
theorem isChartMeanAt_of_initialData (hZ : Measurable Z) (hY : Measurable Y) (hB : MeasurableSet B)
    (D : InitialWindowData β (μ.map Z) d T₀)
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ (fun x => T₀ (Z x)))
    (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁) (h𝒢 : 𝒢₀ ≤ 𝒢)
    {Wph : X → ℝ → ℝ} {η : X → ℝ → ℂ} {r τ Tc : X → ℝ}
    {c : X → Chart} {Ω : X → Set ℂ} {γ : X → ℝ → ℂ}
    {ι : Type*} {ρ : ι → X → ℝ} {L : ι → X → Set ℂ} {A : X → Set ℂ}
    {M₂ uph : ι → X → ℂ → ℝ} {S' : ι → Set X}
    (hglued : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      IsGluedSlitSample d.κ (withQ d (D.correction (Z x))) (D.cutoff (Z x)) D.neighbourhood
        (Y x) q (Wph x) (η x) (r x) (τ x) (c x) (Ω x) (γ x) (Tc x)
        (fun i => ρ i x) (fun i => L i x) (A x) (fun i => M₂ i x) (fun i => uph i x))
    (hS' : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      ∀ i, ρ i x < r x + τ x → x ∈ S' i)
    (hconv : ∀ᵐ x ∂μ, ∀ i, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → x ∈ S' i →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ chartHull Y q x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x → h₁ x ψ = ∫ z, v z * ψ z) →
      ∀ z₀ ∈ L i x ∪ {z : ℂ | z.im = 0}, (∃ ε > 0, A x ∩ ball z₀ ε ⊆ L i x) →
      ∀ l : Filter ℂ, l ≤ 𝓟 (H \ chartHull Y q x) → Tendsto (c x).2.1 l (𝓝 z₀) →
        Tendsto (fun ζ => v ζ - (M₂ i x ((c x).2.1 ζ) + 0 +
          QuantumZipper.chiC d.κ * (c x).2.2 ((c x).2.1 ζ))) l (𝓝 0)) :
    @IsChartMeanAt X mX β _ μ Z B Y q 𝒢
      (fun x => canonMean.{v} (withQ d (D.correction (Z x))) (D.cutoff (Z x)) (ULift.up (Y x)) q) := by
  exact Aux61OldB.isChartMeanAt_canonMean_of_glued_of_zero hY hB hG d.κ hglued hS' hconv hG0 h𝒢
    (isChartMeanAt_zero_of_initialData hZ hY hB D hG0)

end InteractingSLE.Sec5.Aux61GStep
