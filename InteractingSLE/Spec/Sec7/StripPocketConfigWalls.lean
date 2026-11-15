/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripWallMeanFull
import InteractingSLE.Spec.Sec7.StripPocketConfigEvent

/-!
# Theorem 1.3's pocket word: the strip walls are simple proper curves

Packet PROVE-STRIPSYS30. Specification §7.4.1, proof of Aux. lemma 130 (`source/spec/p385-432.md` L431–L452,
p. 410): "For these two-piece schedules the required continuity, simplicity, and determination follow directly from
the earlier non-boundary results. […] The continuously extended inverse own map therefore gives a continuous simple
complete concatenation."

`StripPocketConfig.exists_stripPocketEvent` needs the walls `α = η^{1,∞}_{−π/2,θ₁}` and `β^{(q)} = η^{q,∞}_{π/2,θ₂}`
of the strip system to be simple proper curves (`Lemma71I.IsSimpleProper`) almost surely. PROVE-STRIPSYS28/29 work
with *versions* of the walls (continuous at every sample, `0` at time `0`, measurable at fixed times, almost surely a
generating trace of the concatenated driver). Here: every such version is almost surely simple proper
(`ae_isSimpleProper_alpha`, `ae_isSimpleProper_beta`), from the simple transient traces of PROVE-STRIPSYS28
(`ae_simple_trace_alpha/beta`) and the uniqueness of the generating trace of a continuous driver.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE

namespace Sec7

namespace StripWall

open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **A version of a two-piece wall with a simple transient trace is simple proper** almost surely: if the
concatenated driver of two regular pieces with infinite lifetimes almost surely has a simple transient generating
trace, every path that is continuous, starts at `0` and almost surely generates the same chain is almost surely a
simple proper curve of `ℍ`. -/
theorem ae_isSimpleProper_of_catPath {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {t₀ : ℝ≥0}
    (hsimple : ∀ᵐ ω ∂P, ((E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤) ∧ ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
        Tendsto η atTop (cobounded ℂ))
    {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0)
    (hγtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω)) :
    ∀ᵐ ω ∂P, Lemma71I.IsSimpleProper (γ ω) := by
  filter_upwards [hsimple, hγtr] with ω hω hγ
  obtain ⟨hζ, η, hη, hinj, hH, htr⟩ := hω
  obtain ⟨hcc, hcc0⟩ := continuous_catPath_of_isRegularDriver (hreg 0 ω) (hreg 1 ω) hζ.1 hζ.2 t₀
  have heq : γ ω = η := funext fun t => by
    rw [← LP.traceAt_eq_of_isGeneratingTrace hγ hcc.continuousOn hcc0 ENNReal.coe_lt_top,
      LP.traceAt_eq_of_isGeneratingTrace hη hcc.continuousOn hcc0 ENNReal.coe_lt_top]
  refine ⟨hγc ω, heq ▸ hinj, hγ0 ω, heq ▸ hH, ?_⟩
  rw [heq]
  exact tendsto_norm_atTop_iff_cobounded.2 htr

/-- **Every version of the wall `α = η^{1,∞}_{−π/2,θ₁}` is almost surely a simple proper curve** (Aux. lemma 130's
height choice, p. 410). -/
theorem ae_isSimpleProper_alpha (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω))
    {α : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    ∀ᵐ ω ∂P, Lemma71I.IsSimpleProper (α ω) :=
  ae_isSimpleProper_of_catPath hregα (ae_simple_trace_alpha hS hcumL hcumR hθ₁ hregα) hαc hα0 hαtr

/-- **Every version of the wall `β^{(r)} = η^{r,∞}_{π/2,θ₂}` is almost surely a simple proper curve**, for every
change time `r` (Aux. lemma 130's height choice, p. 410). -/
theorem ae_isSimpleProper_beta (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregβ : ∀ j ω, IsRegularDriver (Es (StripSys.betaSpec r θ₂) j ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec r θ₂) 0 ω).1 r
      (Es (StripSys.betaSpec r θ₂) 1 ω).1) ⊤ (β ω)) :
    ∀ᵐ ω ∂P, Lemma71I.IsSimpleProper (β ω) :=
  ae_isSimpleProper_of_catPath hregβ (ae_simple_trace_beta hS hcumL hcumR hθ₂ r hregβ) hβc hβ0 hβtr

end StripWall

end Sec7

end InteractingSLE
