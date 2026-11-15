/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71GFlow
import InteractingSLE.Spec.Sec7.StripSysField
import InteractingSLE.Spec.Sec7.Prop74
import InteractingSLE.Spec.Exist.CanonicalMain
import InteractingSLE.Spec.Sec6.Prop61Three

/-!
# Lemma 7.1: the three-curve space

Packet PROVE-LEMMA71G, part (A) (specification §7.1, setup p. 221, `source/spec/p193-240.md` L543: "Fix `a, b > 0`
and let `h` be a GFF on `ℍ` with boundary data as in the left side of Figure 7.1. Fix `θ₁ < 0 < θ₂` and let `η_{θᵢ}`
be the flow line of `h` with angle `θᵢ` […] Let `η` be the (zero angle) flow line of `h`. Assume that `a, b` are
chosen sufficiently large […] By Theorem 1.2, in a certain non-boundary-intersecting regime, which we proved in
Section 4.2, we know that `η_{θ₁}`, `η`, and `η_{θ₂}` are all almost surely determined by `h`").

* `exists_isGFFWithBoundaryData_prop74Data`: a GFF with the data of Figure 7.1 (`−a` left of `0`, `b` right of `0`)
  exists on some probability space (the field of Theorem 1.1's coupling of the zero-angle flow-line word);
* `IsFlowLine.congr_ae`: a flow line may be replaced by a version that agrees with it almost surely;
* `IsLemma62Curve.three`: the hypotheses of the three-curve form of Lemma 6.2
  (`Sec6.Three.ae_condExp_exp_eq_three_of_tendsto`) from the hypotheses on each curve;
* **`exists_threeCurveSpace`**: for `0 < κ < 4`, `θ₁ < 0 < θ₂` and `a, b` large (Remark 4.1 for each of the three
  angles: `a ≥ λ − πχ + θ₂χ`, `b ≥ λ − πχ − θ₁χ`), one probability space carries a GFF `h` with the data of
  Figure 7.1 and its three flow lines `β = η_{θ₂}`, `γ = η_0`, `α = η_{θ₁}` from `0`, each continuous for every `ω`,
  with infinite lifetime, never touching `ℝ ∖ {0}`, and with every hypothesis of Lemma 6.2 for the centred field
  `h − 𝔥₀` (a zero-boundary GFF). Named inputs: the frozen types of Theorems 1.2 and 1.3 (`Exist.Theorem12Statement`,
  `Exist.Theorem13Statement`, through the landed flow-line existence `Exist.exists_isFlowLine_of_thm12_thm13_only`),
  Lemma 7.5 (`Theorem15.Lemma75Statement`) and Aux. lemma 56 at first entrance times
  (`Restart.RetainedRangeEntranceStatement`). All four are used only for flow-line words in Remark 4.1's regime (no
  boundary contacts), the §4.2 regime the source invokes.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71G

open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open Sec6

/-! ### The field of Figure 7.1 -/

/-- **A GFF with the data of Figure 7.1 exists**: the field of Theorem 1.1's coupling (assembled from Theorem 2.2's
existence) of the zero-angle flow-line word of `prop74Data a b`. -/
theorem exists_isGFFWithBoundaryData_prop74Data {κ : ℝ} (hκ : 0 < κ) (a b : ℝ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) := by
  have hb := isPiecewiseConstant_prop74Data a b
  have hF := Theorem15.isOrderedForceWord_flowLine (prop74Data a b) {0} 0
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h', hC⟩ :=
    Coupling.exists_isOptionalHullCoupling_of_thm22.{u} hκ hF
      (exists_isIntegratedSLEEvolution_assembled (ρL := flowLineRhoL κ (prop74Data a b) {0} 0 0)
        (ρR := flowLineRhoR κ (prop74Data a b) {0} 0 0) hκ hF)
  exact ⟨Ω, mΩ, P, hP, h', StripSysField.isGFFWithBoundaryData_of_flowLineGFF hκ hb ⟨hC.2.1, hC.2.2.1⟩⟩

/-! ### Versions of flow lines -/

/-- A flow line may be replaced by a path that agrees with it almost surely at all times. -/
theorem IsFlowLine.congr_ae {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {x θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {η η' : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b J x θ P h η ζ) (he : ∀ᵐ ω ∂P, ∀ t, η' ω t = η ω t) :
    IsFlowLine κ b J x θ P h η' ζ := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hcpl, hgen⟩ := hη
  refine ⟨h', 𝓕, W, VL, VR, B, htr, hcpl, ?_⟩
  filter_upwards [hgen, he] with ω hω heω
  have e : (fun t => η' ω t - x) = fun t => η ω t - x := funext fun t => by rw [heω t]
  rw [e]
  exact hω

/-! ### Lemma 6.2's hypotheses for the three curves -/

section Three

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {β α γ : Ω → ℝ≥0 → ℂ}

/-- **The hypotheses of the three-curve Lemma 6.2** (`Sec6.Three.ae_condExp_exp_eq_three_of_tendsto`, curves
`![β, α, γ]`) from Lemma 6.2's hypotheses on each curve. -/
theorem IsLemma62Curve.three (hβ : IsLemma62Curve β h P) (hα : IsLemma62Curve α h P)
    (hγ : IsLemma62Curve γ h P) :
    (∀ i ω, Continuous (Three.threeCurves β α γ i ω)) ∧ (∀ i ω, Three.threeCurves β α γ i ω 0 = 0) ∧
      (∀ i ω t, 0 ≤ (Three.threeCurves β α γ i ω t).im) ∧
      (∀ i t, Measurable fun ω => Three.threeCurves β α γ i ω t) ∧
      (∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
        (fun ω => Three.threeCurves β α γ i ω t) =ᵐ[P] fun ω => f (h ω)) ∧
      (∀ i, IsEntranceHistoryLocal (Three.threeCurves β α γ i) h P) ∧
      ∀ᵐ ω ∂P, ∀ i, Tendsto (Three.threeCurves β α γ i ω) atTop (Bornology.cobounded ℂ) := by
  have hall : ∀ i, IsLemma62Curve (Three.threeCurves β α γ i) h P := fun i => by
    fin_cases i
    · exact hβ
    · exact hα
    · exact hγ
  refine ⟨fun i => (hall i).1, fun i => (hall i).2.1, fun i => (hall i).2.2.1, fun i => (hall i).2.2.2.1,
    fun i => (hall i).2.2.2.2.1, fun i => (hall i).2.2.2.2.2.1, ?_⟩
  filter_upwards [hβ.2.2.2.2.2.2, hα.2.2.2.2.2.2, hγ.2.2.2.2.2.2] with ω h1 h2 h3 i
  fin_cases i
  · exact h1
  · exact h2
  · exact h3

end Three

/-! ### The three-curve space -/

/-- Remark 4.1 for the angle-`θ` flow line of the data of Figure 7.1, when `θ₁ ≤ θ ≤ θ₂` and `a, b` are large. -/
theorem prop74Data_remark41 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ θ a b : ℝ} (h1 : θ₁ ≤ θ) (h2 : θ ≤ θ₂)
    (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a) (hb : sleLambda κ - π * chiC κ - θ₁ * chiC κ ≤ b) :
    (∀ x : ℝ, x < 0 → x ∉ (({0} : Finset ℝ) : Set ℝ) → prop74Data a b x + θ * chiC κ ≤ -sleLambda κ + π * chiC κ) ∧
      ∀ x : ℝ, 0 < x → x ∉ (({0} : Finset ℝ) : Set ℝ) →
        sleLambda κ - π * chiC κ ≤ prop74Data a b x + θ * chiC κ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθ2 : θ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h2 hχ.le
  have hθ1 : θ₁ * chiC κ ≤ θ * chiC κ := mul_le_mul_of_nonneg_right h1 hχ.le
  refine ⟨fun x hx _ => ?_, fun x hx _ => ?_⟩
  · simp only [prop74Data, hx, ↓reduceIte]
    linarith
  · simp only [prop74Data, not_lt.2 hx.le, ↓reduceIte]
    linarith

/-- **The three-curve space of §7.1.** For `0 < κ < 4`, `θ₁ < 0 < θ₂` and `a, b` large (Remark 4.1 for the three
angles), one probability space carries a GFF `h` with the data of Figure 7.1 (`−a` left of `0`, `b` right of `0`),
its bounded harmonic extension `u₀`, and its three flow lines from `0`: `β = η_{θ₂}` (left flank), `α = η_{θ₁}`
(right flank) and the zero-angle `γ = η` (middle), each with Lemma 6.2's hypotheses for the centred field `h − 𝔥₀`
(a zero-boundary GFF), with almost surely infinite lifetimes and no contact with `ℝ ∖ {0}`. Named inputs: the frozen
types of Theorems 1.2 and 1.3 (flow-line existence), Lemma 7.5 and Aux. lemma 56 at first entrance times, each used
only for flow-line words in Remark 4.1's regime. Conditional helper. -/
theorem exists_threeCurveSpace (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hL75 : Theorem15.Lemma75Statement.{u}) (hA56 : Restart.RetainedRangeEntranceStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ a b : ℝ} (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
    (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a) (hb : sleLambda κ - π * chiC κ - θ₁ * chiC κ ≤ b) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) (ζβ ζα ζγ : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) ∧
      IsBoundedHarmonicExtension (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) u₀ ∧
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P ∧
      IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h β ζβ ∧ IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h α ζα ∧
      IsFlowLine κ (prop74Data a b) {0} 0 0 P h γ ζγ ∧
      IsLemma62Curve β (WholeField.centredField h u₀) P ∧ IsLemma62Curve α (WholeField.centredField h u₀) P ∧
      IsLemma62Curve γ (WholeField.centredField h u₀) P ∧
      ∀ᵐ ω ∂P, ζβ ω = ⊤ ∧ ζα ω = ⊤ ∧ ζγ ω = ⊤ ∧
        ∀ i (t : ℝ≥0) (x : ℝ), x ≠ 0 → Three.threeCurves β α γ i ω t ≠ x := by
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := exists_isGFFWithBoundaryData_prop74Data.{u} hκ a b
  have hbpc := isPiecewiseConstant_prop74Data a b
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hbpc
  -- one flow line per angle, and its version with Lemma 6.2's hypotheses
  have hcurve : ∀ θ : ℝ, θ₁ ≤ θ → θ ≤ θ₂ → ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
      IsFlowLine κ (prop74Data a b) {0} 0 θ P h η ζ ∧ IsLemma62Curve η (WholeField.centredField h u₀) P ∧
        ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ (t : ℝ≥0) (x : ℝ), x ≠ 0 → η ω t ≠ x := by
    intro θ h1 h2
    obtain ⟨η₀, ζ, hη₀⟩ := Exist.exists_isFlowLine_of_thm12_thm13_only h12 h13 (x := 0) (θ := θ) hκ hκ4 hbpc hh
    obtain ⟨hL, hR⟩ := prop74Data_remark41 hκ hκ4 h1 h2 ha hb
    obtain ⟨η, hη, hae⟩ := exists_lemma62Version hL75 hA56 hκ hκ4 hbpc hh hL hR hη₀ hu₀
    refine ⟨η, ζ, IsFlowLine.congr_ae hη₀ (hae.mono fun ω hω => hω.2.1), hη, ?_⟩
    filter_upwards [hae] with ω hω
    exact ⟨hω.1, hω.2.2⟩
  obtain ⟨β, ζβ, hβf, hβ, hβa⟩ := hcurve θ₂ (hθ₁.trans hθ₂).le le_rfl
  obtain ⟨α, ζα, hαf, hα, hαa⟩ := hcurve θ₁ le_rfl (hθ₁.trans hθ₂).le
  obtain ⟨γ, ζγ, hγf, hγ, hγa⟩ := hcurve 0 hθ₁.le hθ₂.le
  refine ⟨Ω, mΩ, P, hP, h, u₀, β, α, γ, ζβ, ζα, ζγ, hh, hu₀,
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀, hβf, hαf, hγf, hβ, hα, hγ, ?_⟩
  filter_upwards [hβa, hαa, hγa] with ω h1 h2 h3
  refine ⟨h1.1, h2.1, h3.1, fun i t x hx => ?_⟩
  fin_cases i
  · exact h1.2 t x hx
  · exact h2.2 t x hx
  · exact h3.2 t x hx

end InteractingSLE.Sec7.Lemma71G
