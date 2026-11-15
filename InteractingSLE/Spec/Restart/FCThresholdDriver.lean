/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCThresholdDriverPremises
import InteractingSLE.Spec.Restart.FCThresholdDriverObstruction

/-!
# Canonical clock regularity and almost-sure threshold-driver records

The exact committed record has an everywhere branch cover. Here an almost-sure
record keeps that record on a measurable event equal almost surely to the meeting
event. This separate interface does not change the committed statement. Constructing
its stochastic driver inputs from the first-contact geometry remains explicit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb

open Sec2.Assembly

universe u

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Two canonical clocks of the same pair agree on the available chart intervals,
including the closed terminal endpoints. -/
theorem ae_canonClock_eq {P : Measure Ω} {d : PairData Ω}
    {γ₁ γ₂ γ₁' γ₂' : Ω → ℝ≥0 → ℂ} {U₁ U₂ U₁' U₂' : Ω → ℝ≥0∞}
    (hc : d.IsCanonClock P γ₁ γ₂ U₁ U₂) (hc' : d.IsCanonClock P γ₁' γ₂' U₁' U₂') :
    ∀ᵐ ω ∂P, ω ∈ meetSet d → U₁ ω = U₁' ω ∧ U₂ ω = U₂' ω ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U₁ ω → γ₁ ω t = γ₁' ω t) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U₂ ω → γ₂ ω t = γ₂' ω t) := by
  filter_upwards [hc, hc'] with ω hω hω' hm
  obtain ⟨hE, hζ₁, hζ₂⟩ := mem_meetSet_iff.1 hm
  have h₁ := (hω hE).1 hζ₁
  have h₂ := (hω hE).2 hζ₂
  have h₁' := (hω' hE).1 hζ₁
  have h₂' := (hω' hE).2 hζ₂
  have he₁ := h₁.2.trans h₁'.2.symm
  have he₂ := h₂.2.trans h₂'.2.symm
  exact ⟨he₁, he₂,
    fun t ht => (h₁.1 t ht).trans (h₁'.1 t (he₁ ▸ ht)).symm,
    fun t ht => (h₂.1 t ht).trans (h₂'.1 t (he₂ ▸ ht)).symm⟩

/-- The closed-interval continuity field of the record is already forced by
the source canonical-clock hypotheses, rather than an extra mathematical input. -/
theorem ae_continuousOn_canonClock_flowLines
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h77 : Supp10.Lemma77Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞}
    (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d →
      ContinuousOn (γ₁ ω) {t | (t : ℝ≥0∞) ≤ U₁ ω} ∧
      ContinuousOn (γ₂ ω) {t | (t : ℝ≥0∞) ≤ U₂ ω} := by
  obtain ⟨γc₁, γc₂, Uc₁, Uc₂, -, -, -, -, hc₁, hc₂, hccanon, -⟩ :=
    exists_canonClock Theorem15.aux25Statement h77 hκ hκ4 hb hx hθ hh hη₁ hη₂
      hd hζ₁ hζ₂ hae
  filter_upwards [ae_canonClock_eq hcanon hccanon] with ω he hm
  obtain ⟨he₁, he₂, hγ₁, hγ₂⟩ := he hm
  have hcont₁ := hc₁ ω
  have hcont₂ := hc₂ ω
  rw [← he₁] at hcont₁
  rw [← he₂] at hcont₂
  exact ⟨hcont₁.congr hγ₁, hcont₂.congr hγ₂⟩

/-- The original record on a measurable modification of the live event. This
avoids imposing a countable word-type range on arbitrary null modifications. -/
def HasAEThresholdDriverInputs (P : Measure Ω) (κ θ : ℝ) (M : Set Ω)
    (β : Ω → BoundaryWord) (Hc : Ω → DistOn upperHalfPlaneOpens)
    (Γ : Ω → ℝ≥0 → ℂ) (U : Ω → ℝ≥0∞) : Prop :=
  ∃ M' : Set Ω, MeasurableSet M' ∧ M =ᵐ[P] M' ∧
    Nonempty (FCThresholdDriverInputs P κ θ M' β Hc Γ U)

/-- An almost-sure live event is sufficient for the exact driver-reading conclusion. -/
theorem ae_driverReading_of_aeThresholdInputs {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) {M : Set Ω} {β : Ω → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc)
    {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (h : HasAEThresholdDriverInputs P κ θ M β Hc Γ U)
    {G : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hG : IsCanonicalDriverCode κ θ G) :
    ∀ᵐ ω ∂P, ω ∈ M → ∃ W : ℝ≥0 → ℝ,
      ContinuousOn W {t | (t : ℝ≥0∞) < U ω} ∧ W 0 = 0 ∧
      ContinuousOn (Γ ω) {t | (t : ℝ≥0∞) ≤ U ω} ∧
      IsGeneratingTrace W (U ω) (Γ ω) ∧
      IsDriverCodeMatch (G (β ω, Hc ω)) W (U ω) := by
  obtain ⟨M', -, he, ⟨h'⟩⟩ := h
  filter_upwards [ae_driverReading_of_thresholdInputs hκ hHc h' hG, he]
    with ω hr heω hm
  exact hr (heω ▸ hm)

/-- The exact remaining source construction with live events modified only on null
sets. This distinct proposition is not asserted proved here. Its stochastic
fields still require the relative driver, safe laws, seed and threshold proofs. -/
def FirstContactAEThresholdDriverInputsStatement : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [_mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : PairData Ω) (hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord, Measurable[retSigma d P] β →
      (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) →
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞),
      (∀ t, Measurable fun ω => γ₁ ω t) → (∀ t, Measurable fun ω => γ₂ ω t) →
      Measurable U₁ → Measurable U₂ → d.IsCanonClock P γ₁ γ₂ U₁ U₂ →
    HasAEThresholdDriverInputs P κ θ₁ (meetSet d) β (hd.chartField κ h) γ₁ U₁ ∧
      HasAEThresholdDriverInputs P κ θ₂ (meetSet d) β (hd.chartField κ h) γ₂ U₂

/-- An exact record construction would imply the almost-sure interface. The
converse is not claimed: the exact cover has additional all-sample obligations. -/
theorem firstContactAEThresholdDriverInputsStatement_of_exact
    (h : FirstContactThresholdDriverInputsStatement.{u}) :
    FirstContactAEThresholdDriverInputsStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ H hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
  have hM : MeasurableSet (meetSet d) := retSigma_le P _ (hd.measurableSet_meetSet P)
  obtain ⟨h₁, h₂⟩ := h κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P H hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
  exact ⟨⟨meetSet d, hM, EventuallyEqSet.rfl, h₁⟩,
    ⟨meetSet d, hM, EventuallyEqSet.rfl, h₂⟩⟩

/-- The almost-sure interface suffices for the original source-facing determination
conclusion. No exact branch cover on discarded null realizations is used. -/
theorem firstContactCanonCondDetStatement_of_aeThresholdInputs
    (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hA56 : RetainedRangeEntranceStatement.{u}) (hCode : CanonicalDriverCodeStatement)
    (hInputs : FirstContactAEThresholdDriverInputsStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} := by
  apply firstContactCanonCondDetStatement_of_driver_readings hL75 hL77 hA56 hCode
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon G₁ G₂ hG₁ hG₂
  obtain ⟨I₁, I₂⟩ := hInputs κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
  have hr₁ := ae_driverReading_of_aeThresholdInputs hκ (hd.measurable_chartField κ hh.1) I₁ hG₁
  have hr₂ := ae_driverReading_of_aeThresholdInputs hκ (hd.measurable_chartField κ hh.1) I₂ hG₂
  filter_upwards [hr₁, hr₂] with ω h₁ h₂ hω
  obtain ⟨W₁, hW₁⟩ := h₁ hω
  obtain ⟨W₂, hW₂⟩ := h₂ hω
  exact ⟨W₁, W₂, hW₁, hW₂⟩

/-- Final conditional source conclusion with the remaining premises displayed:
Theorems 1.2 and 1.3, Lemma 7.6, and the almost-sure threshold-driver construction.
L75, L77, A56 and canonical driver codes are supplied by the proved adapters. -/
theorem firstContactCanonCondDetStatement_of_aeThresholdInputs_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u}) (hInputs : FirstContactAEThresholdDriverInputsStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_aeThresholdInputs (lemma75Statement_of_thm12_thm13 h12 h13)
    (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76) firstContact_retainedRangeEntranceStatement
    (firstContact_canonicalDriverCodeStatement_of_thm12_thm13 h12₀ h13₀) hInputs

end InteractingSLE.Restart.FCPlumb
