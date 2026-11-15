/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2SrcWord

/-!
# Source incident heights at finite canonical endpoints

A finite real canonical endpoint lies outside the retained union, by the
closed source clock and first-contact no return. Both heights of the actual
supplied box word therefore agree with the original terminal heights,
including when the endpoint is an original jump.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Complex
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData
universe u

/-- The original field's incident heights are the actual box word's incident
heights at every finite real canonical terminal point, almost surely. -/
theorem ae_canon_terminal_incident_readings
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β : Ω → BoundaryWord} (hs : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hm : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β)
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞}
    (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d →
      (∀ T : ℝ≥0, (T : ℝ≥0∞) = U₁ ω → (γ₁ ω T).im = 0 →
        ((γ₁ ω T).re < d.wordL ω ∨ d.wordR ω < (γ₁ ω T).re) ∧
        leftLim (β ω).fn (γ₁ ω T).re = leftLim b (η₁ ω (ζ₁ ω).toNNReal).re ∧
        rightLim (β ω).fn (γ₁ ω T).re = rightLim b (η₁ ω (ζ₁ ω).toNNReal).re) ∧
      (∀ T : ℝ≥0, (T : ℝ≥0∞) = U₂ ω → (γ₂ ω T).im = 0 →
        ((γ₂ ω T).re < d.wordL ω ∨ d.wordR ω < (γ₂ ω T).re) ∧
        leftLim (β ω).fn (γ₂ ω T).re = leftLim b (η₂ ω (ζ₂ ω).toNNReal).re ∧
        rightLim (β ω).fn (γ₂ ω T).re = rightLim b (η₂ ω (ζ₂ ω).toNNReal).re) := by
  obtain ⟨c₀, hc₀, hJ, hb₀⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
  have hside := Sec7.SideHeightBox.isBoxSideLimit_of_flowLines h75 h77 h56 hκ hκ4 hb hx hθ hh
    hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
  have hword := isBoxMeanIdentification_word h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂
    hae hu₀ hc₀ hJ hb₀ hside
  have he := ae_mean_integrals_eq_of_boxMean h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hu₀ hword hm
  have hp₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hp₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  have hr := ae_canon_terminal_physical_readings h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂
    hae hcanon
  filter_upwards [hs, he, hae, hp₁, hp₂, hr] with ω hsω heω ha hp₁ω hp₂ω hrω hM
  obtain ⟨hE, hs₀, ht₀⟩ := mem_meetSet_iff.1 hM
  obtain ⟨eL, eR⟩ := word_limits_eq_of_mean_integrals (hd.word_isSorted hE hc₀ _ _)
    (hsω hM) (heω hM)
  have hi₁ : InjOn (d.η₁ ω) {s | (s : ℝ≥0∞) ≤ d.ζ₁ ω} := by
    rw [hζ₁]
    exact hp₁ω.1.congr (fun s hs => (ha.2.1 s hs).symm)
  have hi₂ : InjOn (d.η₂ ω) {s | (s : ℝ≥0∞) ≤ d.ζ₂ ω} := by
    rw [hζ₂]
    exact hp₂ω.1.congr (fun s hs => (ha.2.2 s hs).symm)
  have hN := Sec7.IsFirstContact.no_return hi₁ hi₂ (hd.isFirstContact hE)
  constructor
  · intro T hT him
    obtain ⟨-, hfin, htip⟩ := (hrω hM).1 T hT
    have hco : (((ζ₁ ω).toNNReal : ℝ≥0) : ℝ≥0∞) = d.ζ₁ ω := by
      rw [hζ₁, ENNReal.coe_toNNReal hfin]
    have hlater : d.s₀ ω < (ζ₁ ω).toNNReal :=
      ENNReal.coe_lt_coe.1 (hs₀.trans_eq hco.symm)
    have hn : d.inv ω (γ₁ ω T) ∉ d.K ω := by
      rw [htip, ← ha.2.1 _ (ENNReal.coe_toNNReal hfin).le, PairData.K_of_mem hE, prefixSet]
      exact hN.1 _ hlater hco.le
    have hout := real_chart_point_exterior_of_notMem_K hd hE him hn
    have hv := word_incident_limits_of_exterior hd hE hc₀ hb₀
      (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ) hout
    rw [eL, eR, Sec7.SideHeightBox.ofReal_re_of_im him, htip] at hv
    exact ⟨hout, hv⟩
  · intro T hT him
    obtain ⟨-, hfin, htip⟩ := (hrω hM).2 T hT
    have hco : (((ζ₂ ω).toNNReal : ℝ≥0) : ℝ≥0∞) = d.ζ₂ ω := by
      rw [hζ₂, ENNReal.coe_toNNReal hfin]
    have hlater : d.t₀ ω < (ζ₂ ω).toNNReal :=
      ENNReal.coe_lt_coe.1 (ht₀.trans_eq hco.symm)
    have hn : d.inv ω (γ₂ ω T) ∉ d.K ω := by
      rw [htip, ← ha.2.2 _ (ENNReal.coe_toNNReal hfin).le, PairData.K_of_mem hE, prefixSet]
      exact hN.2 _ hlater hco.le
    have hout := real_chart_point_exterior_of_notMem_K hd hE him hn
    have hv := word_incident_limits_of_exterior hd hE hc₀ hb₀
      (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ) hout
    rw [eL, eR, Sec7.SideHeightBox.ofReal_re_of_im him, htip] at hv
    exact ⟨hout, hv⟩

end InteractingSLE.Restart.FCPlumb
