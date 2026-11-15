/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2TermSource
import InteractingSLE.Spec.Sec7.ContinuityProb2Join

/-! # Physical terminal heights retain their side in the first-contact chart -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData
universe u

/-- A closed-half-plane point whose chart preimage is real is real. -/
theorem real_of_firstContact_inv_real {Ω : Type*} [MeasurableSpace Ω]
    {d : PairData Ω} (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E)
    {z : ℂ} (hz : z ∈ Hbar) (hi : (d.inv ω z).im = 0) : z.im = 0 := by
  apply le_antisymm (not_lt.1 fun hpos => ?_) hz
  have hm := (hd.isFirstContactChart hE).2.2.1.mapsTo hpos
  have hp : 0 < (d.inv ω z).im := hm.1.1
  exact (ne_of_gt hp) hi

/-- An original bad incident height outside the retained union lies on the
same exterior ray of the chart. This uses no terminal side-image assertion. -/
theorem bad_incident_on_chart_side {Ω : Type*} [MeasurableSpace Ω]
    {d : PairData Ω} (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E)
    {κ θ x : ℝ} {b : ℝ → ℝ} {z p : ℂ} (hz : z ∈ Hbar)
    (hi : d.inv ω z = p) (hn : p ∉ d.K ω) (hx : (x : ℂ) ∈ d.K ω)
    (hb : p.im = 0 ∧ ((p.re ≤ x ∧ sleLambda κ ≤ leftLim b p.re + θ * chiC κ) ∨
      (x ≤ p.re ∧ rightLim b p.re + θ * chiC κ ≤ -sleLambda κ))) :
    z.im = 0 ∧ ((z.re < d.wordL ω ∧ sleLambda κ ≤ leftLim b p.re + θ * chiC κ) ∨
      (d.wordR ω < z.re ∧ rightLim b p.re + θ * chiC κ ≤ -sleLambda κ)) := by
  have him := real_of_firstContact_inv_real hd hE hz (by rw [hi]; exact hb.1)
  have hout := real_chart_point_exterior_of_notMem_K hd hE him (hi ▸ hn)
  have hip : (d.inv ω (z.re : ℂ)).re = p.re := by
    rw [Sec7.SideHeightBox.ofReal_re_of_im him, hi]
  refine ⟨him, ?_⟩
  rcases hb.2 with hL | hR
  · rcases hout with hout | hout
    · exact Or.inl ⟨hout, hL.2⟩
    · have h := (hd.inv_of_wordR_lt hE hout).1
      rw [hip] at h
      exact False.elim ((not_lt_of_ge (hL.1.trans (hd.le_baseR hx))) h)
  · rcases hout with hout | hout
    · have h := (hd.inv_of_lt_wordL hE hout).1
      rw [hip] at h
      exact False.elim ((not_lt_of_ge ((hd.baseL_le hx).trans hR.1)) h)
    · exact Or.inr ⟨hout, hR.2⟩

/-- Both actual canonical paths have real finite endpoints and a bad
original incident height on the matching exterior chart side. The source
forward kernels, the box mean, and terminal side-image access are not inputs. -/
theorem ae_canon_terminal_bad_incident_on_chart_side
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h77 : Supp10.Lemma77Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b J x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b J x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞}
    (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂) {W₁ W₂ : ℝ≥0 → Ω → ℝ}
    (hc₁ : ∀ ω, Continuous (W₁ · ω)) (hc₂ : ∀ ω, Continuous (W₂ · ω))
    (hz₁ : ∀ ω, W₁ 0 ω = 0) (hz₂ : ∀ ω, W₂ 0 ω = 0)
    (hg : ∀ᵐ ω ∂P, ω ∈ meetSet d →
      IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
      IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d →
      (∀ T : ℝ≥0, (T : ℝ≥0∞) = U₁ ω → 0 < T ∧ (γ₁ ω T).im = 0 ∧
        (((γ₁ ω T).re < d.wordL ω ∧
          sleLambda κ ≤ leftLim b (η₁ ω (ζ₁ ω).toNNReal).re + θ₁ * chiC κ) ∨
        (d.wordR ω < (γ₁ ω T).re ∧
          rightLim b (η₁ ω (ζ₁ ω).toNNReal).re + θ₁ * chiC κ ≤ -sleLambda κ))) ∧
      (∀ T : ℝ≥0, (T : ℝ≥0∞) = U₂ ω → 0 < T ∧ (γ₂ ω T).im = 0 ∧
        (((γ₂ ω T).re < d.wordL ω ∧
          sleLambda κ ≤ leftLim b (η₂ ω (ζ₂ ω).toNNReal).re + θ₂ * chiC κ) ∨
        (d.wordR ω < (γ₂ ω T).re ∧
          rightLim b (η₂ ω (ζ₂ ω).toNNReal).re + θ₂ * chiC κ ≤ -sleLambda κ))) := by
  have hp₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hp₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  have hb₁ := ae_original_terminal_bad_incident hκ hb hη₁
  have hb₂ := ae_original_terminal_bad_incident hκ hb hη₂
  have hr := ae_canon_terminal_physical_readings h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂
    hae hcanon
  filter_upwards [hp₁, hp₂, hb₁, hb₂, hr, hae, hg]
    with ω hp₁ω hp₂ω hb₁ω hb₂ω hrω ha hgω hM
  obtain ⟨hE, hs, ht⟩ := mem_meetSet_iff.1 hM
  have hi₁ : InjOn (d.η₁ ω) {s | (s : ℝ≥0∞) ≤ d.ζ₁ ω} := by
    rw [hζ₁]
    exact hp₁ω.1.congr (fun s hs => (ha.2.1 s hs).symm)
  have hi₂ : InjOn (d.η₂ ω) {s | (s : ℝ≥0∞) ≤ d.ζ₂ ω} := by
    rw [hζ₂]
    exact hp₂ω.1.congr (fun s hs => (ha.2.2 s hs).symm)
  have hN := Sec7.IsFirstContact.no_return hi₁ hi₂ (hd.isFirstContact hE)
  have hx₁K : (x₁ : ℂ) ∈ d.K ω := by
    rw [PairData.K_of_mem hE, prefixSet]
    exact Or.inl ⟨0, ⟨le_rfl, zero_le⟩,
      (ha.2.1 0 (by simp)).trans (Sec7.IsPathGood.zero hp₁ω)⟩
  have hx₂K : (x₂ : ℂ) ∈ d.K ω := by
    rw [PairData.K_of_mem hE, prefixSet]
    exact Or.inr ⟨0, ⟨le_rfl, zero_le⟩,
      (ha.2.2 0 (by simp)).trans (Sec7.IsPathGood.zero hp₂ω)⟩
  constructor
  · intro T hT
    obtain ⟨hT0, hfin, htip⟩ := (hrω hM).1 T hT
    have hco := ENNReal.coe_toNNReal hfin
    have hco' : (((ζ₁ ω).toNNReal : ℝ≥0) : ℝ≥0∞) = d.ζ₁ ω := by rwa [hζ₁]
    have hlater : d.s₀ ω < (ζ₁ ω).toNNReal := ENNReal.coe_lt_coe.1 (hs.trans_eq hco'.symm)
    have hpos : 0 < (ζ₁ ω).toNNReal := lt_of_le_of_lt zero_le hlater
    have hn : η₁ ω (ζ₁ ω).toNNReal ∉ d.K ω := by
      rw [← ha.2.1 _ hco.le, PairData.K_of_mem hE, prefixSet]
      exact hN.1 _ hlater hco'.le
    exact ⟨hT0, bad_incident_on_chart_side hd hE
      (Sec7.IsGeneratingTrace.mem_Hbar (hgω hM).1 (hc₁ ω).continuousOn (hz₁ ω) hT.le) htip hn hx₁K
      (hb₁ω _ hpos hco)⟩
  · intro T hT
    obtain ⟨hT0, hfin, htip⟩ := (hrω hM).2 T hT
    have hco := ENNReal.coe_toNNReal hfin
    have hco' : (((ζ₂ ω).toNNReal : ℝ≥0) : ℝ≥0∞) = d.ζ₂ ω := by rwa [hζ₂]
    have hlater : d.t₀ ω < (ζ₂ ω).toNNReal := ENNReal.coe_lt_coe.1 (ht.trans_eq hco'.symm)
    have hpos : 0 < (ζ₂ ω).toNNReal := lt_of_le_of_lt zero_le hlater
    have hn : η₂ ω (ζ₂ ω).toNNReal ∉ d.K ω := by
      rw [← ha.2.2 _ hco.le, PairData.K_of_mem hE, prefixSet]
      exact hN.2 _ hlater hco'.le
    exact ⟨hT0, bad_incident_on_chart_side hd hE
      (Sec7.IsGeneratingTrace.mem_Hbar (hgω hM).2 (hc₂ ω).continuousOn (hz₂ ω) hT.le) htip hn hx₂K
      (hb₂ω _ hpos hco)⟩

end InteractingSLE.Restart.FCPlumb
