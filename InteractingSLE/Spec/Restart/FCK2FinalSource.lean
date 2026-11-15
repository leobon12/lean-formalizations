/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2FinalClock

/-!
# Source incident bounds at every live canonical real tip
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (chiC)
namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData
universe u

/-- The box word has the strict incident heights needed at every positive
live real tip of either actual canonical chart path. -/
theorem ae_canon_real_tip_incident_bounds
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
      (∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < U₁ ω → (γ₁ ω q).im = 0 →
        ((γ₁ ω q).re ≤ 0 → leftLim (β ω).fn (γ₁ ω q).re + θ₁ * chiC κ < sleLambda κ) ∧
        (0 ≤ (γ₁ ω q).re → -sleLambda κ < rightLim (β ω).fn (γ₁ ω q).re + θ₁ * chiC κ)) ∧
      (∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < U₂ ω → (γ₂ ω q).im = 0 →
        ((γ₂ ω q).re ≤ 0 → leftLim (β ω).fn (γ₂ ω q).re + θ₂ * chiC κ < sleLambda κ) ∧
        (0 ≤ (γ₂ ω q).re → -sleLambda κ < rightLim (β ω).fn (γ₂ ω q).re + θ₂ * chiC κ)) := by
  obtain ⟨c₀, hc₀, hJ, hb₀⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
  have hside := Sec7.SideHeightBox.isBoxSideLimit_of_flowLines h75 h77 h56 hκ hκ4 hb hx hθ hh
    hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
  have hword := isBoxMeanIdentification_word h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂
    hae hu₀ hc₀ hJ hb₀ hside
  have he := ae_mean_integrals_eq_of_boxMean h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hu₀ hword hm
  have hv₁ := ae_live_real_incident_bounds hκ hκ4 hb hh hη₁
  have hv₂ := ae_live_real_incident_bounds hκ hκ4 hb hh hη₂
  have hj₁ := RLC.jumpVisitStatement κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁
  have hj₂ := RLC.jumpVisitStatement κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂
  have hp₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hp₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  have hr := ae_live_canon_tip_readings h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hcanon
  filter_upwards [hs, he, hae, hv₁, hv₂, hj₁, hj₂, hp₁, hp₂, hr]
    with ω hsω heω ha hv₁ω hv₂ω hj₁ω hj₂ω hp₁ω hp₂ω hrω hM
  have hE := (mem_meetSet_iff.1 hM).1
  obtain ⟨eL, eR⟩ := word_limits_eq_of_mean_integrals (hd.word_isSorted hE hc₀ _ _)
    (hsω hM) (heω hM)
  have hzero₁ : d.η₁ ω 0 = (x₁ : ℂ) := (ha.2.1 0 (by simp)).trans (Sec7.IsPathGood.zero hp₁ω)
  have hzero₂ : d.η₂ ω 0 = (x₂ : ℂ) := (ha.2.2 0 (by simp)).trans (Sec7.IsPathGood.zero hp₂ω)
  have hx₁K : (x₁ : ℂ) ∈ d.K ω := by
    rw [PairData.K_of_mem hE, prefixSet]
    exact Or.inl ⟨0, ⟨le_rfl, zero_le⟩, hzero₁⟩
  have hx₂K : (x₂ : ℂ) ∈ d.K ω := by
    rw [PairData.K_of_mem hE, prefixSet]
    exact Or.inr ⟨0, ⟨le_rfl, zero_le⟩, hzero₂⟩
  have hi₁ : InjOn (d.η₁ ω) {s | (s : ℝ≥0∞) ≤ d.ζ₁ ω} := by
    rw [hζ₁]
    exact hp₁ω.1.congr (fun s hs => (ha.2.1 s hs).symm)
  have hi₂ : InjOn (d.η₂ ω) {s | (s : ℝ≥0∞) ≤ d.ζ₂ ω} := by
    rw [hζ₂]
    exact hp₂ω.1.congr (fun s hs => (ha.2.2 s hs).symm)
  have hN := Sec7.IsFirstContact.no_return hi₁ hi₂ (hd.isFirstContact hE)
  have hout {z : ℂ} (him : z.im = 0) (hn : d.inv ω z ∉ d.K ω) :
      z.re < d.wordL ω ∨ d.wordR ω < z.re := by
    by_contra hbad
    push Not at hbad
    have hK := hd.inv_mem_K_of_mem_Icc hE hbad.1 hbad.2
    rw [Sec7.SideHeightBox.ofReal_re_of_im him] at hK
    exact hn hK
  constructor
  · intro q hq hqU him
    obtain ⟨s, hs₀, hsζ, htip⟩ := (hrω hM).1 q hq hqU
    have hsζ' : (s : ℝ≥0∞) < ζ₁ ω := by rwa [← hζ₁]
    have hn : d.inv ω (γ₁ ω q) ∉ d.K ω := by
      rw [htip, PairData.K_of_mem hE, prefixSet]
      exact hN.1 s hs₀ hsζ.le
    have hv := word_incident_bounds_of_live_visit hd hE hb hc₀ hb₀
      (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ) (Sec7.IsPathGood.zero hp₁ω)
      (hd.baseL_le hx₁K) (hd.le_baseR hx₁K) hv₁ω hj₁ω (hout him hn)
      ⟨s, hsζ', (ha.2.1 s hsζ'.le).symm.trans (htip.symm.trans
        (congrArg (d.inv ω) (Sec7.SideHeightBox.ofReal_re_of_im him)).symm)⟩
    rw [eL, eR] at hv
    exact hv
  · intro q hq hqU him
    obtain ⟨s, ht₀, hsζ, htip⟩ := (hrω hM).2 q hq hqU
    have hsζ' : (s : ℝ≥0∞) < ζ₂ ω := by rwa [← hζ₂]
    have hn : d.inv ω (γ₂ ω q) ∉ d.K ω := by
      rw [htip, PairData.K_of_mem hE, prefixSet]
      exact hN.2 s ht₀ hsζ.le
    have hv := word_incident_bounds_of_live_visit hd hE hb hc₀ hb₀
      (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ) (Sec7.IsPathGood.zero hp₂ω)
      (hd.baseL_le hx₂K) (hd.le_baseR hx₂K) hv₂ω hj₂ω (hout him hn)
      ⟨s, hsζ', (ha.2.2 s hsζ'.le).symm.trans (htip.symm.trans
        (congrArg (d.inv ω) (Sec7.SideHeightBox.ofReal_re_of_im him)).symm)⟩
    rw [eL, eR] at hv
    exact hv

/-- Both source canonical paths avoid the force threshold at every positive
pre-lifetime capacity, including real tips and every fixed force type. -/
theorem ae_canon_positive_prelife_nonThreshold
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
    (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂)
    {W₁ W₂ : ℝ≥0 → Ω → ℝ}
    (hc₁ : ∀ ω, Continuous (W₁ · ω)) (hc₂ : ∀ ω, Continuous (W₂ · ω))
    (hz₁ : ∀ ω, W₁ 0 ω = 0) (hz₂ : ∀ ω, W₂ 0 ω = 0)
    (hg : ∀ᵐ ω ∂P, ω ∈ meetSet d →
      IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
      IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) :
    (∀ a : RetAux79.ForceWordType, ∀ᵐ ω ∂P, ω ∈ fcTypeBranch κ θ₁ (meetSet d) β a →
      ∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < U₁ ω →
        ¬ ForceWord.ThresholdCondition a.rhoL a.rhoR (W₁ q ω)
          (fun i => Sec7.PocketTraversal.geomLW W₁
            (fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω)) i q ω)
          (fun j => Sec7.PocketTraversal.geomRW W₁
            (fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω)) j q ω)) ∧
    (∀ a : RetAux79.ForceWordType, ∀ᵐ ω ∂P, ω ∈ fcTypeBranch κ θ₂ (meetSet d) β a →
      ∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < U₂ ω →
        ¬ ForceWord.ThresholdCondition a.rhoL a.rhoR (W₂ q ω)
          (fun i => Sec7.PocketTraversal.geomLW W₂
            (fun ω => FCDet.typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω)) i q ω)
          (fun j => Sec7.PocketTraversal.geomRW W₂
            (fun ω => FCDet.typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω)) j q ω)) := by
  have hi := ae_canon_real_tip_incident_bounds h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd
    hζ₁ hζ₂ hae hu₀ hs hm hcanon
  constructor
  · intro a
    filter_upwards [hi, hg] with ω hiω hgω hB q hq hqU
    exact not_threshold_type_geom_of_incident_bounds (c := β ω) (W := fun t => W₁ t ω)
      (U := U₁ ω) (γ := γ₁ ω) hκ hB.2 (hc₁ ω) (hz₁ ω) (hgω hB.1).1
      hq hqU.le ((hiω hB.1).1 q hq hqU)
  · intro a
    filter_upwards [hi, hg] with ω hiω hgω hB q hq hqU
    exact not_threshold_type_geom_of_incident_bounds (c := β ω) (W := fun t => W₂ t ω)
      (U := U₂ ω) (γ := γ₂ ω) hκ hB.2 (hc₂ ω) (hz₂ ω) (hgω hB.1).2
      hq hqU.le ((hiω hB.1).2 q hq hqU)

/-- Each actual canonical lifetime is at most the force threshold. The
finite-terminal reverse inequality is the only remaining collision step. -/
theorem ae_canon_life_le_threshold
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
    (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂)
    {W₁ W₂ : ℝ≥0 → Ω → ℝ}
    (hc₁ : ∀ ω, Continuous (W₁ · ω)) (hc₂ : ∀ ω, Continuous (W₂ · ω))
    (hz₁ : ∀ ω, W₁ 0 ω = 0) (hz₂ : ∀ ω, W₂ 0 ω = 0)
    (hg : ∀ᵐ ω ∂P, ω ∈ meetSet d →
      IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
      IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) :
    (∀ a : RetAux79.ForceWordType, ∀ᵐ ω ∂P, ω ∈ fcTypeBranch κ θ₁ (meetSet d) β a →
      U₁ ω ≤ FCDet.thr a.rhoL a.rhoR W₁
        (fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω))
        (fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω)) ω) ∧
    (∀ a : RetAux79.ForceWordType, ∀ᵐ ω ∂P, ω ∈ fcTypeBranch κ θ₂ (meetSet d) β a →
      U₂ ω ≤ FCDet.thr a.rhoL a.rhoR W₂
        (fun ω => FCDet.typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω))
        (fun ω => FCDet.typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω)) ω) := by
  have hp := ae_canon_positive_prelife_nonThreshold h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd
    hζ₁ hζ₂ hae hu₀ hs hm hcanon hc₁ hc₂ hz₁ hz₂ hg
  have ha := ae_admissible_of_boxMean_all_sides h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd
    hζ₁ hζ₂ hae hu₀ hs hm
  constructor
  · intro a
    apply RetAux79.life_le_thr_of_retPrelifeNonThreshold hc₁
    apply prelifeNonThreshold_of_boundary_checks hc₁ hz₁
      (fun ω => (FCDet.isOrderedForceWord_typeXL (β ω)).2.1)
      (fun ω => (FCDet.isOrderedForceWord_typeXL (β ω)).2.2.2)
      (hg.mono fun _ hω hB => (hω hB.1).1)
    · filter_upwards [ha] with ω haω hB
      exact not_threshold_type_of_admissible hκ hB.2 (haω hB.1).1
    · exact (hp.1 a).mono (fun _ hω hB q hq hqU _ => hω hB q hq hqU)
  · intro a
    apply RetAux79.life_le_thr_of_retPrelifeNonThreshold hc₂
    apply prelifeNonThreshold_of_boundary_checks hc₂ hz₂
      (fun ω => (FCDet.isOrderedForceWord_typeXL (β ω)).2.1)
      (fun ω => (FCDet.isOrderedForceWord_typeXL (β ω)).2.2.2)
      (hg.mono fun _ hω hB => (hω hB.1).2)
    · filter_upwards [ha] with ω haω hB
      exact not_threshold_type_of_admissible hκ hB.2 (haω hB.1).2
    · exact (hp.2 a).mono (fun _ hω hB q hq hqU _ => hω hB q hq hqU)

end InteractingSLE.Restart.FCPlumb
