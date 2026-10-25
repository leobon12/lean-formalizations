import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio.RatioLocal
import SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.AXPOSComplete




 
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio

open LQGMetric (DistC DistOn addConst circleAvg restrictTo)

theorem rawRatioEvent_shift_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : LQGMetric.IsWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (z : ℂ) (r : Ioi (0 : ℝ)) (c : ℝ≥0∞) (t : Ω → ℝ) :
    ∀ᵐ ω ∂P,
      (addConst (h ω) (t ω) ∈ rawRatioEvent D z r c ↔
        h ω ∈ rawRatioEvent D z r c) := by
  have hplus : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hh
  filter_upwards [Positivity.Witnesses.ae_annulus_addConst_eq_mul P h hplus ξ Q D hD t]
    with ω hw
  let k : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * t ω))
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hkTop : k ≠ ∞ := ENNReal.ofReal_ne_top
  simp only [rawRatioEvent, Set.mem_ofPred_eq]
  rw [(hw (BiLipschitz.OneScale.crossingAt z r)).1, (hw (BiLipschitz.OneScale.crossingAt z r)).2]
  rw [mul_left_comm c k]
  change k * aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z r) ≤
      k * (c * acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z r)) ↔
    aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z r) ≤
      c * acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z r)
  rw [mul_comm k (aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z r)),
    mul_comm k (c * acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z r))]
  exact ENNReal.mul_le_mul_iff_left hk0 hkTop

 

theorem centered_ratio_local
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (z : ℂ) (r : Ioi (0 : ℝ)) (c : ℝ≥0∞)
    (R : Ioi (0 : ℝ)) :
    let U := BiLipschitz.OneScale.collarOpen z r
    let q : Ω → DistOn U := fun ω =>
      restrictTo U (addConst (h ω) (-circleAvg (h ω) R z))
    ∃ S : Set (DistOn U), MeasurableSet S ∧
      MeasurableSet[MeasurableSpace.comap q inferInstance]
        {ω | BiLipschitz.OneScale.gaussianSmooth U S (q ω) > 1 / 2} ∧
      {ω | BiLipschitz.OneScale.gaussianSmooth U S (q ω) > 1 / 2} =ᵐ[P]
        {ω | h ω ∈ rawRatioEvent D z r c} := by
  dsimp only
  let U := BiLipschitz.OneScale.collarOpen z r
  let q : Ω → DistOn U := fun ω =>
    restrictTo U (addConst (h ω) (-circleAvg (h ω) R z))
  let μH : Measure DistC := (P.prod BiLipschitz.OneScale.standardGaussian).map (BiLipschitz.OneScale.gaussianShift h)
  haveI : IsProbabilityMeasure μH :=
    (Measure.isProbabilityMeasure_map_iff
      (BiLipschitz.OneScale.gff_gaussianShift P h hh.1).measurable.aemeasurable).2 inferInstance
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  obtain ⟨S, hS, hLocal⟩ := canonical_ratio_local ξ Q D hD z r c μH
    (BiLipschitz.OneScale.canonical_gaussianShift_isGFFPlusCont P h hh.1)
    (BiLipschitz.OneScale.canonical_gaussianShift_barrier P h hh ξ Q hQ D hD)
  have hLocalProd : {p : Ω × ℝ | BiLipschitz.OneScale.gaussianShift h p ∈ rawRatioEvent D z r c}
      =ᵐ[P.prod BiLipschitz.OneScale.standardGaussian]
      {p : Ω × ℝ | restrictTo U (BiLipschitz.OneScale.gaussianShift h p) ∈ S} :=
    ae_of_ae_map (BiLipschitz.OneScale.gff_gaussianShift P h hh.1).measurable.aemeasurable hLocal
  have hInv := rawRatioEvent_shift_ae (P.prod BiLipschitz.OneScale.standardGaussian)
    (fun p : Ω × ℝ => h p.1)
    (BiLipschitz.OneScale.gff_prod_fst P BiLipschitz.OneScale.standardGaussian h hh.1)
    ξ Q D hD z r c (fun p : Ω × ℝ => p.2)
  have hAE : ∀ᵐ p ∂P.prod BiLipschitz.OneScale.standardGaussian,
      (h p.1 ∈ rawRatioEvent D z r c ↔
        BiLipschitz.OneScale.localShift U (q p.1) (circleAvg (h p.1) R z + p.2) ∈ S) := by
    filter_upwards [hInv, hLocalProd] with p hi hl
    have hShift : BiLipschitz.OneScale.localShift U (q p.1)
          (circleAvg (h p.1) R z + p.2) =
        restrictTo U (BiLipschitz.OneScale.gaussianShift h p) := by
      calc
        BiLipschitz.OneScale.localShift U (q p.1) (circleAvg (h p.1) R z + p.2) =
            restrictTo U (addConst (addConst (h p.1)
              (-circleAvg (h p.1) R z)) (circleAvg (h p.1) R z + p.2)) :=
          BiLipschitz.OneScale.localShift_restrictTo U _ _
        _ = restrictTo U (addConst (h p.1) p.2) := by
          rw [LQGMetric.GFFLaw.addConst_addConst]
          congr 1
          ring
        _ = restrictTo U (BiLipschitz.OneScale.gaussianShift h p) := rfl
    rw [hShift]
    exact hi.symm.trans (Iff.of_eq hl)
  have hSmooth := BiLipschitz.OneScale.gaussian_smoothing_event P U q
    (fun ω => circleAvg (h ω) R z)
    {ω | h ω ∈ rawRatioEvent D z r c} S hS hAE
  refine ⟨S, hS, ?_, ?_⟩
  · have hB : MeasurableSet
        {v : DistOn U | BiLipschitz.OneScale.gaussianSmooth U S v > 1 / 2} :=
      measurableSet_lt measurable_const (BiLipschitz.OneScale.measurable_gaussianSmooth U hS)
    exact hB.preimage (Measurable.of_comap_le le_rfl)
  · filter_upwards [hSmooth] with ω hω
    exact propext hω.symm


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio
