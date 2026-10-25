import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.EventShift




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale

open LQGMetric (DistC DistOn addConst circleAvg restrictTo)

 
theorem ebl_raw_centered_event_of_e1a
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hAXPOS_Q_pos : 0 < Q)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (z : ℂ) (r : Ioi (0 : ℝ)) (A : ℝ)
    (hE1a_around : ∀ d e : LSCMetric,
      d.internal (collarOpen z r : Set ℂ) = e.internal (collarOpen z r : Set ℂ) →
      aroundDist d (separatorAt z r) = aroundDist e (separatorAt z r))
    (R : Ioi (0 : ℝ)) :
    let U := collarOpen z r
    let q : Ω → DistOn U := fun ω =>
      restrictTo U (addConst (h ω) (-circleAvg (h ω) R z))
    ∃ S : Set (DistOn U), MeasurableSet S ∧
      MeasurableSet[MeasurableSpace.comap q inferInstance]
        {ω | gaussianSmooth U S (q ω) > 1 / 2} ∧
      {ω | gaussianSmooth U S (q ω) > 1 / 2} =ᵐ[P]
        {ω | h ω ∈ pairedRawEvent ξ Q D D' z r A} := by
  dsimp only
  let U := collarOpen z r
  let q : Ω → DistOn U := fun ω =>
    restrictTo U (addConst (h ω) (-circleAvg (h ω) R z))
  obtain ⟨S, hS, hLocal⟩ := ebl_canonical_local_event_of_e1a P h hh ξ Q hAXPOS_Q_pos
    D D' hD hD' z r A hE1a_around
  have hInv := pairedRawEvent_shift_ae (P.prod standardGaussian)
    (fun p : Ω × ℝ => h p.1) (gff_prod_fst P standardGaussian h hh.1)
    ξ Q D D' hD hD' z r A (fun p : Ω × ℝ => p.2)
  have hAE : ∀ᵐ p ∂P.prod standardGaussian,
      (h p.1 ∈ pairedRawEvent ξ Q D D' z r A ↔
        localShift U (q p.1) (circleAvg (h p.1) R z + p.2) ∈ S) := by
    filter_upwards [hInv, hLocal] with p hI hL
    have hShift : localShift U (q p.1) (circleAvg (h p.1) R z + p.2) =
        restrictTo U (gaussianShift h p) := by
      calc
        localShift U (q p.1) (circleAvg (h p.1) R z + p.2) =
            restrictTo U (addConst (addConst (h p.1)
              (-circleAvg (h p.1) R z)) (circleAvg (h p.1) R z + p.2)) :=
          localShift_restrictTo U _ _
        _ = restrictTo U (addConst (h p.1) p.2) := by
          rw [LQGMetric.GFFLaw.addConst_addConst]
          congr 1
          ring
        _ = restrictTo U (gaussianShift h p) := rfl
    rw [hShift]
    exact hI.symm.trans (Iff.of_eq hL)
  have hSmooth := gaussian_smoothing_event P U q
    (fun ω => circleAvg (h ω) R z)
    {ω | h ω ∈ pairedRawEvent ξ Q D D' z r A} S hS hAE
  refine ⟨S, hS, ?_, ?_⟩
  · have hB : MeasurableSet {v : DistOn U | gaussianSmooth U S v > 1 / 2} :=
      measurableSet_lt measurable_const (measurable_gaussianSmooth U hS)
    exact hB.preimage (Measurable.of_comap_le le_rfl)
  · filter_upwards [hSmooth] with ω hω
    exact propext hω.symm

 
theorem ae_all_centered_event_versions
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (E B : ℕ → Set Ω) (h : ∀ n, B n =ᵐ[P] E n) :
    ∀ᵐ ω ∂P, ∀ n, (ω ∈ B n) = (ω ∈ E n) :=
  ae_all_iff.mpr h


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale
