import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.ELocalA




 

















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC DistOn addConst restrictTo)

theorem sphere_subset_carrier (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Metric.sphere z r ⊆ TwoScale.S36Events.eventCarrier z r := by
  intro y hy
  rw [Metric.mem_sphere] at hy
  refine ⟨Metric.mem_closedBall.mpr (by linarith), ?_⟩
  rw [Metric.mem_ball, not_lt]
  linarith

 
theorem canonical_attained_local {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (cMinus cPlus : ℝ≥0∞) (hm0 : 0 < cMinus) (hMt : cPlus < ⊤)
    (hm : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hM : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (K : Ioi (1 : ℝ)) (C θ : Ioi (0 : ℝ)) (U : TopologicalSpace.Opens ℂ)
    (hYU : TwoScale.S36Events.eventCarrier z r ⊆ U) :
    ∃ S : Set (DistOn U), MeasurableSet S ∧
      TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q z r q a K C θ cMinus.toReal cPlus.toReal =ᵐ[muH P h]
        restrictTo U ⁻¹' S := by
  have hprob := muH_isProb P h hh.1
  have hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) (muH P h) :=
    BiLipschitz.OneScale.canonical_gaussianShift_isGFFPlusCont P h hh.1
  have hr : (0 : ℝ) < r := r.2
  set E := TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q z r q a K C θ cMinus.toReal cPlus.toReal
  
  obtain ⟨FD, -, hlocD⟩ := hD.locality (muH P h) id hμ U
  obtain ⟨FD', -, hlocD'⟩ := hD'.locality (muH P h) id hμ U
  have hopt := muH_ae_optima P h hh ξ Q D D' hD hD' cMinus cPlus hm hM
  have hpair := muH_ae_ratioPair P h hh ξ Q D hD
  have hle : cMinus ≤ cPlus := by
    obtain ⟨g, hg, hp⟩ := (hopt.and hpair).exists
    rw [← hg.1, ← hg.2.1]
    exact OptimalConstants.Ratios.lowerOptimal_le_upperOptimal hp
  have hmt : cMinus ≠ ⊤ := ne_top_of_le_ne_top hMt.ne hle
  have hCm : 0 < cMinus.toReal := ENNReal.toReal_pos hm0.ne' hmt
  have hCmp : cMinus.toReal ≤ cPlus.toReal := ENNReal.toReal_mono hMt.ne hle
  have hofm : ENNReal.ofReal cMinus.toReal = cMinus := ENNReal.ofReal_toReal hmt
  have hofM : ENNReal.ofReal cPlus.toReal = cPlus := ENNReal.ofReal_toReal hMt.ne
  have hGood : ∀ᵐ g ∂(muH P h), BiLipschitz.Barrier.Barrier (D g) ∧ BiLipschitz.Barrier.Barrier (D' g) ∧
      (D g).IsLengthSpace ∧ (D' g).IsLengthSpace ∧
      (∀ x y, ENNReal.ofReal cMinus.toReal * D g (x, y) ≤ D' g (x, y) ∧
        D' g (x, y) ≤ ENNReal.ofReal cPlus.toReal * D g (x, y)) ∧
      OptimalConstants.Ratios.setDist (D g) (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) < ⊤ ∧
      (D g).internal U = FD (restrictTo U g) ∧ (D' g).internal U = FD' (restrictTo U g) := by
    filter_upwards [BiLipschitz.OneScale.canonical_gaussianShift_barrier P h hh ξ Q hQ D hD,
      BiLipschitz.OneScale.canonical_gaussianShift_barrier P h hh ξ Q hQ D' hD',
      hD.length (muH P h) id hμ, hD'.length (muH P h) id hμ, hopt,
      muH_ae_middle_lt_top P h hh ξ Q D hD z r, hlocD, hlocD'] with g h1 h2 h3 h4 h5 h6 h7 h8
    refine ⟨h1, h2, h3, h4, fun x y => ?_, h6, h7, h8⟩
    rw [hofm, hofM]
    exact h5.2.2 x y
  obtain ⟨W, hWae, hWm, hWsub⟩ := hGood.exists_measurable_mem
  let R : DistC → LQGMetric.CoordJ → ℝ := fun g => LQGMetric.pairJ U (restrictTo U g)
  have hR : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp (LQGMetric.measurable_restrictTo U)
  have hV : Measurable[LQGMetric.Blueprint.fieldSigma id U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hsU : Metric.sphere z (r : ℝ) ⊆ U := (sphere_subset_carrier z hr).trans hYU
  have hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ E → g₂ ∈ E := by
    intro g₁ hg₁ g₂ hg₂ he hE₁
    have hres : restrictTo U g₁ = restrictTo U g₂ := LQGMetric.injective_pairJ U he
    obtain ⟨hB₁, hB₁', hL₁, hL₁', hc₁, hm₁, hi₁, hi₁'⟩ := hWsub g₁ hg₁
    obtain ⟨hB₂, hB₂', hL₂, hL₂', hc₂, hm₂, hi₂, hi₂'⟩ := hWsub g₂ hg₂
    have hId : ∀ x y, intExt (D g₁) U x y = intExt (D g₂) U x y :=
      intExt_eq_of_internal_eq (by rw [hi₁, hi₂, hres])
    have hIe : ∀ x y, intExt (D' g₁) U x y = intExt (D' g₂) U x y :=
      intExt_eq_of_internal_eq (by rw [hi₁', hi₂', hres])
    obtain ⟨c, hc, hA⟩ := hE₁
    exact ⟨c, (isCircleAverage_congr_restrict hres r z hsU c).mp hc,
      attained_transfer hB₁ hB₁' hB₂ hB₂' hL₁ hL₁' hL₂ hL₂' hCm hCmp hc₁ hc₂ (ξ : ℝ) Q z r q a
        K C θ c hm₁ hm₂ hYU hId hIe hA⟩
  have hB : NullMeasurableSet E ((muH P h).map id) :=
    (AttainedEvent_um D D' hD.measurable hD'.measurable (ξ : ℝ) Q z r q a K C θ
      cMinus.toReal cPlus.toReal) _ inferInstance
  have hLocal := LQGMetric.LocalEvent.aeEventIn_of_saturated
    (Y := id) (R := R) (V := R) (B := E) (W := W)
    measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl) hWm hB hWae hsat
  obtain ⟨F, hFm, hFe⟩ := hLocal
  obtain ⟨S, hS, hF⟩ := MeasurableSpace.measurableSet_comap.mp hFm
  refine ⟨S, hS, ?_⟩
  rw [← hF] at hFe
  exact hFe

 


theorem attained_centered_local {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (cMinus cPlus : ℝ≥0∞) (hm0 : 0 < cMinus) (hMt : cPlus < ⊤)
    (hm : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hM : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (K : Ioi (1 : ℝ)) (C θ : Ioi (0 : ℝ)) (U : TopologicalSpace.Opens ℂ)
    (hYU : TwoScale.S36Events.eventCarrier z r ⊆ U) (R : ℝ) :
    LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => addConst (h ω) (-LQGMetric.circleAvg (h ω) R z)) U)
      {ω | h ω ∈ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q z r q a K C θ
        cMinus.toReal cPlus.toReal} := by
  set E := TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q z r q a K C θ cMinus.toReal cPlus.toReal
  let q' : Ω → DistOn U := fun ω => restrictTo U (addConst (h ω) (-LQGMetric.circleAvg (h ω) R z))
  obtain ⟨S, hS, hLocal⟩ := canonical_attained_local P h hh ξ Q hQ D D' hD hD' cMinus cPlus
    hm0 hMt hm hM z r q a K C θ U hYU
  have hmeasH := (BiLipschitz.OneScale.gff_gaussianShift P h hh.1).measurable
  have hLocalProd : {x : Ω × ℝ | BiLipschitz.OneScale.gaussianShift h x ∈ E}
      =ᵐ[P.prod BiLipschitz.OneScale.standardGaussian]
      {x : Ω × ℝ | restrictTo U (BiLipschitz.OneScale.gaussianShift h x) ∈ S} :=
    ae_of_ae_map hmeasH.aemeasurable hLocal
  have hprod : LQGMetric.IsGFFPlusCont (fun x : Ω × ℝ => h x.1)
      (P.prod BiLipschitz.OneScale.standardGaussian) :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp (BiLipschitz.OneScale.gff_prod_fst P BiLipschitz.OneScale.standardGaussian h hh.1)
  have hInv := ae_attainedEvent_addConst_iff (P.prod BiLipschitz.OneScale.standardGaussian) (fun x => h x.1)
    hprod ξ Q D D' hD hD' z r q a K C θ cMinus.toReal cPlus.toReal (fun x => x.2)
  have hAE : ∀ᵐ x ∂P.prod BiLipschitz.OneScale.standardGaussian,
      (h x.1 ∈ E ↔
        BiLipschitz.OneScale.localShift U (q' x.1) (LQGMetric.circleAvg (h x.1) R z + x.2) ∈ S) := by
    filter_upwards [hInv, hLocalProd] with x hi hl
    have hShift : BiLipschitz.OneScale.localShift U (q' x.1) (LQGMetric.circleAvg (h x.1) R z + x.2) =
        restrictTo U (BiLipschitz.OneScale.gaussianShift h x) := by
      calc
        BiLipschitz.OneScale.localShift U (q' x.1) (LQGMetric.circleAvg (h x.1) R z + x.2) =
            restrictTo U (addConst (addConst (h x.1) (-LQGMetric.circleAvg (h x.1) R z))
              (LQGMetric.circleAvg (h x.1) R z + x.2)) :=
          BiLipschitz.OneScale.localShift_restrictTo U _ _
        _ = restrictTo U (addConst (h x.1) x.2) := by
          rw [LQGMetric.GFFLaw.addConst_addConst]
          congr 2
          ring
        _ = restrictTo U (BiLipschitz.OneScale.gaussianShift h x) := rfl
    rw [hShift]
    exact hi.symm.trans (Iff.of_eq hl)
  have hSmooth := BiLipschitz.OneScale.gaussian_smoothing_event P U q'
    (fun ω => LQGMetric.circleAvg (h ω) R z) {ω | h ω ∈ E} S hS hAE
  refine ⟨{ω | BiLipschitz.OneScale.gaussianSmooth U S (q' ω) > 1 / 2}, ?_, ?_⟩
  · have hB : MeasurableSet {v : DistOn U | BiLipschitz.OneScale.gaussianSmooth U S v > 1 / 2} :=
      measurableSet_lt measurable_const (BiLipschitz.OneScale.measurable_gaussianSmooth U hS)
    exact hB.preimage (Measurable.of_comap_le le_rfl)
  · filter_upwards [hSmooth] with ω hω
    exact propext hω

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
