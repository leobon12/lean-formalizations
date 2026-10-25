import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.AroundLocality
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.RatioMarginal.OneAnnulus




 
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio

open LQGMetric (DistC DistOn restrictTo addConst circleAvg)

def rawRatioEvent (D : DistC → LSCMetric) (z : ℂ)
    (r : Ioi (0 : ℝ)) (c : ℝ≥0∞) : Set DistC :=
  {g | aroundDist (D g) (BiLipschitz.OneScale.crossingAt z r) ≤
    c * acrossDist (D g) (BiLipschitz.OneScale.crossingAt z r)}

theorem measurableSet_rawRatioEvent (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (z : ℂ) (r : Ioi (0 : ℝ)) (c : ℝ≥0∞) :
    MeasurableSet (rawRatioEvent D z r c) := by
  unfold rawRatioEvent
  exact measurableSet_le
    ((Toolkit.CountableBase.aroundBoundedAnnulus_borel _).comp hD.measurable)
    (measurable_const.mul ((measurable_acrossDist _).comp hD.measurable))

private theorem closed_crossing_subset_collar (z : ℂ) (r : Ioi (0 : ℝ)) :
    BiLipschitz.Barrier.closedAnn (BiLipschitz.OneScale.crossingAt z r).center
      (BiLipschitz.OneScale.crossingAt z r).innerRadius
      (BiLipschitz.OneScale.crossingAt z r).outerRadius ⊆
      (BiLipschitz.OneScale.collarOpen z r : Set ℂ) := by
  intro w hw
  have hrad : (r : ℝ) ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ 2 * (r : ℝ) := by
    simpa only [BiLipschitz.Barrier.closedAnn, BiLipschitz.OneScale.crossingAt, BiLipschitz.OneScale.crossingShape,
      Positivity.Witnesses.annulusTranslate, EuclideanAnnulus.center,
      EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius,
      EuclideanAnnulus.dilate, smul_zero, zero_add, mul_one, mul_comm,
      Set.mem_ofPred_eq] using hw
  have hr : 0 < (r : ℝ) := r.2
  change w ∈ (BiLipschitz.OneScale.collarAnnulus z r).toSet
  unfold EuclideanAnnulus.toSet
  simp only [BiLipschitz.OneScale.collarAnnulus, EuclideanAnnulus.center,
    EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius]
  rw [closure_ball z ((div_pos r.2 (by norm_num)).ne')]
  simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le,
    dist_eq_norm]
  constructor <;> nlinarith [hr, hrad.1, hrad.2]

private theorem crossing_toSet_subset_collar (z : ℂ) (r : Ioi (0 : ℝ)) :
    (BiLipschitz.OneScale.crossingAt z r).toSet ⊆ (BiLipschitz.OneScale.collarOpen z r : Set ℂ) := by
  intro w hw
  apply closed_crossing_subset_collar z r
  change (BiLipschitz.OneScale.crossingAt z r).innerRadius ≤ ‖w - (BiLipschitz.OneScale.crossingAt z r).center‖ ∧
    ‖w - (BiLipschitz.OneScale.crossingAt z r).center‖ ≤ (BiLipschitz.OneScale.crossingAt z r).outerRadius
  have h := hw
  unfold EuclideanAnnulus.toSet at h
  rw [closure_ball _ (ne_of_gt (BiLipschitz.OneScale.crossingAt z r).innerRadius_pos)] at h
  simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le,
    dist_eq_norm] at h
  exact ⟨h.2.le, h.1.le⟩

 

theorem canonical_ratio_local
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (z : ℂ) (r : Ioi (0 : ℝ)) (c : ℝ≥0∞)
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ)
    (hBarrier : ∀ᵐ g ∂μ, BiLipschitz.Barrier.Barrier (D g)) :
    ∃ S : Set (DistOn (BiLipschitz.OneScale.collarOpen z r)), MeasurableSet S ∧
      rawRatioEvent D z r c =ᵐ[μ]
        (restrictTo (BiLipschitz.OneScale.collarOpen z r) ⁻¹' S) := by
  let U := BiLipschitz.OneScale.collarOpen z r
  let B := rawRatioEvent D z r c
  obtain ⟨FD, _, hLocD⟩ := hD.locality μ id hμ U
  have hLenD := hD.length μ id hμ
  obtain ⟨NLD, hNLDsub, hNLDm, hNLDnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hLenD)
  obtain ⟨NCD, hNCDsub, hNCDm, hNCDnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hLocD)
  let W : Set DistC := {g | g ∉ NLD ∧ g ∉ NCD ∧ BiLipschitz.Barrier.Barrier (D g)}
  have hW : MeasurableSet W := by
    have heq : W = NLDᶜ ∩ NCDᶜ ∩ {g | BiLipschitz.Barrier.Barrier (D g)} := by
      ext g
      simp only [W, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    rw [heq]
    exact (hNLDm.compl.inter hNCDm.compl).inter
      (BiLipschitz.Barrier.measurableSet_barrier hD.measurable)
  have hYW : ∀ᵐ g ∂μ, g ∈ W := by
    have h₁ : ∀ᵐ g ∂μ, g ∉ NLD := ae_iff.2 (by simpa using hNLDnull)
    have h₂ : ∀ᵐ g ∂μ, g ∉ NCD := ae_iff.2 (by simpa using hNCDnull)
    filter_upwards [h₁, h₂, hBarrier] with g hg₁ hg₂ hgB
    exact ⟨hg₁, hg₂, hgB⟩
  let R : DistC → LQGMetric.CoordJ → ℝ :=
    fun g => LQGMetric.pairJ U (restrictTo U g)
  have hR : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp (LQGMetric.measurable_restrictTo U)
  have hV : Measurable[LQGMetric.Blueprint.fieldSigma id U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B := by
    intro g₁ hg₁ g₂ hg₂ hcode hB₁
    have hrest : restrictTo U g₁ = restrictTo U g₂ :=
      LQGMetric.injective_pairJ U hcode
    have hl₁ : (D g₁).IsLengthSpace := by
      by_contra hn
      exact hg₁.1 (hNLDsub hn)
    have hl₂ : (D g₂).IsLengthSpace := by
      by_contra hn
      exact hg₂.1 (hNLDsub hn)
    have hI₁ : (D g₁).internal (U : Set ℂ) = FD (restrictTo U g₁) := by
      by_contra hn
      exact hg₁.2.1 (hNCDsub hn)
    have hI₂ : (D g₂).internal (U : Set ℂ) = FD (restrictTo U g₂) := by
      by_contra hn
      exact hg₂.2.1 (hNCDsub hn)
    have hint : (D g₁).internal (U : Set ℂ) = (D g₂).internal (U : Set ℂ) := by
      calc
        _ = FD (restrictTo U g₁) := hI₁
        _ = FD (restrictTo U g₂) := by rw [hrest]
        _ = _ := hI₂.symm
    have hcross : acrossDist (D g₁) (BiLipschitz.OneScale.crossingAt z r) =
        acrossDist (D g₂) (BiLipschitz.OneScale.crossingAt z r) := by
      rw [BiLipschitz.Barrier.acrossDist_eq_iInf_internal (D g₁) hg₁.2.2 hl₁
        (BiLipschitz.OneScale.crossingAt z r) (closed_crossing_subset_collar z r),
        BiLipschitz.Barrier.acrossDist_eq_iInf_internal (D g₂) hg₂.2.2 hl₂
          (BiLipschitz.OneScale.crossingAt z r) (closed_crossing_subset_collar z r), hint]
    have haround : aroundDist (D g₁) (BiLipschitz.OneScale.crossingAt z r) =
        aroundDist (D g₂) (BiLipschitz.OneScale.crossingAt z r) :=
      BiLipschitz.EqualNormalizer.aroundDist_eq_of_internal_eq _ _ (U : Set ℂ) hint _
        (crossing_toSet_subset_collar z r)
    change aroundDist (D g₂) (BiLipschitz.OneScale.crossingAt z r) ≤
      c * acrossDist (D g₂) (BiLipschitz.OneScale.crossingAt z r)
    change aroundDist (D g₁) (BiLipschitz.OneScale.crossingAt z r) ≤
      c * acrossDist (D g₁) (BiLipschitz.OneScale.crossingAt z r) at hB₁
    rwa [← haround, ← hcross]
  have hLocal := LQGMetric.LocalEvent.aeEventIn_of_saturated
    (Y := id) (R := R) (V := R) (B := B) (W := W)
    measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl)
    hW (measurableSet_rawRatioEvent ξ Q D hD z r c).nullMeasurableSet
    hYW hsat
  obtain ⟨F, hFm, hFe⟩ := hLocal
  obtain ⟨S, hS, hF⟩ := MeasurableSpace.measurableSet_comap.mp hFm
  refine ⟨S, hS, ?_⟩
  rw [← hF] at hFe
  simpa [B, U] using hFe


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio
