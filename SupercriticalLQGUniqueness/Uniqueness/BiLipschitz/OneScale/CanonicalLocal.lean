import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.AroundTranslate
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Meas
import LQGMetric.Meas.LocalEvent
import LQGMetric.Field.StandardBorelRange
import LQGMetric.Papers.DG.S3P18R1




 





set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale

open LQGMetric (DistC DistOn circleAvg restrictTo)
open SupercriticalLQGUniqueness

 
def crossingAt (z : ℂ) (r : Ioi (0 : ℝ)) : EuclideanAnnulus :=
  Positivity.Witnesses.annulusTranslate (crossingShape.dilate r r.2) z

def separatorAt (z : ℂ) (r : Ioi (0 : ℝ)) : EuclideanAnnulus :=
  Positivity.Witnesses.annulusTranslate (separatorShape.dilate r r.2) z

 
def collarAnnulus (z : ℂ) (r : Ioi (0 : ℝ)) : EuclideanAnnulus :=
  ⟨(z, (r : ℝ) / 2, 4 * (r : ℝ)), by
    have hr : 0 < (r : ℝ) := r.2
    constructor <;> dsimp <;> nlinarith⟩

def collarOpen (z : ℂ) (r : Ioi (0 : ℝ)) : TopologicalSpace.Opens ℂ :=
  ⟨(collarAnnulus z r).toSet, Toolkit.CountableBase.annulus_toSet_open _⟩

private theorem closed_crossing_subset_collar (z : ℂ) (r : Ioi (0 : ℝ)) :
    BiLipschitz.Barrier.closedAnn (crossingAt z r).center (crossingAt z r).innerRadius
      (crossingAt z r).outerRadius ⊆ (collarOpen z r : Set ℂ) := by
  intro w hw
  have hr : 0 < (r : ℝ) := r.2
  have hrad : (r : ℝ) ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ 2 * (r : ℝ) := by
    simpa only [BiLipschitz.Barrier.closedAnn, crossingAt, crossingShape, Positivity.Witnesses.annulusTranslate,
      EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
      EuclideanAnnulus.outerRadius, EuclideanAnnulus.dilate,
      smul_zero, zero_add, mul_one, mul_comm, Set.mem_ofPred_eq] using hw
  change w ∈ (collarAnnulus z r).toSet
  unfold EuclideanAnnulus.toSet
  simp only [collarAnnulus, EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
    EuclideanAnnulus.outerRadius]
  rw [closure_ball z ((div_pos r.2 (by norm_num)).ne')]
  simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le,
    dist_eq_norm]
  constructor <;> nlinarith [hrad.1, hrad.2]

private theorem circle_subset_collar (z : ℂ) (r : Ioi (0 : ℝ)) :
    Metric.sphere z r ⊆ (collarOpen z r : Set ℂ) := by
  intro w hw
  have hr : 0 < (r : ℝ) := r.2
  have hrad : ‖w - z‖ = (r : ℝ) := by simpa only [Metric.mem_sphere, dist_eq_norm] using hw
  change w ∈ (collarAnnulus z r).toSet
  unfold EuclideanAnnulus.toSet
  simp only [collarAnnulus, EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
    EuclideanAnnulus.outerRadius]
  rw [closure_ball z ((div_pos r.2 (by norm_num)).ne')]
  simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le,
    dist_eq_norm]
  constructor <;> nlinarith

 
def pairedRawEvent (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ)) (A : ℝ) :
    Set DistC := {g |
      ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * circleAvg g r z)) ≤ acrossDist (D g) (crossingAt z r) ∧
      aroundDist (D' g) (separatorAt z r) ≤
        ENNReal.ofReal (A * (r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg g r z))}

theorem measurableSet_pairedRawEvent (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (hD' : IsWeakLQGMetric ξ Q D') (z : ℂ) (r : Ioi (0 : ℝ)) (A : ℝ) :
    MeasurableSet (pairedRawEvent ξ Q D D' z r A) := by
  have hca : Measurable fun g : DistC => circleAvg g r z :=
    LQGMetric.measurable_circleAvg_left r z
  have hAc : Measurable fun g : DistC => acrossDist (D g) (crossingAt z r) :=
    (measurable_acrossDist _).comp hD.measurable
  have hAr : Measurable fun g : DistC => aroundDist (D' g) (separatorAt z r) :=
    (Toolkit.CountableBase.aroundBoundedAnnulus_borel _).comp hD'.measurable
  unfold pairedRawEvent
  exact (measurableSet_le
      ((measurable_const.mul
        ((Real.measurable_exp.comp (measurable_const.mul hca)))).ennreal_ofReal) hAc).inter
    (measurableSet_le hAr
      ((measurable_const.mul
        ((Real.measurable_exp.comp (measurable_const.mul hca)))).ennreal_ofReal))

 

theorem canonical_local_event_of_e1a
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (z : ℂ) (r : Ioi (0 : ℝ)) (A : ℝ)
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ)
    (hBarrier : ∀ᵐ g ∂μ, BiLipschitz.Barrier.Barrier (D g))
    (hE1a_around : ∀ d e : LSCMetric,
      d.internal (collarOpen z r : Set ℂ) = e.internal (collarOpen z r : Set ℂ) →
      aroundDist d (separatorAt z r) = aroundDist e (separatorAt z r)) :
    ∃ S : Set (DistOn (collarOpen z r)), MeasurableSet S ∧
      pairedRawEvent ξ Q D D' z r A =ᵐ[μ]
        (restrictTo (collarOpen z r) ⁻¹' S) := by
  let U := collarOpen z r
  let B := pairedRawEvent ξ Q D D' z r A
  obtain ⟨FD, _, hLocD⟩ := hD.locality μ id hμ U
  obtain ⟨FD', _, hLocD'⟩ := hD'.locality μ id hμ U
  have hLenD := hD.length μ id hμ
  have hLenD' := hD'.length μ id hμ
  obtain ⟨NLD, hNLDsub, hNLDm, hNLDnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hLenD)
  obtain ⟨NLD', hNLD'sub, hNLD'm, hNLD'null⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hLenD')
  obtain ⟨NCD, hNCDsub, hNCDm, hNCDnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hLocD)
  obtain ⟨NCD', hNCD'sub, hNCD'm, hNCD'null⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hLocD')
  let W : Set DistC := {g | g ∉ NLD ∧ g ∉ NLD' ∧ g ∉ NCD ∧ g ∉ NCD' ∧
    BiLipschitz.Barrier.Barrier (D g)}
  have hW : MeasurableSet W := by
    have hWeq : W = NLDᶜ ∩ NLD'ᶜ ∩ NCDᶜ ∩ NCD'ᶜ ∩
        {g | BiLipschitz.Barrier.Barrier (D g)} := by
      ext g
      simp only [W, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    rw [hWeq]
    exact ((((hNLDm.compl.inter hNLD'm.compl).inter hNCDm.compl).inter
      hNCD'm.compl).inter (BiLipschitz.Barrier.measurableSet_barrier hD.measurable))
  have hYW : ∀ᵐ g ∂μ, g ∈ W := by
    have h₁ : ∀ᵐ g ∂μ, g ∉ NLD := ae_iff.2 (by simpa using hNLDnull)
    have h₂ : ∀ᵐ g ∂μ, g ∉ NLD' := ae_iff.2 (by simpa using hNLD'null)
    have h₃ : ∀ᵐ g ∂μ, g ∉ NCD := ae_iff.2 (by simpa using hNCDnull)
    have h₄ : ∀ᵐ g ∂μ, g ∉ NCD' := ae_iff.2 (by simpa using hNCD'null)
    filter_upwards [h₁, h₂, h₃, h₄, hBarrier] with g hg₁ hg₂ hg₃ hg₄ hgB
    exact ⟨hg₁, hg₂, hg₃, hg₄, hgB⟩
  obtain ⟨Ψ, _, hΨ⟩ := LQGMetric.DG.r18_circ_factor U r.2
    (circle_subset_collar z r)
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
      exact hg₁.2.2.1 (hNCDsub hn)
    have hI₂ : (D g₂).internal (U : Set ℂ) = FD (restrictTo U g₂) := by
      by_contra hn
      exact hg₂.2.2.1 (hNCDsub hn)
    have hI'₁ : (D' g₁).internal (U : Set ℂ) = FD' (restrictTo U g₁) := by
      by_contra hn
      exact hg₁.2.2.2.1 (hNCD'sub hn)
    have hI'₂ : (D' g₂).internal (U : Set ℂ) = FD' (restrictTo U g₂) := by
      by_contra hn
      exact hg₂.2.2.2.1 (hNCD'sub hn)
    have hint : (D g₁).internal (U : Set ℂ) = (D g₂).internal (U : Set ℂ) := by
      calc
        _ = FD (restrictTo U g₁) := hI₁
        _ = FD (restrictTo U g₂) := by rw [hrest]
        _ = _ := hI₂.symm
    have hint' : (D' g₁).internal (U : Set ℂ) = (D' g₂).internal (U : Set ℂ) := by
      calc
        _ = FD' (restrictTo U g₁) := hI'₁
        _ = FD' (restrictTo U g₂) := by rw [hrest]
        _ = _ := hI'₂.symm
    have hcross : acrossDist (D g₁) (crossingAt z r) =
        acrossDist (D g₂) (crossingAt z r) := by
      rw [BiLipschitz.Barrier.acrossDist_eq_iInf_internal (D g₁) hg₁.2.2.2.2 hl₁
        (crossingAt z r) (closed_crossing_subset_collar z r),
        BiLipschitz.Barrier.acrossDist_eq_iInf_internal (D g₂) hg₂.2.2.2.2 hl₂
          (crossingAt z r) (closed_crossing_subset_collar z r), hint]
    have haround : aroundDist (D' g₁) (separatorAt z r) =
        aroundDist (D' g₂) (separatorAt z r) :=
      hE1a_around (D' g₁) (D' g₂) hint'
    have hcircle : circleAvg g₁ r z = circleAvg g₂ r z := by
      rw [hΨ g₁, hΨ g₂, hrest]
    change (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * circleAvg g₂ r z)) ≤ acrossDist (D g₂) (crossingAt z r) ∧
      aroundDist (D' g₂) (separatorAt z r) ≤
        ENNReal.ofReal (A * (r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg g₂ r z)))
    change (ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * circleAvg g₁ r z)) ≤ acrossDist (D g₁) (crossingAt z r) ∧
      aroundDist (D' g₁) (separatorAt z r) ≤
        ENNReal.ofReal (A * (r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg g₁ r z))) at hB₁
    rwa [hcircle, hcross, haround] at hB₁
  have hLocal := LQGMetric.LocalEvent.aeEventIn_of_saturated
    (Y := id) (R := R) (V := R) (B := B) (W := W)
    measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl)
    hW (measurableSet_pairedRawEvent ξ Q D D' hD hD' z r A).nullMeasurableSet
    hYW hsat
  obtain ⟨F, hFm, hFe⟩ := hLocal
  obtain ⟨S, hS, hF⟩ := MeasurableSpace.measurableSet_comap.mp hFm
  refine ⟨S, hS, ?_⟩
  rw [← hF] at hFe
  simpa [B, U] using hFe


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale
