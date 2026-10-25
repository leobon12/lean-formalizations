import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.S8Marg
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio.RatioCentered




 






















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9

open LQGMetric (DistC DistOn restrictTo addConst circleAvg)

 

theorem canonical_local_of_internal (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (U : TopologicalSpace.Opens ℂ) (B : Set DistC)
    (hB : MeasurableSet B)
    (hdet : ∀ g₁ g₂ : DistC, BiLipschitz.Barrier.Barrier (D g₁) → BiLipschitz.Barrier.Barrier (D g₂) →
      (D g₁).IsLengthSpace → (D g₂).IsLengthSpace →
      (D g₁).internal (U : Set ℂ) = (D g₂).internal (U : Set ℂ) → g₁ ∈ B → g₂ ∈ B)
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ)
    (hBarrier : ∀ᵐ g ∂μ, BiLipschitz.Barrier.Barrier (D g)) :
    ∃ S : Set (DistOn U), MeasurableSet S ∧ B =ᵐ[μ] (restrictTo U ⁻¹' S) := by
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
    exact (hNLDm.compl.inter hNCDm.compl).inter (BiLipschitz.Barrier.measurableSet_barrier hD.measurable)
  have hYW : ∀ᵐ g ∂μ, g ∈ W := by
    have h₁ : ∀ᵐ g ∂μ, g ∉ NLD := ae_iff.2 (by simpa using hNLDnull)
    have h₂ : ∀ᵐ g ∂μ, g ∉ NCD := ae_iff.2 (by simpa using hNCDnull)
    filter_upwards [h₁, h₂, hBarrier] with g hg₁ hg₂ hgB
    exact ⟨hg₁, hg₂, hgB⟩
  let R : DistC → LQGMetric.CoordJ → ℝ := fun g => LQGMetric.pairJ U (restrictTo U g)
  have hR : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp (LQGMetric.measurable_restrictTo U)
  have hV : Measurable[LQGMetric.Blueprint.fieldSigma id U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B := by
    intro g₁ hg₁ g₂ hg₂ hcode hB₁
    have hrest : restrictTo U g₁ = restrictTo U g₂ := LQGMetric.injective_pairJ U hcode
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
    exact hdet g₁ g₂ hg₁.2.2 hg₂.2.2 hl₁ hl₂ hint hB₁
  have hLocal := LQGMetric.LocalEvent.aeEventIn_of_saturated
    (Y := id) (R := R) (V := R) (B := B) (W := W)
    measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl)
    hW hB.nullMeasurableSet hYW hsat
  obtain ⟨F, hFm, hFe⟩ := hLocal
  obtain ⟨S, hS, hF⟩ := MeasurableSpace.measurableSet_comap.mp hFm
  refine ⟨S, hS, ?_⟩
  rw [← hF] at hFe
  simpa using hFe

 



theorem centered_local_of_internal
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (U : TopologicalSpace.Opens ℂ) (B : Set DistC) (hB : MeasurableSet B)
    (hdet : ∀ g₁ g₂ : DistC, BiLipschitz.Barrier.Barrier (D g₁) → BiLipschitz.Barrier.Barrier (D g₂) →
      (D g₁).IsLengthSpace → (D g₂).IsLengthSpace →
      (D g₁).internal (U : Set ℂ) = (D g₂).internal (U : Set ℂ) → g₁ ∈ B → g₂ ∈ B)
    (hinv : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (h' : Ω' → DistC), LQGMetric.IsWholePlaneGFF h' P' → ∀ t : Ω' → ℝ,
      ∀ᵐ ω ∂P', (addConst (h' ω) (t ω) ∈ B ↔ h' ω ∈ B))
    (z : ℂ) (R : ℝ) :
    LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) R z)) U)
      {ω | h ω ∈ B} := by
  let q : Ω → DistOn U := fun ω => restrictTo U (addConst (h ω) (-circleAvg (h ω) R z))
  let μH : Measure DistC := (P.prod BiLipschitz.OneScale.standardGaussian).map (BiLipschitz.OneScale.gaussianShift h)
  have : IsProbabilityMeasure μH :=
    (Measure.isProbabilityMeasure_map_iff
      (BiLipschitz.OneScale.gff_gaussianShift P h hh.1).measurable.aemeasurable).2 inferInstance
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  obtain ⟨S, hS, hLocal⟩ := canonical_local_of_internal ξ Q D hD U B hB hdet μH
    (BiLipschitz.OneScale.canonical_gaussianShift_isGFFPlusCont P h hh.1)
    (BiLipschitz.OneScale.canonical_gaussianShift_barrier P h hh ξ Q hQ D hD)
  have hLocalProd : {p : Ω × ℝ | BiLipschitz.OneScale.gaussianShift h p ∈ B}
      =ᵐ[P.prod BiLipschitz.OneScale.standardGaussian]
      {p : Ω × ℝ | restrictTo U (BiLipschitz.OneScale.gaussianShift h p) ∈ S} :=
    ae_of_ae_map (BiLipschitz.OneScale.gff_gaussianShift P h hh.1).measurable.aemeasurable hLocal
  have hInv := hinv (Ω × ℝ) (P.prod BiLipschitz.OneScale.standardGaussian) (fun p : Ω × ℝ => h p.1)
    (BiLipschitz.OneScale.gff_prod_fst P BiLipschitz.OneScale.standardGaussian h hh.1) (fun p : Ω × ℝ => p.2)
  have hAE : ∀ᵐ p ∂P.prod BiLipschitz.OneScale.standardGaussian,
      (h p.1 ∈ B ↔ BiLipschitz.OneScale.localShift U (q p.1) (circleAvg (h p.1) R z + p.2) ∈ S) := by
    filter_upwards [hInv, hLocalProd] with p hi hl
    have hShift : BiLipschitz.OneScale.localShift U (q p.1) (circleAvg (h p.1) R z + p.2) =
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
    (fun ω => circleAvg (h ω) R z) {ω | h ω ∈ B} S hS hAE
  refine ⟨{ω | BiLipschitz.OneScale.gaussianSmooth U S (q ω) > 1 / 2}, ?_, ?_⟩
  · have hBm : MeasurableSet {v : DistOn U | BiLipschitz.OneScale.gaussianSmooth U S v > 1 / 2} :=
      measurableSet_lt measurable_const (BiLipschitz.OneScale.measurable_gaussianSmooth U hS)
    exact hBm.preimage (Measurable.of_comap_le le_rfl)
  · filter_upwards [hSmooth] with ω hω
    exact propext hω

 

 
theorem supOuter_toSet_subset {R : ℝ} (hR : 0 < R) (w : ℂ) :
    (supOuter hR w).toSet ⊆ (LQGMetric.Blueprint.annulus w R (3 * R) : Set ℂ) := by
  intro y hy
  have hy' : y ∈ Metric.ball w ((3 - 1 / 20) * R) ∧
      y ∉ closure (Metric.ball w ((2 + 1 / 20) * R)) := hy
  rw [closure_ball w (by positivity), Metric.mem_ball, Metric.mem_closedBall, not_le] at hy'
  simp only [dist_eq_norm] at hy'
  change R < ‖y - w‖ ∧ ‖y - w‖ < 3 * R
  constructor <;> nlinarith [hy'.1, hy'.2]

 
theorem supInner_closed_subset {R : ℝ} (hR : 0 < R) (w : ℂ) :
    BiLipschitz.Barrier.closedAnn (supInner hR w).center (supInner hR w).innerRadius
      (supInner hR w).outerRadius ⊆ (LQGMetric.Blueprint.annulus w R (3 * R) : Set ℂ) := by
  intro y hy
  have hy' : (1 + 1 / 20) * R ≤ ‖y - w‖ ∧ ‖y - w‖ ≤ (2 - 1 / 20) * R := hy
  change R < ‖y - w‖ ∧ ‖y - w‖ < 3 * R
  constructor <;> nlinarith [hy'.1, hy'.2]

 
theorem supProxy_det_internal (κ : ℝ) (D : DistC → LSCMetric) {R : ℝ} (hR : 0 < R) (w : ℂ)
    (g₁ g₂ : DistC) (hB₁ : BiLipschitz.Barrier.Barrier (D g₁)) (hB₂ : BiLipschitz.Barrier.Barrier (D g₂))
    (hl₁ : (D g₁).IsLengthSpace) (hl₂ : (D g₂).IsLengthSpace)
    (hint : (D g₁).internal (LQGMetric.Blueprint.annulus w R (3 * R) : Set ℂ) =
      (D g₂).internal (LQGMetric.Blueprint.annulus w R (3 * R) : Set ℂ))
    (h₁ : SupProxy κ (D g₁) hR w) : SupProxy κ (D g₂) hR w := by
  have hcross : acrossDist (D g₁) (supInner hR w) = acrossDist (D g₂) (supInner hR w) := by
    rw [BiLipschitz.Barrier.acrossDist_eq_iInf_internal (D g₁) hB₁ hl₁ (supInner hR w)
      (supInner_closed_subset hR w),
      BiLipschitz.Barrier.acrossDist_eq_iInf_internal (D g₂) hB₂ hl₂ (supInner hR w)
        (supInner_closed_subset hR w), hint]
  have haround : aroundDist (D g₁) (supOuter hR w) = aroundDist (D g₂) (supOuter hR w) :=
    BiLipschitz.EqualNormalizer.aroundDist_eq_of_internal_eq _ _ _ hint _ (supOuter_toSet_subset hR w)
  unfold SupProxy at h₁ ⊢
  rwa [← haround, ← hcross]

 
theorem ae_supProxy_addConst_iff (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (κ : ℝ) {R : ℝ} (hR : 0 < R) (w : ℂ)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hh' : LQGMetric.IsWholePlaneGFF h' P') (t : Ω' → ℝ) :
    ∀ᵐ ω ∂P', (addConst (h' ω) (t ω) ∈ {g : DistC | SupProxy κ (D g) hR w} ↔
      h' ω ∈ {g : DistC | SupProxy κ (D g) hR w}) := by
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul P' h' (LQGMetric.GM.detGFFPlusCont hh') ξ Q D hD t]
    with ω hω
  exact supProxy_scale_iff κ (D (h' ω)) (D (addConst (h' ω) (t ω))) _
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top
    (fun u v => hω (u, v)) hR w

 

theorem supProxy_aeEventIn {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (κ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) :
    LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) ρ w))
        (LQGMetric.Blueprint.annulus w ((1 / 4) * ρ) ((3 / 4) * ρ)))
      {ω | SupProxy κ (D (h ω)) (show 0 < ρ / 4 by positivity) w} := by
  have hR : 0 < ρ / 4 := by positivity
  have hU : LQGMetric.Blueprint.annulus w ((1 / 4) * ρ) ((3 / 4) * ρ) =
      LQGMetric.Blueprint.annulus w (ρ / 4) (3 * (ρ / 4)) := by
    congr 1 <;> ring
  rw [hU]
  have key := centered_local_of_internal P h hh ξ Q D hD
    (LQGMetric.Blueprint.annulus w (ρ / 4) (3 * (ρ / 4)))
    {g : DistC | SupProxy κ (D g) hR w} (measurableSet_supProxy hD.measurable κ hR w)
    (fun g₁ g₂ hB₁ hB₂ hl₁ hl₂ hint h₁ =>
      supProxy_det_internal κ D hR w g₁ g₂ hB₁ hB₂ hl₁ hl₂ hint h₁)
    (fun Ω' _ P' _ h' hh' t => ae_supProxy_addConst_iff ξ Q D hD κ hR w Ω' P' h' hh' t) w ρ
  exact key


end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9
