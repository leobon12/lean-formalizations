import BR1Bridges
import SLUMetricAPI
import SLUFieldSupport
import LQGMetric.Field.CircleAvgAffine
import LQGMetric.Field.CircleAvgLaw
import LQGMetric.Papers.GM.S2.TightLaw
import LQGMetric.Papers.DFGPS.L2_19
import LQGMetric.Papers.GM.S2.SpatialIndepShift
import LQGMetric.Papers.GM.S3.DeterministicScale
import LQGMetric.Papers.LM.L3_4M6




 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness

open LQGMetric (DistC IsWholePlaneGFF IsGFFPlusCont addConst affineComp circleAvg)

private theorem testTranslate_eq_testAffinePull_one (z : ℂ) (φ : LQGMetric.TestC) :
    testTranslate z φ = LQGMetric.testAffinePull 1 z φ := by
  ext x
  rw [LQGMetric.testAffinePull_apply 1 z one_ne_zero]
  simp only [Complex.ofReal_one, div_one]
  rfl

 
theorem translateDist_eq_affineComp_one (z : ℂ) (g : DistC) :
    translateDist z g = affineComp 1 z g := by
  ext φ
  rw [LQGMetric.GFFInv.affineComp_apply, one_pow, inv_one, one_mul]
  exact congrArg g (testTranslate_eq_testAffinePull_one z φ)

 
theorem map_eq_of_candidate_normalized {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsNormalizedWholePlaneGFF h P)
    (hh' : IsNormalizedWholePlaneGFF h' P') :
    P.map h = P'.map h' :=
  LQGMetric.CircleAvg.map_eq_of_isNormalizedWPGFF
    (isNormalizedWholePlaneGFF_iff_old.mp hh)
    (isNormalizedWholePlaneGFF_iff_old.mp hh')

 
theorem map_affine_normalized_of_candidate {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    P.map (fun ω => addConst (affineComp r z (h ω))
      (-circleAvg (affineComp r z (h ω)) 1 0)) = P.map h :=
  LQGMetric.CircleAvg.map_affine_normalized
    (isNormalizedWholePlaneGFF_iff_old.mp hh) hr z

 
theorem normalized_translate_sub_circleAvg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) :
    IsNormalizedWholePlaneGFF
      (fun ω => addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) P := by
  have hold := isNormalizedWholePlaneGFF_iff_old.mp hh
  have htrans : IsWholePlaneGFF (fun ω => translateDist z (h ω)) P := by
    simpa only [translateDist_eq_affineComp_one] using hh.1.affineComp one_pos z
  have hc : Measurable (fun ω => -circleAvg (h ω) 1 z) :=
    ((LQGMetric.measurable_circleAvg_left 1 z).comp hh.1.measurable).neg
  have hwhole := htrans.addConst hc
  apply isNormalizedWholePlaneGFF_iff_old.mpr
  refine ⟨hwhole, ?_⟩
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst htrans 0 one_pos]
    with ω hca
  rw [hca, translateDist_eq_affineComp_one,
    LQGMetric.GM.Tight.circleAvg_affineComp_one]
  ring

 
theorem normalized_translate_old {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) :
    LQGMetric.IsNormalizedWPGFF
      (fun ω => addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) P :=
  isNormalizedWholePlaneGFF_iff_old.mp (normalized_translate_sub_circleAvg hh z)

 
theorem map_normalized_translate_sub_circleAvg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) :
    P.map (fun ω => addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) =
      P.map h := by
  have hold := isNormalizedWholePlaneGFF_iff_old.mp hh
  simp only [translateDist_eq_affineComp_one]
  exact LQGMetric.CircleAvg.map_affine_sub_circleAvg hold one_pos z

 
theorem ae_circleAvg_normalized_translate {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) (r : Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P,
      circleAvg (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) r 0 =
        circleAvg (h ω) r z - circleAvg (h ω) 1 z := by
  have htrans : IsWholePlaneGFF (fun ω => translateDist z (h ω)) P := by
    simpa only [translateDist_eq_affineComp_one] using hh.1.affineComp one_pos z
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst htrans 0 r.2]
    with ω hω
  rw [hω, translateDist_eq_affineComp_one,
    LQGMetric.GM.Tight.circleAvg_affineComp_one]
  ring

 
theorem ae_isCircleAverage_normalized_translate {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) (r : Ioi (0 : ℝ))
    (a b c : Ω → ℝ)
    (ha : ∀ᵐ ω ∂P, IsCircleAverage
      (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) r 0 (a ω))
    (hb : ∀ᵐ ω ∂P, IsCircleAverage (h ω) r z (b ω))
    (hc : ∀ᵐ ω ∂P, IsCircleAverage (h ω) ⟨1, Set.mem_Ioi.mpr one_pos⟩ z (c ω)) :
    a =ᵐ[P] (fun ω => b ω - c ω) := by
  filter_upwards [ha, hb, hc, ae_circleAvg_normalized_translate hh z r]
    with ω haω hbω hcω heq
  have ha' : circleAvg
      (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) r 0 = a ω :=
    haω.limUnder_eq
  have hb' : circleAvg (h ω) r z = b ω := hbω.limUnder_eq
  have hc' : circleAvg (h ω) 1 z = c ω := hcω.limUnder_eq
  calc
    a ω = circleAvg
        (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) r 0 := ha'.symm
    _ = circleAvg (h ω) r z - circleAvg (h ω) 1 z := heq
    _ = b ω - c ω := by rw [hb', hc']

 
theorem normalized_translate_isGFFPlusCont {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) :
    IsGFFPlusCont
      (fun ω => addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) P :=
  LQGMetric.GM.Tight.isGFFPlusCont_of_wp (normalized_translate_sub_circleAvg hh z).1

 
theorem center_at_circleAvg_isGFFPlusCont {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) (r : Ioi (0 : ℝ)) :
    IsGFFPlusCont (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) P := by
  have hc : Measurable (fun ω => -circleAvg (h ω) r z) :=
    ((LQGMetric.measurable_circleAvg_left r z).comp hh.1.measurable).neg
  exact LQGMetric.GM.Tight.isGFFPlusCont_of_wp (hh.1.addConst hc)

 
theorem isTwoSidedTight_of_field_law_eq {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h h' : Ω → DistC}
    (hm : Measurable h) (hm' : Measurable h') (hlaw : P.map h' = P.map h)
    (F : ι → DistC → ℝ≥0∞) (hF : ∀ i, Measurable (F i))
    (htight : IsTwoSidedTight P (fun i ω => F i (h ω))) :
    IsTwoSidedTight P (fun i ω => F i (h' ω)) := by
  constructor
  · intro i
    exact ((hF i).comp hm').aemeasurable
  · intro ε hε
    obtain ⟨M, hM, htails⟩ := htight.2 ε hε
    refine ⟨M, hM, ?_⟩
    intro i
    have hevent (S : Set DistC) (hS : MeasurableSet S) :
        P (h' ⁻¹' S) = P (h ⁻¹' S) := by
      calc
        P (h' ⁻¹' S) = (P.map h') S := (Measure.map_apply hm' hS).symm
        _ = (P.map h) S := by rw [hlaw]
        _ = P (h ⁻¹' S) := Measure.map_apply hm hS
    have hU : MeasurableSet {g : DistC | ENNReal.ofReal M < F i g} :=
      measurableSet_lt measurable_const (hF i)
    have hL : MeasurableSet {g : DistC | F i g < ENNReal.ofReal M⁻¹} :=
      measurableSet_lt (hF i) measurable_const
    constructor
    · change P (h' ⁻¹' {g : DistC | ENNReal.ofReal M < F i g}) ≤ _
      rw [hevent _ hU]
      exact (htails i).1
    · change P (h' ⁻¹' {g : DistC | F i g < ENNReal.ofReal M⁻¹}) ≤ _
      rw [hevent _ hL]
      exact (htails i).2

 
theorem measurable_normalized_across (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : Measurable D) (A : EuclideanAnnulus)
    (r : Ioi (0 : ℝ)) :
    Measurable (fun g : DistC =>
      ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * circleAvg g r 0))) *
      acrossDist (D g) (A.dilate r r.2)) := by
  have hca : Measurable fun g : DistC => circleAvg g r 0 :=
    LQGMetric.measurable_circleAvg_left r 0
  have hac : Measurable fun g : DistC => acrossDist (D g) (A.dilate r r.2) :=
    (measurable_acrossDist _).comp hD
  exact ((measurable_const.mul
    ((Real.measurable_exp.comp (measurable_const.mul hca).neg))).ennreal_ofReal).mul hac

 
theorem uniform_center_normalized_across_lower_tail {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (A : EuclideanAnnulus) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
      P {ω | ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * circleAvg
          (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) r 0))) *
        acrossDist (D (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)))
          (A.dilate r r.2) < ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal ε := by
  let F : Ioi (0 : ℝ) → DistC → ℝ≥0∞ := fun r g =>
    ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg g r 0))) *
      acrossDist (D g) (A.dilate r r.2)
  have hV : IsTwoSidedTight P (fun r ω => F r (h ω)) := by
    exact (hD.tightness P h hh
      (fun r ω => circleAvg (h ω) r 0)
      (fun r => ae_isCircleAverage_old hh.1 r 0) A).1
  intro ε hε
  obtain ⟨M, hM, hbound⟩ := hV.2 ε hε
  refine ⟨M, hM, ?_⟩
  intro z r
  let hz : Ω → DistC := fun ω =>
    addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)
  have hhz := normalized_translate_sub_circleAvg hh z
  have hlaw : P.map hz = P.map h := map_normalized_translate_sub_circleAvg hh z
  have hS : MeasurableSet {g : DistC | F r g < ENNReal.ofReal M⁻¹} :=
    measurableSet_lt (measurable_normalized_across ξ Q D hD.measurable A r)
      measurable_const
  have heq : P (hz ⁻¹' {g : DistC | F r g < ENNReal.ofReal M⁻¹}) =
      P (h ⁻¹' {g : DistC | F r g < ENNReal.ofReal M⁻¹}) := by
    calc
      P (hz ⁻¹' {g : DistC | F r g < ENNReal.ofReal M⁻¹}) =
          (P.map hz) {g : DistC | F r g < ENNReal.ofReal M⁻¹} :=
        (Measure.map_apply hhz.1.measurable hS).symm
      _ = (P.map h) {g : DistC | F r g < ENNReal.ofReal M⁻¹} := by rw [hlaw]
      _ = P (h ⁻¹' {g : DistC | F r g < ENNReal.ofReal M⁻¹}) :=
        Measure.map_apply hh.1.measurable hS
  change P (hz ⁻¹' {g : DistC | F r g < ENNReal.ofReal M⁻¹}) ≤ _
  rw [heq]
  exact (hbound r).2

 
theorem ae_centered_translate_eq_affine {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) (r : Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P,
      affineComp 1 z (addConst (h ω) (-circleAvg (h ω) r z)) =
        addConst
          (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z))
          (-circleAvg
            (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) r 0) := by
  have htrans := hh.1.affineComp one_pos z
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst htrans 0 r.2]
    with ω hca
  rw [translateDist_eq_affineComp_one, hca,
    LQGMetric.GM.affineComp_addConst one_pos,
    LQGMetric.GM.addConst_addConst,
    LQGMetric.GM.Tight.circleAvg_affineComp_one]
  congr 1
  ring

 

theorem aeEventIn_centered_translate {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) (r : Ioi (0 : ℝ))
    (U V : TopologicalSpace.Opens ℂ)
    (hUV : ∀ y : ℂ, y ∈ V ↔ (1 : ℝ) • y + z ∈ U)
    {E : Set Ω}
    (hE : LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) U) E) :
    LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => addConst
          (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z))
          (-circleAvg
            (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) r 0)) V) E := by
  obtain ⟨F, hFm, hFa⟩ := hE
  have hF : LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => affineComp 1 z
          (addConst (h ω) (-circleAvg (h ω) r z))) V) E :=
    ⟨F, LQGMetric.GM.fieldSigma_le_affineComp one_pos hUV
      (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) F hFm, hFa⟩
  exact LQGMetric.GM.aeEventIn_of_ae_eq
    (ae_centered_translate_eq_affine hh z r) V hF

 
theorem ae_countOcc_eq_of_event_versions {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} (E F : ℕ → Set Ω)
    (hEF : ∀ j, E j =ᵐ[P] F j) :
    ∀ᵐ ω ∂P, ∀ K : ℕ,
      LQGMetric.Blueprint.countOcc E K ω = LQGMetric.Blueprint.countOcc F K ω := by
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, (ω ∈ E j) = (ω ∈ F j) := ae_all_iff.mpr hEF
  filter_upwards [hall] with ω hω K
  unfold LQGMetric.Blueprint.countOcc
  congr 1
  ext j
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ => Iff.of_eq (hω j))

end SupercriticalLQGUniqueness

