import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.FieldTranslations
import LQGMetric.Field.GFFLaw
import LQGMetric.Papers.GM.S1.FieldAux




 



set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses

open LQGMetric (DistC addConst circleAvg)
open SupercriticalLQGUniqueness

def annulusTranslate (A : EuclideanAnnulus) (z : ℂ) : EuclideanAnnulus :=
  ⟨(A.center + z, A.innerRadius, A.outerRadius), A.2⟩

theorem mem_innerBoundary_translate (A : EuclideanAnnulus) (z x : ℂ) :
    x ∈ A.innerBoundary ↔ x + z ∈ (annulusTranslate A z).innerBoundary := by
  simp only [EuclideanAnnulus.innerBoundary, EuclideanAnnulus.center,
    EuclideanAnnulus.innerRadius, annulusTranslate, Metric.mem_sphere]
  rw [dist_add_right]

theorem mem_outerBoundary_translate (A : EuclideanAnnulus) (z x : ℂ) :
    x ∈ A.outerBoundary ↔ x + z ∈ (annulusTranslate A z).outerBoundary := by
  simp only [EuclideanAnnulus.outerBoundary, EuclideanAnnulus.center,
    EuclideanAnnulus.outerRadius, annulusTranslate, Metric.mem_sphere]
  rw [dist_add_right]

 
theorem acrossDist_translate (D E : LSCMetric) (A : EuclideanAnnulus) (z : ℂ)
    (hD : ∀ x y : ℂ, E (x, y) = D (x + z, y + z)) :
    acrossDist E A = acrossDist D (annulusTranslate A z) := by
  apply le_antisymm
  · refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
    let x' := x - z
    let y' := y - z
    have hx' : x' ∈ A.innerBoundary := by
      apply (mem_innerBoundary_translate A z x').2
      simpa only [x', sub_add_cancel] using hx
    have hy' : y' ∈ A.outerBoundary := by
      apply (mem_outerBoundary_translate A z y').2
      simpa only [y', sub_add_cancel] using hy
    calc
      acrossDist E A ≤ E (x', y') := iInf_le_of_le x' <| iInf_le_of_le hx' <|
        iInf_le_of_le y' <| iInf_le _ hy'
      _ = D (x, y) := by rw [hD]; simp only [x', y', sub_add_cancel]
  · refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
    have hx' := (mem_innerBoundary_translate A z x).1 hx
    have hy' := (mem_outerBoundary_translate A z y).1 hy
    calc
      acrossDist D (annulusTranslate A z) ≤ D (x + z, y + z) :=
        iInf_le_of_le (x + z) <| iInf_le_of_le hx' <|
          iInf_le_of_le (y + z) <| iInf_le _ hy'
      _ = E (x, y) := (hD x y).symm

 
theorem ae_normalized_across_translate {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (A : EuclideanAnnulus)
    (z : ℂ) (r : Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P,
      ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * circleAvg
          (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) r 0))) *
        acrossDist (D (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)))
          (A.dilate r r.2) =
      ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * circleAvg (h ω) r z))) *
        acrossDist (D (h ω)) (annulusTranslate (A.dilate r r.2) z) := by
  let hz : Ω → DistC := fun ω =>
    addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)
  have hhz : LQGMetric.IsGFFPlusCont hz P :=
    normalized_translate_isGFFPlusCont hh z
  have hwhole : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hh.1
  filter_upwards [ae_circleAvg_normalized_translate hh z r,
    ae_annulus_addConst_eq_mul P hz hhz ξ Q D hD
      (fun ω => circleAvg (h ω) 1 z),
    hD.translation P h hwhole z] with ω hca hw ht
  have hcancel : addConst (hz ω) (circleAvg (h ω) 1 z) =
      translateDist z (h ω) := by
    simp only [hz, LQGMetric.GFFLaw.addConst_addConst, neg_add_cancel,
      LQGMetric.GFFLaw.addConst_zero']
  have hmetric : acrossDist (D (h ω)) (annulusTranslate (A.dilate r r.2) z) =
      ENNReal.ofReal (Real.exp ((ξ : ℝ) * circleAvg (h ω) 1 z)) *
        acrossDist (D (hz ω)) (A.dilate r r.2) := by
    calc
      acrossDist (D (h ω)) (annulusTranslate (A.dilate r r.2) z) =
          acrossDist (D (translateDist z (h ω))) (A.dilate r r.2) := by
        symm
        exact acrossDist_translate (D (h ω)) (D (translateDist z (h ω)))
          (A.dilate r r.2) z (fun x y => ht x y)
      _ = ENNReal.ofReal (Real.exp ((ξ : ℝ) * circleAvg (h ω) 1 z)) *
          acrossDist (D (hz ω)) (A.dilate r r.2) := by
        rw [← hcancel]
        exact (hw (A.dilate r r.2)).1
  rw [hmetric, hca]
  change ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * (circleAvg (h ω) r z - circleAvg (h ω) 1 z)))) *
      acrossDist (D (hz ω)) (A.dilate r r.2) =
    ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg (h ω) r z))) *
      (ENNReal.ofReal (Real.exp ((ξ : ℝ) * circleAvg (h ω) 1 z)) *
        acrossDist (D (hz ω)) (A.dilate r r.2))
  have hpos : 0 ≤ (r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg (h ω) r z)) :=
    mul_nonneg (le_of_lt (Real.rpow_pos_of_pos r.2 _)) (le_of_lt (Real.exp_pos _))
  rw [← mul_assoc, ← ENNReal.ofReal_mul hpos]
  congr 1
  rw [show -((ξ : ℝ) * (circleAvg (h ω) r z - circleAvg (h ω) 1 z)) =
      -((ξ : ℝ) * circleAvg (h ω) r z) +
        (ξ : ℝ) * circleAvg (h ω) 1 z by ring, Real.exp_add]
  ring

 
theorem uniform_normalized_across_lower_tail {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (A : EuclideanAnnulus)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
      ENNReal.ofReal p ≤ P {ω |
        ENNReal.ofReal c ≤
          ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
            Real.exp (-((ξ : ℝ) * circleAvg (h ω) r z))) *
            acrossDist (D (h ω)) (annulusTranslate (A.dilate r r.2) z)} := by
  obtain ⟨M, hM, htail⟩ :=
    uniform_center_normalized_across_lower_tail hh ξ Q D hD A
      (1 - p) (by linarith)
  refine ⟨M⁻¹, inv_pos.mpr hM, ?_⟩
  intro z r
  let X : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg (h ω) r z))) *
      acrossDist (D (h ω)) (annulusTranslate (A.dilate r r.2) z)
  let Y : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg
        (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) r 0))) *
      acrossDist (D (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)))
        (A.dilate r r.2)
  have hXY : Y =ᵐ[P] X := ae_normalized_across_translate P h hh ξ Q D hD A z r
  have hbad : P {ω | X ω < ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal (1 - p) := by
    calc
      P {ω | X ω < ENNReal.ofReal M⁻¹} =
          P {ω | Y ω < ENNReal.ofReal M⁻¹} := by
        apply measure_congr
        filter_upwards [hXY] with ω hω
        simp only [hω]
      _ ≤ _ := htail z r
  have hX : Measurable X := by
    have hca : Measurable fun ω => circleAvg (h ω) r z :=
      (LQGMetric.measurable_circleAvg_left r z).comp hh.1.measurable
    have hac : Measurable fun ω =>
        acrossDist (D (h ω)) (annulusTranslate (A.dilate r r.2) z) :=
      (measurable_acrossDist _).comp (hD.measurable.comp hh.1.measurable)
    exact ((measurable_const.mul
      ((Real.measurable_exp.comp (measurable_const.mul hca).neg))).ennreal_ofReal).mul hac
  have hset : MeasurableSet {ω | X ω < ENNReal.ofReal M⁻¹} :=
    measurableSet_lt hX measurable_const
  have hpE : ENNReal.ofReal p ≤ (1 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp1.le
  have hid : (1 : ℝ≥0∞) - ENNReal.ofReal (1 - p) = ENNReal.ofReal p := by
    rw [ENNReal.ofReal_sub 1 hp0.le, ENNReal.ofReal_one]
    exact ENNReal.sub_sub_cancel (by norm_num) hpE
  have hcomp : P {ω | ENNReal.ofReal M⁻¹ ≤ X ω} =
      (1 : ℝ≥0∞) - P {ω | X ω < ENNReal.ofReal M⁻¹} := by
    simpa only [Set.compl_ofPred, not_lt] using (prob_compl_eq_one_sub hset)
  change ENNReal.ofReal p ≤ P {ω | ENNReal.ofReal M⁻¹ ≤ X ω}
  rw [hcomp, ← hid]
  exact tsub_le_tsub_left hbad 1

theorem raw_lower_of_normalized (a b c : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a * b = 1) (d : ℝ≥0∞)
    (h : ENNReal.ofReal c ≤ ENNReal.ofReal a * d) :
    ENNReal.ofReal (c * b) ≤ d := by
  have hmul : ENNReal.ofReal b * ENNReal.ofReal c ≤
      ENNReal.ofReal b * (ENNReal.ofReal a * d) := by
    gcongr
  have hprod : ENNReal.ofReal b * ENNReal.ofReal a = 1 := by
    rw [mul_comm, ← ENNReal.ofReal_mul ha, hab, ENNReal.ofReal_one]
  calc
    ENNReal.ofReal (c * b) = ENNReal.ofReal b * ENNReal.ofReal c := by
      rw [mul_comm c b, ENNReal.ofReal_mul hb]
    _ ≤ ENNReal.ofReal b * (ENNReal.ofReal a * d) := hmul
    _ = d := by rw [← mul_assoc, hprod, one_mul]

 
theorem uniform_offcenter_across_lower_tail {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (A : EuclideanAnnulus)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
      ENNReal.ofReal p ≤ P {ω |
        ENNReal.ofReal (c * (r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg (h ω) r z)) ≤
          acrossDist (D (h ω)) (annulusTranslate (A.dilate r r.2) z)} := by
  obtain ⟨c, hc, htail⟩ :=
    uniform_normalized_across_lower_tail P h hh ξ Q D hD A p hp0 hp1
  refine ⟨c, hc, ?_⟩
  intro z r
  apply le_trans (htail z r)
  apply measure_mono
  intro ω hω
  let v : ℝ := (ξ : ℝ) * circleAvg (h ω) r z
  let u : ℝ := (ξ : ℝ) * Q
  let a : ℝ := (r : ℝ) ^ (-u) * Real.exp (-v)
  let b : ℝ := (r : ℝ) ^ u * Real.exp v
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos r.2 _)) (le_of_lt (Real.exp_pos _))
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos r.2 _)) (le_of_lt (Real.exp_pos _))
  have hab : a * b = 1 := by
    dsimp [a, b]
    rw [Real.rpow_neg r.2.le, Real.exp_neg]
    have hr : (r : ℝ) ^ u ≠ 0 := (Real.rpow_pos_of_pos r.2 u).ne'
    have he : Real.exp v ≠ 0 := (Real.exp_pos v).ne'
    field_simp
  have hraw := raw_lower_of_normalized a b c ha hb hab
    (acrossDist (D (h ω)) (annulusTranslate (A.dilate r r.2) z)) hω
  change ENNReal.ofReal (c * (r : ℝ) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * circleAvg (h ω) r z)) ≤
    acrossDist (D (h ω)) (annulusTranslate (A.dilate r r.2) z)
  simpa only [a, b, u, v, mul_assoc] using hraw

 
def crossingAnnulus : EuclideanAnnulus :=
  ⟨(0, 11 / 20, 4 / 5), by constructor <;> norm_num⟩

theorem ax9_offcenter_tail {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
      ENNReal.ofReal p ≤ P {ω |
        ENNReal.ofReal (c * (r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg (h ω) r z)) ≤
          acrossDist (D (h ω))
            (annulusTranslate (crossingAnnulus.dilate r r.2) z)} :=
  uniform_offcenter_across_lower_tail P h hh ξ Q D hD crossingAnnulus p hp0 hp1

 
theorem exists_canonical_normalized_law :
    ∃ μ : Measure DistC, IsProbabilityMeasure μ ∧
      IsNormalizedWholePlaneGFF (id : DistC → DistC) μ := by
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := exists_normalizedGFF
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  let μ : Measure DistC := P.map h
  haveI : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hh.1.measurable.aemeasurable).2 inferInstance
  have hold := isNormalizedWholePlaneGFF_iff_old.mp hh
  have hμold : LQGMetric.IsNormalizedWPGFF (id : DistC → DistC) μ := by
    refine ⟨LQGMetric.GM.isWholePlaneGFF_id_map hh.1, ?_⟩
    have hS : MeasurableSet {g : DistC | circleAvg g 1 0 = 0} :=
      measurableSet_eq_fun (LQGMetric.measurable_circleAvg_left 1 0) measurable_const
    exact (ae_map_iff hh.1.measurable.aemeasurable hS).2 hold.2
  exact ⟨μ, inferInstance, isNormalizedWholePlaneGFF_iff_old.mpr hμold⟩

theorem ax9_canonical_tail (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
      ENNReal.ofReal p ≤ μ {u |
        ENNReal.ofReal (c * (r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg u r z)) ≤
          acrossDist (D u)
            (annulusTranslate (crossingAnnulus.dilate r r.2) z)} :=
  ax9_offcenter_tail μ id hμ ξ Q D hD p hp0 hp1


end SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses
