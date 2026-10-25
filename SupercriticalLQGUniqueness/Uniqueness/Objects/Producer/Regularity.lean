import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.Producer
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapChecks.Gapc2
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProducerBlocks.BlockLemmas
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Prob
import SLUMetricAPI




 


















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

open LQGMetric (DistC TestC addConst addFun ofCont)

 

theorem addConst_eq_addFun (u : DistC) (c : ℝ) :
    addConst u c = addFun u (ContinuousMap.const ℂ c) := rfl

theorem ofCont_add (f g : C(ℂ, ℝ)) : ofCont (f + g) = ofCont f + ofCont g := by
  unfold LQGMetric.ofCont
  rw [ContinuousMap.coe_add]
  exact Distribution.ofFun_add (f.continuous.locallyIntegrable.locallyIntegrableOn _)
    (g.continuous.locallyIntegrable.locallyIntegrableOn _)

theorem addFun_addFun (u : DistC) (f g : C(ℂ, ℝ)) :
    addFun (addFun u f) g = addFun u (f + g) := by
  simp only [LQGMetric.addFun, ofCont_add, add_assoc]

theorem addFun_addConst (u : DistC) (c : ℝ) (f : C(ℂ, ℝ)) :
    addFun (addConst u c) f = addFun u (f + ContinuousMap.const ℂ c) := by
  rw [addConst_eq_addFun, addFun_addFun, add_comm]

theorem testTranslate_apply (z : ℂ) (φ : TestC) (x : ℂ) : testTranslate z φ x = φ (x - z) := rfl

theorem integral_testTranslate (z : ℂ) (φ : TestC) : ∫ x, testTranslate z φ x = ∫ x, φ x := by
  simp_rw [testTranslate_apply]
  exact integral_sub_right_eq_self (fun x => φ x) z

 
theorem translateDist_addConst (z : ℂ) (u : DistC) (c : ℝ) :
    translateDist z (addConst u c) = addConst (translateDist z u) c := by
  refine DFunLike.ext _ _ fun φ => ?_
  change addConst u c (testTranslate z φ) = addConst (translateDist z u) c φ
  rw [LQGMetric.GFFInv.addConst_apply, LQGMetric.GFFInv.addConst_apply, integral_testTranslate]
  rfl

 

section scaled

variable {D E : LSCMetric} {k : ℝ}

theorem scale_le (hE : ∀ p : ℂ × ℂ, E p = ENNReal.ofReal k * D p) (x y : ℂ) :
    E (x, y) ≤ ENNReal.ofReal k * D (x, y) := (hE (x, y)).le

theorem scale_le_inv (hk : 0 < k) (hE : ∀ p : ℂ × ℂ, E p = ENNReal.ofReal k * D p) (x y : ℂ) :
    D (x, y) ≤ ENNReal.ofReal k⁻¹ * E (x, y) := by
  rw [hE (x, y), ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hk).le, inv_mul_cancel₀ hk.ne',
    ENNReal.ofReal_one, one_mul]

theorem isCurve_iff_of_scale (hk : 0 < k) (hE : ∀ p : ℂ × ℂ, E p = ENNReal.ofReal k * D p)
    (P : ℝ → ℂ) (a b : ℝ) : E.IsCurve P a b ↔ D.IsCurve P a b :=
  ⟨fun h => Objects.ProducerBlocks.isCurve_of_le E D ENNReal.ofReal_ne_top (scale_le_inv hk hE) h,
    fun h => Objects.ProducerBlocks.isCurve_of_le D E ENNReal.ofReal_ne_top (scale_le hE) h⟩

theorem len_eq_of_scale (hk : 0 < k) (hE : ∀ p : ℂ × ℂ, E p = ENNReal.ofReal k * D p)
    (P : ℝ → ℂ) (a b : ℝ) : E.len P a b = ENNReal.ofReal k * D.len P a b := by
  refine le_antisymm (Objects.ProducerBlocks.len_le_of_le D E ENNReal.ofReal_ne_top (scale_le hE) P a b) ?_
  have h2 := Objects.ProducerBlocks.len_le_of_le E D ENNReal.ofReal_ne_top (scale_le_inv hk hE) P a b
  calc ENNReal.ofReal k * D.len P a b ≤ ENNReal.ofReal k * (ENNReal.ofReal k⁻¹ * E.len P a b) :=
        by gcongr
    _ = E.len P a b := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hk.le, mul_inv_cancel₀ hk.ne', ENNReal.ofReal_one,
          one_mul]

 
theorem isLengthSpace_of_scale (hk : 0 < k) (hE : ∀ p : ℂ × ℂ, E p = ENNReal.ofReal k * D p)
    (hD : D.IsLengthSpace) : E.IsLengthSpace := by
  intro x y hxy ε hε
  have hDxy : D (x, y) < ⊤ := by
    have := scale_le_inv hk hE x y
    exact lt_of_le_of_lt this (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hxy)
  obtain ⟨P, a, b, hP, ha, hb, hlen⟩ := hD x y hDxy (ε / k) (div_pos hε hk)
  refine ⟨P, a, b, (isCurve_iff_of_scale hk hE P a b).2 hP, ha, hb, ?_⟩
  rw [len_eq_of_scale hk hE, hE (x, y)]
  calc ENNReal.ofReal k * D.len P a b ≤ ENNReal.ofReal k * (D (x, y) + ENNReal.ofReal (ε / k)) := by
        gcongr
    _ = ENNReal.ofReal k * D (x, y) + ENNReal.ofReal ε := by
        rw [mul_add, ← ENNReal.ofReal_mul hk.le, mul_div_cancel₀ _ hk.ne']

theorem acrossDist_of_scale (hk : 0 < k) (hE : ∀ p : ℂ × ℂ, E p = ENNReal.ofReal k * D p)
    (A : EuclideanAnnulus) : acrossDist E A = ENNReal.ofReal k * acrossDist D A := by
  have hk0 : ENNReal.ofReal k ≠ 0 := by simpa using hk
  unfold acrossDist
  simp_rw [ENNReal.mul_iInf_of_ne hk0 ENNReal.ofReal_ne_top, hE]

 
theorem barrier_of_scale (hk : 0 < k) (hE : ∀ p : ℂ × ℂ, E p = ENNReal.ofReal k * D p)
    (hB : BiLipschitz.Barrier.Barrier D) : BiLipschitz.Barrier.Barrier E := by
  intro n₀ M
  obtain ⟨M', hM'⟩ := exists_nat_ge ((M : ℝ) / k)
  obtain ⟨n, hn, hlt⟩ := hB n₀ M'
  refine ⟨n, hn, ?_⟩
  rw [acrossDist_of_scale hk hE]
  have hkM : (M : ℝ≥0∞) ≤ ENNReal.ofReal k * (M' : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast M', ← ENNReal.ofReal_mul hk.le, ← ENNReal.ofReal_natCast M]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (div_le_iff₀ hk).1 hM'
    linarith
  have hk0 : ENNReal.ofReal k ≠ 0 := by simpa using hk
  have h3 := ENNReal.mul_lt_mul_left hk0 ENNReal.ofReal_ne_top hlt
  rw [mul_comm _ (ENNReal.ofReal k), mul_comm (acrossDist D _) (ENNReal.ofReal k)] at h3
  exact hkM.trans_lt h3

end scaled

 
theorem weylScale_add_const (ξ c : ℝ) (f : C(ℂ, ℝ)) (D : LSCMetric) (p : ℂ × ℂ) :
    weylScale ξ (f + ContinuousMap.const ℂ c) D p =
      ENNReal.ofReal (Real.exp (ξ * c)) * weylScale ξ f D p := by
  have hk0 : ENNReal.ofReal (Real.exp (ξ * c)) ≠ 0 := by simpa using Real.exp_pos (ξ * c)
  unfold weylScale
  simp_rw [ENNReal.mul_iInf_of_ne hk0 ENNReal.ofReal_ne_top]
  refine iInf_congr fun P => iInf_congr fun L => iInf_congr fun _ => iInf_congr fun _ =>
    iInf_congr fun _ => iInf_congr fun _ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
  ring

 

 
def WeylReg (ξ : ℝ) (D : DistC → LSCMetric) (u : DistC) : Prop :=
  (D u).IsLengthSpace ∧ ∀ f : C(ℂ, ℝ), weylScale ξ f (D u) = (D (addFun u f)).1

 
theorem WeylReg.scale {ξ : ℝ} {D : DistC → LSCMetric} {u : DistC} (h : WeylReg ξ D u) (c : ℝ)
    (p : ℂ × ℂ) : D (addConst u c) p = ENNReal.ofReal (Real.exp (ξ * c)) * D u p := by
  have h1 := congrFun (h.2 (ContinuousMap.const ℂ c)) p
  rw [← addConst_eq_addFun] at h1
  change (D (addConst u c)).1 p = _
  rw [← h1]
  exact weylScale_const ξ c (D u) h.1 p

 
theorem WeylReg.addConst {ξ : ℝ} {D : DistC → LSCMetric} {u : DistC} (h : WeylReg ξ D u)
    (c : ℝ) : WeylReg ξ D (addConst u c) := by
  have hk : 0 < Real.exp (ξ * c) := Real.exp_pos _
  have hsc := h.scale c
  refine ⟨isLengthSpace_of_scale hk hsc h.1, fun f => ?_⟩
  funext p
  rw [TwoScale.GapChecks.weylScale_eq_mul_of_pointwise ξ f (Real.exp (ξ * c)) hk hsc p, addFun_addConst,
    ← h.2 (f + ContinuousMap.const ℂ c), weylScale_add_const]

 
def MetricReg (ξ : ℝ) (D : DistC → LSCMetric) (u : DistC) : Prop :=
  WeylReg ξ D u ∧ BiLipschitz.Barrier.Barrier (D u)

theorem MetricReg.addConst {ξ : ℝ} {D : DistC → LSCMetric} {u : DistC} (h : MetricReg ξ D u)
    (c : ℝ) : MetricReg ξ D (addConst u c) :=
  ⟨h.1.addConst c, barrier_of_scale (Real.exp_pos _) (h.1.scale c) h.2⟩

 
def TransReg (D : DistC → LSCMetric) (w : ℂ) (u : DistC) : Prop :=
  ∀ a b : ℂ, D (translateDist w u) (a, b) = D u (a + w, b + w)

 
theorem TransReg.addConst {ξ : ℝ} {D : DistC → LSCMetric} {w : ℂ} {u : DistC}
    (h : TransReg D w u) (hu : WeylReg ξ D u) (hw : WeylReg ξ D (translateDist w u)) (c : ℝ) :
    TransReg D w (addConst u c) := by
  intro a b
  rw [translateDist_addConst, hw.scale c, hu.scale c, h a b]

 
def CircReg (u : DistC) (s : Set.Ioi (0 : ℝ)) (w : ℂ) : Prop := ∃ a, IsCircleAverage u s w a

theorem CircReg.addConst {u : DistC} {s : Set.Ioi (0 : ℝ)} {w : ℂ} (h : CircReg u s w) (c : ℝ) :
    CircReg (addConst u c) s w := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a + c, isCircleAverage_addConst ha c⟩

 

section ae

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

omit [IsProbabilityMeasure P] in
theorem isWholePlaneGFF_id_aux (hh : IsNormalizedWholePlaneGFF h P) :
    LQGMetric.IsWholePlaneGFF (id : DistC → DistC) (P.map h) :=
  LQGMetric.GM.isWholePlaneGFF_id_map hh.1

omit [IsProbabilityMeasure P] in
theorem isWholePlaneGFF_id (hh : IsNormalizedWholePlaneGFF h P) :
    LQGMetric.IsWholePlaneGFF (id : DistC → DistC) (P.map h) :=
  isWholePlaneGFF_id_aux hh

omit [IsProbabilityMeasure P] in
 
theorem isNormalized_id (hh : IsNormalizedWholePlaneGFF h P) :
    IsNormalizedWholePlaneGFF (id : DistC → DistC) (P.map h) :=
  ⟨isWholePlaneGFF_id hh, (ae_map_iff hh.1.measurable.aemeasurable
    (measurableSet_isCircleAverage oneR 0 0)).2 hh.2⟩

theorem translateDist_eq_affineComp_one (z : ℂ) (g : DistC) :
    translateDist z g = LQGMetric.affineComp 1 z g := by
  refine DFunLike.ext _ _ fun φ => ?_
  have ht : testTranslate z φ = LQGMetric.testAffinePull 1 z φ := by
    ext x
    rw [LQGMetric.testAffinePull_apply 1 z one_ne_zero]
    simp only [Complex.ofReal_one, div_one]
    rfl
  change g (testTranslate z φ) = LQGMetric.affineComp 1 z g φ
  rw [LQGMetric.GFFInv.affineComp_apply, ht]
  norm_num

omit [IsProbabilityMeasure P] in
theorem isWholePlaneGFF_translate (hh : IsNormalizedWholePlaneGFF h P) (w : ℂ) :
    LQGMetric.IsWholePlaneGFF (fun u : DistC => translateDist w u) (P.map h) := by
  simpa only [translateDist_eq_affineComp_one, id] using
    (isWholePlaneGFF_id hh).affineComp one_pos w

theorem ae_weylReg_of_gff {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D) {μ : Measure DistC} [IsProbabilityMeasure μ]
    {g : DistC → DistC} (hg : LQGMetric.IsWholePlaneGFF g μ) :
    ∀ᵐ u ∂μ, WeylReg (ξ : ℝ) D (g u) := by
  have hplus : LQGMetric.IsGFFPlusCont g μ := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hg
  filter_upwards [hD.2.1 μ g hplus, hD.2.2.2.1 μ g hplus] with u h1 h2
  exact ⟨h1, h2⟩

 
theorem ae_weylReg {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ u ∂(P.map h), WeylReg (ξ : ℝ) D u := by
  exact ae_weylReg_of_gff hD (isWholePlaneGFF_id hh)

 
theorem ae_weylReg_translate {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D) (hh : IsNormalizedWholePlaneGFF h P) (w : ℂ) :
    ∀ᵐ u ∂(P.map h), WeylReg (ξ : ℝ) D (translateDist w u) := by
  exact ae_weylReg_of_gff hD (isWholePlaneGFF_translate hh w)

 
theorem ae_metricReg {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D) (hQ : 0 < Q) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ u ∂(P.map h), MetricReg (ξ : ℝ) D u := by
  filter_upwards [ae_weylReg hD hh, BiLipschitz.Barrier.ae_barrier hD hQ (P.map h) id (isNormalized_id hh)]
    with u h1 h2
  exact ⟨h1, h2⟩

 
theorem ae_transReg {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D) (hh : IsNormalizedWholePlaneGFF h P) (w : ℂ) :
    ∀ᵐ u ∂(P.map h), TransReg D w u := by
  have hplus : LQGMetric.IsGFFPlusCont (id : DistC → DistC) (P.map h) :=
    LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF (isWholePlaneGFF_id hh)
  filter_upwards [hD.2.2.2.2.1 (P.map h) id hplus w] with u hu
  exact hu

omit [IsProbabilityMeasure P] in
 
theorem ae_circReg (hh : IsNormalizedWholePlaneGFF h P) (s : Set.Ioi (0 : ℝ)) (w : ℂ) :
    ∀ᵐ u ∂(P.map h), CircReg u s w := by
  filter_upwards [LQGMetric.CircleAvg.ae_tendsto_mollAvg (isWholePlaneGFF_id hh) w s.2] with u hu
  exact hu

end ae

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
