import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.OneScale
import LQGMetric.Metric.WeylScaling




 


set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale

open SupercriticalLQGUniqueness

private theorem disconnects_image (e : ℂ ≃ₜ ℂ) {K E F : Set ℂ}
    (h : Disconnects K E F) :
    Disconnects (e '' K) (e '' E) (e '' F) := by
  intro hex
  obtain ⟨S, hS, hSK, ⟨u, huS, huE⟩, ⟨v, hvS, hvF⟩⟩ := hex
  let T : Set ℂ := e.symm '' S
  have hTpre : IsPreconnected T := hS.image e.symm e.symm.continuous.continuousOn
  have hTsub : T ⊆ Kᶜ := by
    rintro x ⟨y, hyS, rfl⟩ hxK
    exact hSK hyS ⟨e.symm y, hxK, e.apply_symm_apply y⟩
  obtain ⟨u₀, hu₀E, rfl⟩ := huE
  obtain ⟨v₀, hv₀F, rfl⟩ := hvF
  have hTE : (T ∩ E).Nonempty := ⟨u₀,
    ⟨e u₀, huS, e.symm_apply_apply u₀⟩, hu₀E⟩
  have hTF : (T ∩ F).Nonempty := ⟨v₀,
    ⟨e v₀, hvS, e.symm_apply_apply v₀⟩, hv₀F⟩
  exact h ⟨T, hTpre, hTsub, hTE, hTF⟩

private theorem disconnects_image_iff (e : ℂ ≃ₜ ℂ) {K E F : Set ℂ} :
    Disconnects (e '' K) (e '' E) (e '' F) ↔ Disconnects K E F := by
  constructor
  · intro h
    have h' := disconnects_image e.symm h
    simpa [Set.image_image] using h'
  · exact disconnects_image e

private theorem len_translate (D E : LSCMetric) (z : ℂ)
    (hDE : ∀ x y : ℂ, E (x, y) = D (x + z, y + z))
    (P : ℝ → ℂ) (a b : ℝ) :
    E.len P a b = D.len (fun t => P t + z) a b := by
  unfold LSCMetric.len
  have h := LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
    (F := E.pt ∘ P) (G := D.pt ∘ fun t => P t + z) (c := (1 : ℝ≥0∞))
    (fun s t => by change E (P s, P t) = 1 * D (P s + z, P t + z)
                   simp only [one_mul, hDE]) (Icc a b)
  simpa only [one_mul] using h

private theorem isCurve_translate (D E : LSCMetric) (z : ℂ)
    (hDE : ∀ x y : ℂ, E (x, y) = D (x + z, y + z))
    (P : ℝ → ℂ) (a b : ℝ) :
    E.IsCurve P a b ↔ D.IsCurve (fun t => P t + z) a b := by
  constructor
  · rintro ⟨hab, hP⟩
    refine ⟨hab, ?_⟩
    intro t ht
    have hlim := tendsto_iff_edist_tendsto_0.mp (hP t ht)
    apply tendsto_iff_edist_tendsto_0.mpr
    change Tendsto (fun s => D (P s + z, P t + z)) (𝓝[Icc a b] t) (𝓝 0)
    change Tendsto (fun s => E (P s, P t)) (𝓝[Icc a b] t) (𝓝 0) at hlim
    simpa only [hDE] using hlim
  · rintro ⟨hab, hP⟩
    refine ⟨hab, ?_⟩
    intro t ht
    have hlim := tendsto_iff_edist_tendsto_0.mp (hP t ht)
    apply tendsto_iff_edist_tendsto_0.mpr
    change Tendsto (fun s => E (P s, P t)) (𝓝[Icc a b] t) (𝓝 0)
    change Tendsto (fun s => D (P s + z, P t + z)) (𝓝[Icc a b] t) (𝓝 0) at hlim
    simpa only [hDE] using hlim

private theorem mem_toSet_translate (A : EuclideanAnnulus) (z x : ℂ) :
    x ∈ A.toSet ↔ x + z ∈ (Positivity.Witnesses.annulusTranslate A z).toSet := by
  unfold EuclideanAnnulus.toSet
  simp only [EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
    EuclideanAnnulus.outerRadius, Positivity.Witnesses.annulusTranslate]
  rw [closure_ball _ A.2.1.ne', closure_ball _ A.2.1.ne']
  simp only [Set.mem_diff, Metric.mem_ball, Metric.mem_closedBall,
    dist_add_right]

private theorem image_boundary_translate (A : EuclideanAnnulus) (z : ℂ) :
    (Homeomorph.addRight z) '' A.innerBoundary =
      (Positivity.Witnesses.annulusTranslate A z).innerBoundary := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Positivity.Witnesses.mem_innerBoundary_translate A z y).1 hy
  · intro hx
    refine ⟨x - z, ?_, by simp⟩
    exact (Positivity.Witnesses.mem_innerBoundary_translate A z (x - z)).2 (by simpa using hx)

private theorem image_outerBoundary_translate (A : EuclideanAnnulus) (z : ℂ) :
    (Homeomorph.addRight z) '' A.outerBoundary =
      (Positivity.Witnesses.annulusTranslate A z).outerBoundary := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Positivity.Witnesses.mem_outerBoundary_translate A z y).1 hy
  · intro hx
    refine ⟨x - z, ?_, by simp⟩
    exact (Positivity.Witnesses.mem_outerBoundary_translate A z (x - z)).2 (by simpa using hx)

private theorem disconnects_translate (A : EuclideanAnnulus) (z : ℂ)
    (P : ℝ → ℂ) (a b : ℝ) :
    Disconnects (P '' Icc a b) A.innerBoundary A.outerBoundary ↔
      Disconnects ((fun t => P t + z) '' Icc a b)
        (Positivity.Witnesses.annulusTranslate A z).innerBoundary
        (Positivity.Witnesses.annulusTranslate A z).outerBoundary := by
  have hK : (Homeomorph.addRight z) '' (P '' Icc a b) =
      (fun t => P t + z) '' Icc a b := by
    simp only [Set.image_image]
    rfl
  rw [← hK, ← image_boundary_translate, ← image_outerBoundary_translate]
  exact (disconnects_image_iff (Homeomorph.addRight z)).symm

 
theorem aroundDist_translate (D E : LSCMetric) (A : EuclideanAnnulus) (z : ℂ)
    (hDE : ∀ x y : ℂ, E (x, y) = D (x + z, y + z)) :
    aroundDist E A = aroundDist D (Positivity.Witnesses.annulusTranslate A z) := by
  apply le_antisymm
  · unfold aroundDist
    refine le_iInf fun Q => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hQ => le_iInf fun hQA => le_iInf fun hQD => ?_
    let P : ℝ → ℂ := fun t => Q t - z
    have hP : E.IsCurve P a b :=
      (isCurve_translate D E z hDE P a b).2 (by simpa only [P, sub_add_cancel] using hQ)
    have hPA : ∀ t ∈ Icc a b, P t ∈ A.toSet := by
      intro t ht
      apply (mem_toSet_translate A z (P t)).2
      simpa only [P, sub_add_cancel] using hQA t ht
    have hPD : Disconnects (P '' Icc a b) A.innerBoundary A.outerBoundary := by
      apply (disconnects_translate A z P a b).2
      simpa only [P, sub_add_cancel] using hQD
    calc
      (⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : E.IsCurve P a b)
        (_ : ∀ t ∈ Icc a b, P t ∈ A.toSet)
        (_ : Disconnects (P '' Icc a b) A.innerBoundary A.outerBoundary), E.len P a b)
          ≤ E.len P a b := iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
            iInf_le_of_le hP <| iInf_le_of_le hPA <| iInf_le _ hPD
      _ = D.len Q a b := by
        rw [len_translate D E z hDE P a b]
        simp only [P, sub_add_cancel]
  · unfold aroundDist
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hPA => le_iInf fun hPD => ?_
    let Q : ℝ → ℂ := fun t => P t + z
    have hQ : D.IsCurve Q a b :=
      (isCurve_translate D E z hDE P a b).1 hP
    have hQA : ∀ t ∈ Icc a b, Q t ∈ (Positivity.Witnesses.annulusTranslate A z).toSet := by
      intro t ht
      exact (mem_toSet_translate A z (P t)).1 (hPA t ht)
    have hQD : Disconnects (Q '' Icc a b)
        (Positivity.Witnesses.annulusTranslate A z).innerBoundary
        (Positivity.Witnesses.annulusTranslate A z).outerBoundary :=
      (disconnects_translate A z P a b).1 hPD
    calc
      (⨅ (Q : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve Q a b)
        (_ : ∀ t ∈ Icc a b, Q t ∈ (Positivity.Witnesses.annulusTranslate A z).toSet)
        (_ : Disconnects (Q '' Icc a b)
          (Positivity.Witnesses.annulusTranslate A z).innerBoundary
          (Positivity.Witnesses.annulusTranslate A z).outerBoundary), D.len Q a b)
          ≤ D.len Q a b := iInf_le_of_le Q <| iInf_le_of_le a <| iInf_le_of_le b <|
            iInf_le_of_le hQ <| iInf_le_of_le hQA <| iInf_le _ hQD
      _ = E.len P a b := (len_translate D E z hDE P a b).symm

 
theorem ae_normalized_around_translate {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (A : EuclideanAnnulus)
    (z : ℂ) (r : Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P,
      ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg
          (LQGMetric.addConst (translateDist z (h ω))
            (-LQGMetric.circleAvg (h ω) 1 z)) r 0))) *
        aroundDist (D (LQGMetric.addConst (translateDist z (h ω))
          (-LQGMetric.circleAvg (h ω) 1 z))) (A.dilate r r.2) =
      ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r z))) *
        aroundDist (D (h ω)) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) := by
  let hz : Ω → LQGMetric.DistC := fun ω =>
    LQGMetric.addConst (translateDist z (h ω)) (-LQGMetric.circleAvg (h ω) 1 z)
  have hhz : LQGMetric.IsGFFPlusCont hz P := normalized_translate_isGFFPlusCont hh z
  have hwhole : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hh.1
  filter_upwards [ae_circleAvg_normalized_translate hh z r,
    Positivity.Witnesses.ae_annulus_addConst_eq_mul P hz hhz ξ Q D hD
      (fun ω => LQGMetric.circleAvg (h ω) 1 z),
    hD.translation P h hwhole z] with ω hca hw ht
  have hcancel : LQGMetric.addConst (hz ω) (LQGMetric.circleAvg (h ω) 1 z) =
      translateDist z (h ω) := by
    simp only [hz, LQGMetric.GFFLaw.addConst_addConst, neg_add_cancel,
      LQGMetric.GFFLaw.addConst_zero']
  have hmetric : aroundDist (D (h ω)) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) =
      ENNReal.ofReal (Real.exp ((ξ : ℝ) * LQGMetric.circleAvg (h ω) 1 z)) *
        aroundDist (D (hz ω)) (A.dilate r r.2) := by
    calc
      aroundDist (D (h ω)) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) =
          aroundDist (D (translateDist z (h ω))) (A.dilate r r.2) := by
        symm
        exact aroundDist_translate (D (h ω)) (D (translateDist z (h ω)))
          (A.dilate r r.2) z (fun x y => ht x y)
      _ = ENNReal.ofReal (Real.exp ((ξ : ℝ) * LQGMetric.circleAvg (h ω) 1 z)) *
          aroundDist (D (hz ω)) (A.dilate r r.2) := by
        rw [← hcancel]
        exact (hw (A.dilate r r.2)).2
  rw [hmetric, hca]
  change ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * (LQGMetric.circleAvg (h ω) r z -
        LQGMetric.circleAvg (h ω) 1 z)))) *
      aroundDist (D (hz ω)) (A.dilate r r.2) =
    ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r z))) *
      (ENNReal.ofReal (Real.exp ((ξ : ℝ) * LQGMetric.circleAvg (h ω) 1 z)) *
        aroundDist (D (hz ω)) (A.dilate r r.2))
  have hpos : 0 ≤ (r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r z)) :=
    mul_nonneg (le_of_lt (Real.rpow_pos_of_pos r.2 _)) (le_of_lt (Real.exp_pos _))
  rw [← mul_assoc, ← ENNReal.ofReal_mul hpos]
  congr 1
  rw [show -((ξ : ℝ) * (LQGMetric.circleAvg (h ω) r z -
      LQGMetric.circleAvg (h ω) 1 z)) =
      -((ξ : ℝ) * LQGMetric.circleAvg (h ω) r z) +
        (ξ : ℝ) * LQGMetric.circleAvg (h ω) 1 z by ring, Real.exp_add]
  ring

 
theorem offcenter_paired_uniform
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        ENNReal.ofReal p ≤ P {ω |
          ENNReal.ofReal A⁻¹ ≤
            ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
              Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r z))) *
              acrossDist (D (h ω))
                (Positivity.Witnesses.annulusTranslate (crossingShape.dilate r r.2) z) ∧
          ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
              Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r z))) *
              aroundDist (D' (h ω))
                (Positivity.Witnesses.annulusTranslate (separatorShape.dilate r r.2) z) ≤
            ENNReal.ofReal A} := by
  obtain ⟨A, hA, htail⟩ := origin_paired_uniform ξ Q D D' hD hD' p hp0 hp1
  refine ⟨A, hA, ?_⟩
  intro Ω mΩ P iP h hh z r
  let hz : Ω → LQGMetric.DistC := fun ω =>
    LQGMetric.addConst (translateDist z (h ω)) (-LQGMetric.circleAvg (h ω) 1 z)
  have hhz : IsNormalizedWholePlaneGFF hz P := normalized_translate_sub_circleAvg hh z
  have h₁ := Positivity.Witnesses.ae_normalized_across_translate P h hh ξ Q D hD crossingShape z r
  have h₂ := ae_normalized_around_translate P h hh ξ Q D' hD' separatorShape z r
  have hevent : {ω |
      ENNReal.ofReal A⁻¹ ≤ crossingX ξ Q D (hz ω) r ∧
      separatorY ξ Q D' (hz ω) r ≤ ENNReal.ofReal A} =ᵐ[P]
    {ω |
      ENNReal.ofReal A⁻¹ ≤
        ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
          Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r z))) *
          acrossDist (D (h ω))
            (Positivity.Witnesses.annulusTranslate (crossingShape.dilate r r.2) z) ∧
      ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
          Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r z))) *
          aroundDist (D' (h ω))
            (Positivity.Witnesses.annulusTranslate (separatorShape.dilate r r.2) z) ≤
        ENNReal.ofReal A} := by
    filter_upwards [h₁, h₂] with ω hω₁ hω₂
    simp only [Set.mem_ofPred_eq, crossingX, separatorY, hz]
    rw [hω₁, hω₂]
  rw [← measure_congr hevent]
  exact htail P hz hhz r

private theorem raw_upper_of_normalized (a b c : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a * b = 1) (d : ℝ≥0∞)
    (h : ENNReal.ofReal a * d ≤ ENNReal.ofReal c) :
    d ≤ ENNReal.ofReal (c * b) := by
  have hprod : ENNReal.ofReal b * ENNReal.ofReal a = 1 := by
    rw [mul_comm, ← ENNReal.ofReal_mul ha, hab, ENNReal.ofReal_one]
  calc
    d = ENNReal.ofReal b * (ENNReal.ofReal a * d) := by
      rw [← mul_assoc, hprod, one_mul]
    _ ≤ ENNReal.ofReal b * ENNReal.ofReal c := by gcongr
    _ = ENNReal.ofReal (c * b) := by
      rw [mul_comm c b, ENNReal.ofReal_mul hb]

 
theorem raw_paired_uniform
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        ENNReal.ofReal p ≤ P {ω |
          ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q) *
            Real.exp ((ξ : ℝ) * LQGMetric.circleAvg (h ω) r z)) ≤
              acrossDist (D (h ω))
                (Positivity.Witnesses.annulusTranslate (crossingShape.dilate r r.2) z) ∧
          aroundDist (D' (h ω))
                (Positivity.Witnesses.annulusTranslate (separatorShape.dilate r r.2) z) ≤
            ENNReal.ofReal (A * (r : ℝ) ^ ((ξ : ℝ) * Q) *
              Real.exp ((ξ : ℝ) * LQGMetric.circleAvg (h ω) r z))} := by
  obtain ⟨A, hA, htail⟩ := offcenter_paired_uniform ξ Q D D' hD hD' p hp0 hp1
  refine ⟨A, hA, ?_⟩
  intro Ω mΩ P iP h hh z r
  apply le_trans (htail P h hh z r)
  apply measure_mono
  intro ω hω
  let v : ℝ := (ξ : ℝ) * LQGMetric.circleAvg (h ω) r z
  let u : ℝ := (ξ : ℝ) * Q
  let a : ℝ := (r : ℝ) ^ (-u) * Real.exp (-v)
  let b : ℝ := (r : ℝ) ^ u * Real.exp v
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos r.2 _))
      (le_of_lt (Real.exp_pos _))
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos r.2 _))
      (le_of_lt (Real.exp_pos _))
  have hab : a * b = 1 := by
    dsimp [a, b]
    rw [Real.rpow_neg r.2.le, Real.exp_neg]
    have hr : (r : ℝ) ^ u ≠ 0 := (Real.rpow_pos_of_pos r.2 u).ne'
    have he : Real.exp v ≠ 0 := (Real.exp_pos v).ne'
    field_simp
  constructor
  · have hraw := Positivity.Witnesses.raw_lower_of_normalized a b A⁻¹ ha hb hab
      (acrossDist (D (h ω))
        (Positivity.Witnesses.annulusTranslate (crossingShape.dilate r r.2) z)) hω.1
    simpa only [a, b, u, v, mul_assoc] using hraw
  · have hraw := raw_upper_of_normalized a b A ha hb
      (by linarith) hab
      (aroundDist (D' (h ω))
        (Positivity.Witnesses.annulusTranslate (separatorShape.dilate r r.2) z)) hω.2
    simpa only [a, b, u, v, mul_assoc] using hraw

 
theorem ebl_one_scale_marginal
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D') :
    ∃ p c A : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 1 ≤ A ∧
      (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        LQGMetric.IsNormalizedWPGFF h P →
        ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω),
          LQGMetric.Blueprint.AnnulusIterHyp h (1 / 10) (4 / 5) r E →
          (∀ k, ENNReal.ofReal p ≤ P (E k)) →
          ∀ K : ℕ, P {ω | (LQGMetric.Blueprint.countOcc E K ω : ℝ) <
            (1 / 2 : ℝ) * K} ≤
            ENNReal.ofReal (c * Real.exp (-(8 * Real.log 10) * K))) ∧
      (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        ENNReal.ofReal p ≤ P {ω |
          ENNReal.ofReal (A⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q) *
            Real.exp ((ξ : ℝ) * LQGMetric.circleAvg (h ω) r z)) ≤
              acrossDist (D (h ω))
                (Positivity.Witnesses.annulusTranslate (crossingShape.dilate r r.2) z) ∧
          aroundDist (D' (h ω))
                (Positivity.Witnesses.annulusTranslate (separatorShape.dilate r r.2) z) ≤
            ENNReal.ofReal (A * (r : ℝ) ^ ((ξ : ℝ) * Q) *
              Real.exp ((ξ : ℝ) * LQGMetric.circleAvg (h ω) r z))}) := by
  obtain ⟨p, c, hp0, hp1, hc, hLM⟩ := exists_iteration_constants
  obtain ⟨A, hA, htail⟩ := raw_paired_uniform ξ Q D D' hD hD' p hp0 hp1
  exact ⟨p, c, A, hp0, hp1, hc, hA, hLM, htail⟩


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale
