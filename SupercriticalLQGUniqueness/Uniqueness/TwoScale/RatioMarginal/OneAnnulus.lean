import NV1Evidence
import SLUFieldSupport
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.AroundTranslate




 





set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.RatioMarginal

open LQGMetric (DistC circleAvg)

def normAcross (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (g : DistC) (A : EuclideanAnnulus) (r : Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * circleAvg g r 0))) *
    acrossDist (D g) (A.dilate r r.2)

def normAround (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (g : DistC) (A : EuclideanAnnulus) (r : Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * circleAvg g r 0))) *
    aroundDist (D g) (A.dilate r r.2)

theorem measurable_normAcross (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (A : EuclideanAnnulus) (r : Ioi (0 : ℝ)) :
    Measurable (fun g => normAcross ξ Q D g A r) := by
  have hca : Measurable fun g : DistC => circleAvg g r 0 :=
    LQGMetric.measurable_circleAvg_left r 0
  have har : Measurable fun g : DistC => acrossDist (D g) (A.dilate r r.2) :=
    (measurable_acrossDist _).comp hD.measurable
  exact ((measurable_const.mul
    ((Real.measurable_exp.comp (measurable_const.mul hca).neg))).ennreal_ofReal).mul har

theorem measurable_normAround (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (A : EuclideanAnnulus) (r : Ioi (0 : ℝ)) :
    Measurable (fun g => normAround ξ Q D g A r) := by
  have hca : Measurable fun g : DistC => circleAvg g r 0 :=
    LQGMetric.measurable_circleAvg_left r 0
  have har : Measurable fun g : DistC => aroundDist (D g) (A.dilate r r.2) :=
    (Toolkit.CountableBase.aroundBoundedAnnulus_borel _).comp hD.measurable
  exact ((measurable_const.mul
    ((Real.measurable_exp.comp (measurable_const.mul hca).neg))).ennreal_ofReal).mul har

 
theorem ratio_of_normalized_bounds (n c x y : ℝ≥0∞)
    (hn0 : n ≠ 0) (hnTop : n ≠ ∞) (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hx : n * x ≤ c) (hy : c⁻¹ ≤ n * y) :
    x ≤ c * c * y := by
  apply (ENNReal.mul_le_mul_iff_left hn0 hnTop).1
  calc
    x * n = n * x := mul_comm _ _
    _ ≤ c := hx
    _ = c * c * c⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hc0 hcTop, mul_one]
    _ ≤ c * c * (n * y) := by gcongr
    _ = (c * c * y) * n := by ac_rfl

 

theorem origin_ratio_marginal {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (A : EuclideanAnnulus)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ r : Ioi (0 : ℝ),
      ENNReal.ofReal p ≤ P {ω |
        ENNReal.ofReal M⁻¹ ≤ normAcross ξ Q D (h ω) A r ∧
        normAround ξ Q D (h ω) A r ≤ ENNReal.ofReal M} := by
  let ε : ℝ := (1 - p) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hV := hD.tightness P h hh (fun r ω => circleAvg (h ω) r 0)
    (fun r => ae_isCircleAverage_old hh.1 r 0) A
  obtain ⟨M₁, hM₁, ht₁⟩ := hV.1.2 ε hε
  obtain ⟨M₂, hM₂, ht₂⟩ := hV.2.2 ε hε
  let M := max 1 (max M₁ M₂)
  have hM : 1 ≤ M := le_max_left _ _
  have hM₁M : M₁ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM₂M : M₂ ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨M, hM, ?_⟩
  intro r
  have hcross : P {ω | normAcross ξ Q D (h ω) A r < ENNReal.ofReal M⁻¹} ≤
      ENNReal.ofReal ε := by
    apply le_trans (measure_mono ?_) (ht₁ r).2
    intro ω hω
    have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
    have hMinv : M⁻¹ ≤ M₁⁻¹ := (inv_le_inv₀ hM0 hM₁).2 hM₁M
    exact lt_of_lt_of_le hω (ENNReal.ofReal_le_ofReal hMinv)
  have haround : P {ω | ENNReal.ofReal M < normAround ξ Q D (h ω) A r} ≤
      ENNReal.ofReal ε := by
    apply le_trans (measure_mono ?_) (ht₂ r).1
    intro ω hω
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hM₂M) hω
  have hgood : MeasurableSet {ω |
      ENNReal.ofReal M⁻¹ ≤ normAcross ξ Q D (h ω) A r ∧
      normAround ξ Q D (h ω) A r ≤ ENNReal.ofReal M} := by
    exact (measurableSet_le measurable_const
      ((measurable_normAcross ξ Q D hD A r).comp hh.1.measurable)).inter
      (measurableSet_le ((measurable_normAround ξ Q D hD A r).comp hh.1.measurable)
        measurable_const)
  have hcomp : P {ω |
      ¬ (ENNReal.ofReal M⁻¹ ≤ normAcross ξ Q D (h ω) A r ∧
      normAround ξ Q D (h ω) A r ≤ ENNReal.ofReal M)} ≤
      ENNReal.ofReal (1 - p) := by
    calc
      P {ω | ¬ (ENNReal.ofReal M⁻¹ ≤ normAcross ξ Q D (h ω) A r ∧
        normAround ξ Q D (h ω) A r ≤ ENNReal.ofReal M)} ≤
          P {ω | normAcross ξ Q D (h ω) A r < ENNReal.ofReal M⁻¹} +
          P {ω | ENNReal.ofReal M < normAround ξ Q D (h ω) A r} := by
            apply le_trans (measure_mono ?_) (measure_union_le _ _)
            intro ω hω
            simp only [Set.mem_ofPred_eq, not_and_or, not_le] at hω
            exact hω
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add hcross haround
      _ = ENNReal.ofReal (1 - p) := by
        rw [← ENNReal.ofReal_add hε.le]
        congr 1
        dsimp [ε]
        ring
        exact hε.le
  have hpE : ENNReal.ofReal p ≤ (1 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp1.le
  have hid : (1 : ℝ≥0∞) - ENNReal.ofReal (1 - p) = ENNReal.ofReal p := by
    rw [ENNReal.ofReal_sub 1 hp0.le, ENNReal.ofReal_one]
    exact ENNReal.sub_sub_cancel (by norm_num) hpE
  have hcompl : P {ω |
      ENNReal.ofReal M⁻¹ ≤ normAcross ξ Q D (h ω) A r ∧
      normAround ξ Q D (h ω) A r ≤ ENNReal.ofReal M} =
      (1 : ℝ≥0∞) - P {ω | ¬ (ENNReal.ofReal M⁻¹ ≤ normAcross ξ Q D (h ω) A r ∧
      normAround ξ Q D (h ω) A r ≤ ENNReal.ofReal M)} := by
    simpa only [Set.compl_ofPred, not_not] using
      (prob_compl_eq_one_sub (μ := P) hgood.compl)
  rw [hcompl, ← hid]
  exact tsub_le_tsub_left hcomp 1

 

theorem origin_raw_ratio_marginal {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (A : EuclideanAnnulus)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ r : Ioi (0 : ℝ),
      ENNReal.ofReal p ≤ P {ω |
        aroundDist (D (h ω)) (A.dilate r r.2) ≤
          (ENNReal.ofReal M * ENNReal.ofReal M) *
            acrossDist (D (h ω)) (A.dilate r r.2)} := by
  obtain ⟨M, hM, hprob⟩ := origin_ratio_marginal P h hh ξ Q D hD A p hp0 hp1
  refine ⟨M, hM, fun r => (hprob r).trans ?_⟩
  apply measure_mono
  intro ω hω
  dsimp [normAcross, normAround] at hω
  let n : ℝ≥0∞ := ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * circleAvg (h ω) r 0)))
  have hnreal : 0 < (r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg (h ω) r 0)) :=
    mul_pos (Real.rpow_pos_of_pos r.2 _) (Real.exp_pos _)
  have hn0 : n ≠ 0 := (ENNReal.ofReal_pos.mpr hnreal).ne'
  have hnTop : n ≠ ∞ := ENNReal.ofReal_ne_top
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hc0 : ENNReal.ofReal M ≠ 0 := (ENNReal.ofReal_pos.mpr hM0).ne'
  have hcTop : ENNReal.ofReal M ≠ ∞ := ENNReal.ofReal_ne_top
  have hlow : (ENNReal.ofReal M)⁻¹ ≤ n * acrossDist (D (h ω)) (A.dilate r r.2) := by
    simpa only [ENNReal.ofReal_inv_of_pos hM0] using hω.1
  exact ratio_of_normalized_bounds n (ENNReal.ofReal M)
    (aroundDist (D (h ω)) (A.dilate r r.2))
    (acrossDist (D (h ω)) (A.dilate r r.2))
    hn0 hnTop hc0 hcTop hω.2 hlow

 

theorem origin_ratio_uniform
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (A : EuclideanAnnulus)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P → ∀ r : Ioi (0 : ℝ),
        ENNReal.ofReal p ≤ P {ω |
          ENNReal.ofReal M⁻¹ ≤ normAcross ξ Q D (h ω) A r ∧
          normAround ξ Q D (h ω) A r ≤ ENNReal.ofReal M} := by
  obtain ⟨μ, hμprob, hμ⟩ := Positivity.Witnesses.exists_canonical_normalized_law
  letI : IsProbabilityMeasure μ := hμprob
  obtain ⟨M, hM, htail⟩ := origin_ratio_marginal μ id hμ ξ Q D hD A p hp0 hp1
  refine ⟨M, hM, ?_⟩
  intro Ω mΩ P iP h hh r
  let B : Set DistC := {g |
    ENNReal.ofReal M⁻¹ ≤ normAcross ξ Q D g A r ∧
    normAround ξ Q D g A r ≤ ENNReal.ofReal M}
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const (measurable_normAcross ξ Q D hD A r)).inter
      (measurableSet_le (measurable_normAround ξ Q D hD A r) measurable_const)
  have hlaw : P.map h = μ := by
    simpa only [Measure.map_id] using map_eq_of_candidate_normalized hh hμ
  change ENNReal.ofReal p ≤ P (h ⁻¹' B)
  rw [← Measure.map_apply hh.1.measurable hB, hlaw]
  simpa only [id_eq] using htail r

 

def normAcrossAt (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (g : DistC) (A : EuclideanAnnulus) (z : ℂ) (r : Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * circleAvg g r z))) *
    acrossDist (D g) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z)

def normAroundAt (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (g : DistC) (A : EuclideanAnnulus) (z : ℂ) (r : Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * circleAvg g r z))) *
    aroundDist (D g) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z)

 

theorem center_ratio_uniform
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (A : EuclideanAnnulus)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        ENNReal.ofReal p ≤ P {ω |
          ENNReal.ofReal M⁻¹ ≤ normAcrossAt ξ Q D (h ω) A z r ∧
          normAroundAt ξ Q D (h ω) A z r ≤ ENNReal.ofReal M} := by
  obtain ⟨M, hM, hprob⟩ := origin_ratio_uniform ξ Q D hD A p hp0 hp1
  refine ⟨M, hM, ?_⟩
  intro Ω mΩ P iP h hh z r
  let hz : Ω → DistC := fun ω =>
    LQGMetric.addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)
  have hhz : IsNormalizedWholePlaneGFF hz P := normalized_translate_sub_circleAvg hh z
  have hcross := Positivity.Witnesses.ae_normalized_across_translate P h hh ξ Q D hD A z r
  have haround := BiLipschitz.OneScale.ae_normalized_around_translate P h hh ξ Q D hD A z r
  have hsub : ∀ᵐ ω ∂P,
      (ENNReal.ofReal M⁻¹ ≤ normAcross ξ Q D (hz ω) A r ∧
        normAround ξ Q D (hz ω) A r ≤ ENNReal.ofReal M) →
      (ENNReal.ofReal M⁻¹ ≤ normAcrossAt ξ Q D (h ω) A z r ∧
        normAroundAt ξ Q D (h ω) A z r ≤ ENNReal.ofReal M) := by
    filter_upwards [hcross, haround] with ω hc ha hgood
    have hc' : normAcross ξ Q D (hz ω) A r = normAcrossAt ξ Q D (h ω) A z r := hc
    have ha' : normAround ξ Q D (hz ω) A r = normAroundAt ξ Q D (h ω) A z r := ha
    exact ⟨hc' ▸ hgood.1, ha' ▸ hgood.2⟩
  exact (hprob P hz hhz r).trans (measure_mono_ae hsub)

 

theorem center_raw_ratio_uniform
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (A : EuclideanAnnulus)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        ENNReal.ofReal p ≤ P {ω |
          aroundDist (D (h ω)) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) ≤
            (ENNReal.ofReal M * ENNReal.ofReal M) *
              acrossDist (D (h ω)) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z)} := by
  obtain ⟨M, hM, hprob⟩ := center_ratio_uniform ξ Q D hD A p hp0 hp1
  refine ⟨M, hM, ?_⟩
  intro Ω mΩ P iP h hh z r
  apply (hprob P h hh z r).trans
  apply measure_mono
  intro ω hω
  dsimp [normAcrossAt, normAroundAt] at hω
  let n : ℝ≥0∞ := ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * circleAvg (h ω) r z)))
  have hnreal : 0 < (r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg (h ω) r z)) :=
    mul_pos (Real.rpow_pos_of_pos r.2 _) (Real.exp_pos _)
  have hn0 : n ≠ 0 := (ENNReal.ofReal_pos.mpr hnreal).ne'
  have hnTop : n ≠ ∞ := ENNReal.ofReal_ne_top
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hc0 : ENNReal.ofReal M ≠ 0 := (ENNReal.ofReal_pos.mpr hM0).ne'
  have hcTop : ENNReal.ofReal M ≠ ∞ := ENNReal.ofReal_ne_top
  have hlow : (ENNReal.ofReal M)⁻¹ ≤ n *
      acrossDist (D (h ω)) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) := by
    simpa only [ENNReal.ofReal_inv_of_pos hM0] using hω.1
  exact ratio_of_normalized_bounds n (ENNReal.ofReal M)
    (aroundDist (D (h ω)) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z))
    (acrossDist (D (h ω)) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z))
    hn0 hnTop hc0 hcTop hω.2 hlow


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.RatioMarginal
