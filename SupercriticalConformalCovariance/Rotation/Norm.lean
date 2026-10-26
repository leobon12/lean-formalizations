import SupercriticalConformalCovariance.Rotation.Unique
import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import LQGMetric.Field.ExistGFF

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness

namespace SupercriticalConformalCovariance.Rotation

def unitAnnulus : EuclideanAnnulus :=
  ⟨((0 : ℂ), (1, 2)), by norm_num, by norm_num⟩

private theorem unitAnnulus_mem_rot_iff (a : ℂ) (ha : ‖a‖ = 1)
    (r : ℝ) (z : ℂ) :
    z ∈ Metric.sphere (0 : ℂ) r ↔ a⁻¹ * z ∈ Metric.sphere (0 : ℂ) r := by
  simp only [Metric.mem_sphere, dist_zero_right, norm_mul,
    GaussianLQG.norm_inv_of_norm_eq_one ha, one_mul]

theorem acrossDist_rotMetric_unitAnnulus (a : ℂ) (ha : ‖a‖ = 1)
    (M : LSCMetric) :
    acrossDist (rotMetric a (GaussianLQG.ne_zero_of_norm_eq_one ha) M) unitAnnulus =
      acrossDist M unitAnnulus := by
  have ha0 := GaussianLQG.ne_zero_of_norm_eq_one ha
  have hmem (r : ℝ) (z : ℂ) :
      z ∈ Metric.sphere (0 : ℂ) r ↔ a⁻¹ * z ∈ Metric.sphere (0 : ℂ) r :=
    unitAnnulus_mem_rot_iff a ha r z
  unfold acrossDist
  apply le_antisymm
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    have hx' : a * x ∈ unitAnnulus.innerBoundary := by
      apply (hmem 1 (a * x)).2
      simpa only [EuclideanAnnulus.innerBoundary, EuclideanAnnulus.innerRadius,
        EuclideanAnnulus.center, unitAnnulus, inv_mul_cancel_left₀ ha0] using hx
    have hy' : a * y ∈ unitAnnulus.outerBoundary := by
      apply (hmem 2 (a * y)).2
      simpa only [EuclideanAnnulus.outerBoundary, EuclideanAnnulus.outerRadius,
        EuclideanAnnulus.center, unitAnnulus, inv_mul_cancel_left₀ ha0] using hy
    calc
      acrossDist (rotMetric a ha0 M) unitAnnulus
          ≤ rotMetric a ha0 M (a * x, a * y) := iInf₂_le_of_le _ hx' (iInf₂_le _ hy')
      _ = M (x, y) := by simp [rotMetric_apply, inv_mul_cancel_left₀ ha0]
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    have hx' : a⁻¹ * x ∈ unitAnnulus.innerBoundary := (hmem 1 x).1 hx
    have hy' : a⁻¹ * y ∈ unitAnnulus.outerBoundary := (hmem 2 y).1 hy
    calc
      acrossDist M unitAnnulus ≤ M (a⁻¹ * x, a⁻¹ * y) :=
        iInf₂_le_of_le _ hx' (iInf₂_le _ hy')
      _ = rotMetric a ha0 M (x, y) := rfl

private def boundedObs (x : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (x.toReal / (1 + x.toReal))

private theorem measurable_boundedObs : Measurable boundedObs := by
  unfold boundedObs
  fun_prop

private theorem boundedObs_le_one (x : ℝ≥0∞) : boundedObs x ≤ 1 := by
  unfold boundedObs
  have hx : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  have hd : 0 < 1 + x.toReal := by positivity
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_iff₀ hd).2 (by linarith)

private theorem boundedObs_strictMono_of_finite {x y : ℝ≥0∞}
    (hy : y < ⊤) (hxy : x < y) : boundedObs x < boundedObs y := by
  have hx : x < ⊤ := hxy.trans hy
  have hxr : x.toReal < y.toReal := (ENNReal.toReal_lt_toReal hx.ne hy.ne).2 hxy
  have hx0 : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  have hy0 : 0 ≤ y.toReal := ENNReal.toReal_nonneg
  have hdx : 0 < 1 + x.toReal := by positivity
  have hdy : 0 < 1 + y.toReal := by positivity
  unfold boundedObs
  apply (ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) hdy)).2
  apply (div_lt_div_iff₀ hdx hdy).2
  nlinarith

private theorem no_equal_law_of_ae_lt {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ≥0∞) (hXm : Measurable X) (hYm : Measurable Y)
    (hlaw : P.map X = P.map Y)
    (hXfin : ∀ᵐ ω ∂P, X ω < ⊤) (hYfin : ∀ᵐ ω ∂P, Y ω < ⊤)
    (hXY : ∀ᵐ ω ∂P, X ω < Y ω) : False := by
  have hbound : ∫⁻ ω, boundedObs (X ω) ∂P ≠ ⊤ := by
    apply ne_of_lt
    calc
      ∫⁻ ω, boundedObs (X ω) ∂P ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P :=
        lintegral_mono fun ω => boundedObs_le_one (X ω)
      _ < ⊤ := by simp
  have hstrict : ∫⁻ ω, boundedObs (X ω) ∂P <
      ∫⁻ ω, boundedObs (Y ω) ∂P := by
    apply lintegral_strict_mono (by
      intro hP
      have hm : P Set.univ = 1 := measure_univ
      simp [hP] at hm) (measurable_boundedObs.comp hYm).aemeasurable hbound
    filter_upwards [hXfin, hYfin, hXY] with ω hxf hyf hxy
    exact boundedObs_strictMono_of_finite hyf hxy
  have heq : ∫⁻ ω, boundedObs (X ω) ∂P =
      ∫⁻ ω, boundedObs (Y ω) ∂P := by
    calc
      ∫⁻ ω, boundedObs (X ω) ∂P = ∫⁻ x, boundedObs x ∂(P.map X) :=
        (lintegral_map measurable_boundedObs hXm).symm
      _ = ∫⁻ x, boundedObs x ∂(P.map Y) := by rw [hlaw]
      _ = ∫⁻ ω, boundedObs (Y ω) ∂P :=
        lintegral_map measurable_boundedObs hYm
  exact (ne_of_lt hstrict) heq

private theorem equal_scale_law_implies_one {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ≥0∞) (hXm : Measurable X)
    (hXpos : ∀ᵐ ω ∂P, 0 < X ω) (hXfin : ∀ᵐ ω ∂P, X ω < ⊤)
    (C : ℝ) (hC : 0 < C)
    (hlaw : P.map X = P.map (fun ω => ENNReal.ofReal C * X ω)) : C = 1 := by
  let Y : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal C * X ω
  have hYm : Measurable Y := measurable_const.mul hXm
  have hYfin : ∀ᵐ ω ∂P, Y ω < ⊤ := by
    filter_upwards [hXfin] with ω hx
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hx
  have hlt (ω : Ω) (hx0 : 0 < X ω) (hxf : X ω < ⊤)
      (h1 : 1 < C) : X ω < Y ω := by
    have hxr : 0 < (X ω).toReal := ENNReal.toReal_pos hx0.ne' hxf.ne
    have hyr : (Y ω).toReal = C * (X ω).toReal := by
      simp [Y, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le]
    have hyf : Y ω < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hxf
    apply (ENNReal.toReal_lt_toReal hxf.ne hyf.ne).1
    rw [hyr]
    nlinarith
  rcases lt_trichotomy C 1 with hlt1 | heq | hgt1
  · have hrev : ∀ᵐ ω ∂P, Y ω < X ω := by
      filter_upwards [hXpos, hXfin] with ω hx0 hxf
      have hxr : 0 < (X ω).toReal := ENNReal.toReal_pos hx0.ne' hxf.ne
      have hyf : Y ω < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hxf
      apply (ENNReal.toReal_lt_toReal hyf.ne hxf.ne).1
      simp only [Y, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le]
      nlinarith
    exact (no_equal_law_of_ae_lt P Y X hYm hXm hlaw.symm hYfin hXfin hrev).elim
  · exact heq
  · have hfor : ∀ᵐ ω ∂P, X ω < Y ω := by
      filter_upwards [hXpos, hXfin] with ω hx0 hxf
      exact hlt ω hx0 hxf hgt1
    exact (no_equal_law_of_ae_lt P X Y hXm hYm hlaw hXfin hYfin hfor).elim

/-- The deterministic constant supplied by strong metric uniqueness for a rotation is one. -/
private theorem rotation_constant_eq_one_of_uniqueness
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (a : ℂ) (ha : ‖a‖ = 1) (C : ℝ) (hC : 0 < C)
    (hEq : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ u v : ℂ,
          (D (GaussianLQG.rotDist a (h ω))).1
            (a⁻¹ * u, a⁻¹ * v) =
          ENNReal.ofReal C * (D (h ω)).1 (u, v)) : C = 1 := by
  obtain ⟨Ω, mΩ, P, iP, h, hh⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := iP
  let X : Ω → ℝ≥0∞ := fun ω => acrossDist (D (h ω)) unitAnnulus
  let Y : Ω → ℝ≥0∞ := fun ω => acrossDist (D (GaussianLQG.rotDist a (h ω))) unitAnnulus
  have hplus : IsGFFPlusCont h P :=
    LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh.1
  have hXm : Measurable X := (measurable_acrossDist unitAnnulus).comp (hD.1.comp hh.1.measurable)
  have hYm : Measurable Y :=
    (measurable_acrossDist unitAnnulus).comp
      (hD.1.comp ((GaussianLQG.measurable_rotDist a).comp hh.1.measurable))
  have hXpos : ∀ᵐ ω ∂P, 0 < X ω :=
    Filter.Eventually.of_forall fun ω => B2.Strong.acrossDist_pos _ unitAnnulus
  have hXfin : ∀ᵐ ω ∂P, X ω < ⊤ :=
    B2.Strong.ae_acrossDist_lt_top hD P h hplus unitAnnulus
  have hYlaw : P.map Y = P.map X := by
    let Φ : DistC → ℝ≥0∞ := fun g => acrossDist (D g) unitAnnulus
    have hΦ : Measurable Φ := (measurable_acrossDist unitAnnulus).comp hD.1
    calc
      P.map Y = P.map (Φ ∘ fun ω => GaussianLQG.rotDist a (h ω)) := rfl
      _ = (P.map (fun ω => GaussianLQG.rotDist a (h ω))).map Φ :=
        (Measure.map_map hΦ ((GaussianLQG.measurable_rotDist a).comp hh.1.measurable)).symm
      _ = (P.map h).map Φ := by rw [GaussianLQG.map_rotDist_eq hh ha]
      _ = P.map X := Measure.map_map hΦ hh.1.measurable
  have hscale : ∀ᵐ ω ∂P, Y ω = ENNReal.ofReal C * X ω := by
    filter_upwards [hEq P h hplus] with ω hω
    have hd : ∀ x y : ℂ,
        rotMetric a (GaussianLQG.ne_zero_of_norm_eq_one ha)
          (D (GaussianLQG.rotDist a (h ω))) (x, y) =
          ENNReal.ofReal C * D (h ω) (x, y) := fun x y => hω x y
    have hmul := Uniqueness.Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale
      (D (h ω))
      (rotMetric a (GaussianLQG.ne_zero_of_norm_eq_one ha)
        (D (GaussianLQG.rotDist a (h ω))))
      (ENNReal.ofReal C) ((ENNReal.ofReal_pos.mpr hC).ne')
      ENNReal.ofReal_ne_top hd unitAnnulus
    exact (acrossDist_rotMetric_unitAnnulus a ha _).symm.trans hmul
  have hlaw : P.map X = P.map (fun ω => ENNReal.ofReal C * X ω) :=
    hYlaw.symm.trans (Measure.map_congr hscale)
  exact equal_scale_law_implies_one P X hXm hXpos hXfin C hC hlaw

/-- DG Proposition 1.9, inverse-coordinate form, for every strong LQG metric. -/
theorem ae_rotation_covariance_inv
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (a : ℂ) (ha : ‖a‖ = 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D (h ω)).1 (u, v) =
      (D (GaussianLQG.rotDist a (h ω))).1 (a⁻¹ * u, a⁻¹ * v) := by
  obtain ⟨C, hC, hEq⟩ := exists_rotation_constant ξ Q hQ D hD a ha
  have hC1 := rotation_constant_eq_one_of_uniqueness ξ Q hQ D hD a ha C hC hEq
  filter_upwards [hEq P h hh] with ω hω u v
  simpa [hC1] using (hω u v).symm

/-- DG Proposition 1.9, forward-coordinate form. -/
theorem ae_rotation_covariance
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (a : ℂ) (ha : ‖a‖ = 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D (h ω)).1 (a * u, a * v) =
      (D (GaussianLQG.rotDist a (h ω))).1 (u, v) := by
  have ha0 := GaussianLQG.ne_zero_of_norm_eq_one ha
  filter_upwards [ae_rotation_covariance_inv ξ Q hQ D hD a ha P h hh] with ω hω u v
  simpa only [inv_mul_cancel_left₀ ha0] using hω (a * u) (a * v)




end SupercriticalConformalCovariance.Rotation
