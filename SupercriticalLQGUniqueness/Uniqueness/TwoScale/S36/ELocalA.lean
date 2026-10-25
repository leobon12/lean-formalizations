import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EScale
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Determinism.HDet
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.CanonicalH
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.Smoothing




 














set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC DistOn addConst restrictTo)

 

section ScaleOptimal

variable {d₁ e₁ d₂ e₂ : LSCMetric} {k : ℝ≥0∞}

theorem ratioPair_scale_iff (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hd : ∀ x y, d₂ (x, y) = k * d₁ (x, y)) (u v : ℂ) :
    OptimalConstants.Ratios.RatioPair d₂ u v ↔ OptimalConstants.Ratios.RatioPair d₁ u v := by
  rw [OptimalConstants.Ratios.ratioPair_iff_finite_positive, OptimalConstants.Ratios.ratioPair_iff_finite_positive, hd,
    mul_lt_top_iff_of_ne hk0 hkt]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, pos_iff_ne_zero.mpr fun h0 => by rw [h0, mul_zero] at h2; exact lt_irrefl _ h2,
      h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, ENNReal.mul_pos hk0 h2.ne', h3⟩

theorem lowerOptimal_scale (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hd : ∀ x y, d₂ (x, y) = k * d₁ (x, y)) (he : ∀ x y, e₂ (x, y) = k * e₁ (x, y)) :
    OptimalConstants.Ratios.lowerOptimal d₂ e₂ = OptimalConstants.Ratios.lowerOptimal d₁ e₁ := by
  unfold OptimalConstants.Ratios.lowerOptimal
  refine iInf_congr fun u => iInf_congr fun v => ?_
  rw [hd, he, ENNReal.mul_div_mul_left _ _ hk0 hkt]
  exact iInf_congr_Prop (ratioPair_scale_iff hk0 hkt hd u v) fun _ => rfl

theorem upperOptimal_scale (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hd : ∀ x y, d₂ (x, y) = k * d₁ (x, y)) (he : ∀ x y, e₂ (x, y) = k * e₁ (x, y)) :
    OptimalConstants.Ratios.upperOptimal d₂ e₂ = OptimalConstants.Ratios.upperOptimal d₁ e₁ := by
  unfold OptimalConstants.Ratios.upperOptimal
  refine iSup_congr fun u => iSup_congr fun v => ?_
  rw [hd, he, ENNReal.mul_div_mul_left _ _ hk0 hkt]
  exact iSup_congr_Prop (ratioPair_scale_iff hk0 hkt hd u v) fun _ => rfl

end ScaleOptimal

 

 
def halfAnnShape (z : ℂ) (r : Ioi (0 : ℝ)) : EuclideanAnnulus :=
  ⟨(z / (r : ℂ), ((1 : ℝ) / 2, 1)), by norm_num, by norm_num⟩

theorem halfAnnShape_dilate_center (z : ℂ) (r : Ioi (0 : ℝ)) :
    ((halfAnnShape z r).dilate r r.2).center = z := by
  change (r : ℝ) • (z / (r : ℂ)) = z
  rw [Complex.real_smul]
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast r.2.ne'
  field_simp

theorem setDist_middle_le_across (D : LSCMetric) (z : ℂ) (r : Ioi (0 : ℝ)) :
    OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) ≤
      acrossDist D ((halfAnnShape z r).dilate r r.2) := by
  have hr : (0 : ℝ) < r := r.2
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  have hc := halfAnnShape_dilate_center z r
  have hxF : x ∈ TwoScale.S36Events.eventBoundary z r := by
    left
    have h : x ∈ Metric.sphere ((halfAnnShape z r).dilate r r.2).center
        (((halfAnnShape z r).dilate r r.2).innerRadius) := hx
    rw [hc] at h
    rw [Metric.mem_sphere] at h ⊢
    rw [h]
    change (r : ℝ) * (1 / 2) = r / 2
    ring
  have hyM : y ∈ TwoScale.S36Events.eventMiddle z r := by
    have h : y ∈ Metric.sphere ((halfAnnShape z r).dilate r r.2).center
        (((halfAnnShape z r).dilate r r.2).outerRadius) := hy
    rw [hc] at h
    rw [Metric.mem_sphere] at h
    have hy1 : dist y z = r := by rw [h]; change (r : ℝ) * 1 = r; ring
    exact sphere_subset_middle hr (by linarith) (by linarith) (Metric.mem_sphere.mpr hy1)
  calc
    OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) ≤ D (y, x) :=
      iInf₂_le_of_le y hyM
        (iInf₂_le (f := fun w (_ : w ∈ TwoScale.S36Events.eventBoundary z r) => D (y, w)) x hxF)
    _ = D (x, y) := D.isExtMetric.2.2.1 y x

 
theorem ae_acrossDist_dilate_lt_top (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (A : EuclideanAnnulus) (s : Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P, acrossDist (D (h ω)) (A.dilate s s.2) < ⊤ := by
  let X : Ioi (0 : ℝ) → Ω → ℝ≥0∞ := fun s ω =>
    ENNReal.ofReal ((s : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) s 0))) *
      acrossDist (D (h ω)) (A.dilate s s.2)
  have hV : IsTwoSidedTight P X :=
    (hD.tightness P h hh (fun s ω => LQGMetric.circleAvg (h ω) s 0)
      (fun s => ae_isCircleAverage_old hh.1 s 0) A).1
  filter_upwards [OptimalConstants.Determinism.ae_lt_top_of_twoSidedTight P X hV s] with ω hfin
  have hcoef : 0 < ((s : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) s 0))) := by
    have : (0 : ℝ) < s := s.2
    positivity
  by_contra hn
  have ht : acrossDist (D (h ω)) (A.dilate s s.2) = ⊤ := eq_top_iff.mpr (not_lt.mp hn)
  have hcf : ENNReal.ofReal ((s : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) s 0))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hcoef).ne'
  have : X s ω = ⊤ := by simp only [X, ht, ENNReal.mul_top hcf]
  exact (ne_top_of_lt hfin) this

 

 
abbrev muH {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC) : Measure DistC :=
  (P.prod BiLipschitz.OneScale.standardGaussian).map (BiLipschitz.OneScale.gaussianShift h)

theorem muH_isProb {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : LQGMetric.IsWholePlaneGFF h P) : IsProbabilityMeasure (muH P h) :=
  (Measure.isProbabilityMeasure_map_iff
    (BiLipschitz.OneScale.gff_gaussianShift P h hh).measurable.aemeasurable).2 inferInstance

section Canonical

variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistC)

 
theorem ae_muH_of_prod (hh : LQGMetric.IsWholePlaneGFF h P) {S : Set DistC}
    (hS : MeasurableSet S)
    (hp : ∀ᵐ x ∂(P.prod BiLipschitz.OneScale.standardGaussian), BiLipschitz.OneScale.gaussianShift h x ∈ S) :
    ∀ᵐ g ∂(muH P h), g ∈ S :=
  (ae_map_iff (BiLipschitz.OneScale.gff_gaussianShift P h hh).measurable.aemeasurable hS).2 hp

 
theorem ae_prod_of_ae {p : DistC → Prop} (hp : ∀ᵐ ω ∂P, p (h ω)) :
    ∀ᵐ x ∂(P.prod BiLipschitz.OneScale.standardGaussian), p (h x.1) :=
  Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst hp

 
theorem ae_prod_weyl (hh : LQGMetric.IsWholePlaneGFF h P) (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) :
    ∀ᵐ x ∂(P.prod BiLipschitz.OneScale.standardGaussian), ∀ u v : ℂ,
      D (BiLipschitz.OneScale.gaussianShift h x) (u, v) =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * x.2)) * D (h x.1) (u, v) := by
  have hprod : LQGMetric.IsGFFPlusCont (fun x : Ω × ℝ => h x.1)
      (P.prod BiLipschitz.OneScale.standardGaussian) :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp (BiLipschitz.OneScale.gff_prod_fst P BiLipschitz.OneScale.standardGaussian h hh)
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul (P.prod BiLipschitz.OneScale.standardGaussian) (fun x => h x.1)
    hprod ξ Q D hD (fun x => x.2)] with x hx u v
  exact hx (u, v)

theorem expScale_ne_zero (ξ t : ℝ) : ENNReal.ofReal (Real.exp (ξ * t)) ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

 
theorem muH_ae_middle_lt_top (hh : IsNormalizedWholePlaneGFF h P) (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) (z : ℂ) (r : Ioi (0 : ℝ)) :
    ∀ᵐ g ∂(muH P h), OptimalConstants.Ratios.setDist (D g) (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) < ⊤ := by
  have hS : MeasurableSet {g : DistC |
      OptimalConstants.Ratios.setDist (D g) (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) < ⊤} :=
    measurableSet_lt ((measurable_setDist_middle z r.2).comp hD.measurable) measurable_const
  refine ae_muH_of_prod P h hh.1 hS ?_
  have hbase := ae_prod_of_ae P h
    (p := fun g => acrossDist (D g) ((halfAnnShape z r).dilate r r.2) < ⊤)
    (ae_acrossDist_dilate_lt_top ξ Q D hD P h hh (halfAnnShape z r) r)
  filter_upwards [hbase, ae_prod_weyl P h hh.1 ξ Q D hD] with x hx hw
  change OptimalConstants.Ratios.setDist (D (BiLipschitz.OneScale.gaussianShift h x)) _ _ < ⊤
  rw [setDist_eq_mul_of_scale (expScale_ne_zero _ _) ENNReal.ofReal_ne_top hw]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((setDist_middle_le_across (D (h x.1)) z r).trans_lt hx)

 
theorem muH_ae_ratioPair (hh : IsNormalizedWholePlaneGFF h P) (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) :
    ∀ᵐ g ∂(muH P h), ∃ u v : ℂ, OptimalConstants.Ratios.RatioPair (D g) u v := by
  let A : EuclideanAnnulus := ⟨((0 : ℂ), (1 : ℝ), (2 : ℝ)), by norm_num, by norm_num⟩
  let s : Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  have hS : MeasurableSet {g : DistC | acrossDist (D g) (A.dilate s s.2) < ⊤} :=
    measurableSet_lt ((measurable_acrossDist _).comp hD.measurable) measurable_const
  have hfin : ∀ᵐ g ∂(muH P h), acrossDist (D g) (A.dilate s s.2) < ⊤ := by
    refine ae_muH_of_prod P h hh.1 hS ?_
    filter_upwards [ae_prod_of_ae P h (p := fun g => acrossDist (D g) (A.dilate s s.2) < ⊤)
        (ae_acrossDist_dilate_lt_top ξ Q D hD P h hh A s),
      ae_prod_weyl P h hh.1 ξ Q D hD] with x hx hw
    change acrossDist (D (BiLipschitz.OneScale.gaussianShift h x)) _ < ⊤
    rw [Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale (D (h x.1)) (D (BiLipschitz.OneScale.gaussianShift h x)) _
      (expScale_ne_zero _ _) ENNReal.ofReal_ne_top hw]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hx
  filter_upwards [hfin] with g hg
  exact OptimalConstants.Determinism.finite_pair_of_acrossDist_lt_top (D g) _ hg

 
theorem muH_ae_optima (hh : IsNormalizedWholePlaneGFF h P) (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (cMinus cPlus : ℝ≥0∞)
    (hm : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hM : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) :
    ∀ᵐ g ∂(muH P h), OptimalConstants.Ratios.lowerOptimal (D g) (D' g) = cMinus ∧
      OptimalConstants.Ratios.upperOptimal (D g) (D' g) = cPlus ∧
      ∀ u v : ℂ, cMinus * D g (u, v) ≤ D' g (u, v) ∧ D' g (u, v) ≤ cPlus * D g (u, v) := by
  have := muH_isProb P h hh.1
  have hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) (muH P h) :=
    BiLipschitz.OneScale.canonical_gaussianShift_isGFFPlusCont P h hh.1
  have hmeasH := (BiLipschitz.OneScale.gff_gaussianShift P h hh.1).measurable
  obtain ⟨K, hK, hEBL⟩ := BiLipschitz.EqualNormalizer.ebl ξ Q D D' hD hD'
  have hB : ∀ᵐ g ∂(muH P h), OptimalConstants.Ratios.BiLipBound (D g) (D' g)
      (ENNReal.ofReal K)⁻¹ (ENNReal.ofReal K) := by
    filter_upwards [hEBL (muH P h) id hμ] with g hg
    exact OptimalConstants.Determinism.biLipBound_of_symmetric_ebl K hK (D g) (D' g) hg
  have hc : 0 < (ENNReal.ofReal K)⁻¹ := ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top
  have hpair := muH_ae_ratioPair P h hh ξ Q D hD
  obtain ⟨hX₁, hX₂⟩ := OptimalConstants.OrderTests.aeMeasurable_optima (muH P h) D D' hD.measurable hD'.measurable
    hc hB hpair
  
  have hW := ae_prod_weyl P h hh.1 ξ Q D hD
  have hW' := ae_prod_weyl P h hh.1 ξ Q D' hD'
  have hprod₁ : ∀ᵐ x ∂(P.prod BiLipschitz.OneScale.standardGaussian),
      OptimalConstants.Ratios.lowerOptimal (D (BiLipschitz.OneScale.gaussianShift h x)) (D' (BiLipschitz.OneScale.gaussianShift h x)) = cMinus := by
    filter_upwards [ae_prod_of_ae P h (p := fun g => OptimalConstants.Ratios.lowerOptimal (D g) (D' g) = cMinus) hm,
      hW, hW'] with x hx hw hw'
    rw [lowerOptimal_scale (expScale_ne_zero _ _) ENNReal.ofReal_ne_top hw hw']
    exact hx
  have hprod₂ : ∀ᵐ x ∂(P.prod BiLipschitz.OneScale.standardGaussian),
      OptimalConstants.Ratios.upperOptimal (D (BiLipschitz.OneScale.gaussianShift h x)) (D' (BiLipschitz.OneScale.gaussianShift h x)) = cPlus := by
    filter_upwards [ae_prod_of_ae P h (p := fun g => OptimalConstants.Ratios.upperOptimal (D g) (D' g) = cPlus) hM,
      hW, hW'] with x hx hw hw'
    rw [upperOptimal_scale (expScale_ne_zero _ _) ENNReal.ofReal_ne_top hw hw']
    exact hx
  
  have htr : ∀ {X : DistC → ℝ≥0∞} (hX : AEMeasurable X (muH P h)) (c : ℝ≥0∞),
      (∀ᵐ x ∂(P.prod BiLipschitz.OneScale.standardGaussian), X (BiLipschitz.OneScale.gaussianShift h x) = c) →
      ∀ᵐ g ∂(muH P h), X g = c := by
    intro X hX c hprod
    have hS : MeasurableSet {g : DistC | hX.mk X g = c} :=
      measurableSet_eq_fun hX.measurable_mk measurable_const
    have hmk : ∀ᵐ x ∂(P.prod BiLipschitz.OneScale.standardGaussian),
        X (BiLipschitz.OneScale.gaussianShift h x) = hX.mk X (BiLipschitz.OneScale.gaussianShift h x) :=
      ae_of_ae_map hmeasH.aemeasurable hX.ae_eq_mk
    have h3 : ∀ᵐ g ∂(muH P h), hX.mk X g = c := by
      refine (ae_map_iff hmeasH.aemeasurable hS).2 ?_
      filter_upwards [hprod, hmk] with x h1 h2
      change hX.mk X (BiLipschitz.OneScale.gaussianShift h x) = c
      rw [← h2]
      exact h1
    filter_upwards [h3, hX.ae_eq_mk] with g h1 h2
    rw [h2]
    exact h1
  have h₁ := htr hX₁ cMinus hprod₁
  have h₂ := htr hX₂ cPlus hprod₂
  filter_upwards [h₁, h₂, hB, hpair] with g hg₁ hg₂ hb hp
  refine ⟨hg₁, hg₂, fun u v => ?_⟩
  have hall := OptimalConstants.Ratios.optimal_allPairs_of_biLipBound hc hb hp u v
  rw [hg₁, hg₂] at hall
  exact hall

end Canonical

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
