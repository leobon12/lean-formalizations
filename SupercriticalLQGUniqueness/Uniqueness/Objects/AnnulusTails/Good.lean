import SupercriticalLQGUniqueness.Uniqueness.TwoScale.RatioMarginal.OneAnnulus
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.ELocalB
import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Cover




 






















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

open LQGMetric (DistC DistOn addConst restrictTo)

 
def shape12 : EuclideanAnnulus := ⟨(0, (1, 2)), by norm_num, by norm_num⟩

 
def ann12 (w : ℂ) (t : Ioi (0 : ℝ)) : EuclideanAnnulus :=
  Positivity.Witnesses.annulusTranslate (shape12.dilate t t.2) w

@[simp] theorem ann12_center (w : ℂ) (t : Ioi (0 : ℝ)) : (ann12 w t).center = w := by
  change (t : ℝ) • (0 : ℂ) + w = w
  simp

@[simp] theorem ann12_innerRadius (w : ℂ) (t : Ioi (0 : ℝ)) : (ann12 w t).innerRadius = t := by
  change (t : ℝ) * 1 = t
  ring

@[simp] theorem ann12_outerRadius (w : ℂ) (t : Ioi (0 : ℝ)) :
    (ann12 w t).outerRadius = 2 * t := by
  change (t : ℝ) * 2 = 2 * t
  ring

 

def goodAnn (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (M : ℝ) (w : ℂ)
    (t : Ioi (0 : ℝ)) : Set DistC :=
  {g | ENNReal.ofReal M⁻¹ ≤ TwoScale.RatioMarginal.normAcrossAt ξ Q D g shape12 w t ∧
    TwoScale.RatioMarginal.normAroundAt ξ Q D g shape12 w t ≤ ENNReal.ofReal M}

theorem measurable_normAcrossAt (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : Measurable D) (A : EuclideanAnnulus) (z : ℂ) (r : Ioi (0 : ℝ)) :
    Measurable fun g => TwoScale.RatioMarginal.normAcrossAt ξ Q D g A z r := by
  have hca : Measurable fun g : DistC => LQGMetric.circleAvg g r z :=
    LQGMetric.measurable_circleAvg_left r z
  have har : Measurable fun g : DistC =>
      acrossDist (D g) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) :=
    (measurable_acrossDist _).comp hD
  exact ((measurable_const.mul
    ((Real.measurable_exp.comp (measurable_const.mul hca).neg))).ennreal_ofReal).mul har

theorem measurable_normAroundAt (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : Measurable D) (A : EuclideanAnnulus) (z : ℂ) (r : Ioi (0 : ℝ)) :
    Measurable fun g => TwoScale.RatioMarginal.normAroundAt ξ Q D g A z r := by
  have hca : Measurable fun g : DistC => LQGMetric.circleAvg g r z :=
    LQGMetric.measurable_circleAvg_left r z
  have har : Measurable fun g : DistC =>
      aroundDist (D g) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) :=
    (Toolkit.CountableBase.aroundBoundedAnnulus_borel _).comp hD
  exact ((measurable_const.mul
    ((Real.measurable_exp.comp (measurable_const.mul hca).neg))).ennreal_ofReal).mul har

theorem measurableSet_goodAnn (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : Measurable D) (M : ℝ) (w : ℂ) (t : Ioi (0 : ℝ)) :
    MeasurableSet (goodAnn ξ Q D M w t) :=
  (measurableSet_le measurable_const (measurable_normAcrossAt ξ Q D hD shape12 w t)).inter
    (measurableSet_le (measurable_normAroundAt ξ Q D hD shape12 w t) measurable_const)

 
theorem exists_goodAnn_prob (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (w : ℂ) (t : Ioi (0 : ℝ)),
        ENNReal.ofReal p ≤ P {ω | h ω ∈ goodAnn ξ Q D M w t} :=
  TwoScale.RatioMarginal.center_ratio_uniform ξ Q D hD shape12 p hp0 hp1

 
theorem circleAvg_congr_restrict {U : TopologicalSpace.Opens ℂ} {g₁ g₂ : DistC}
    (he : restrictTo U g₁ = restrictTo U g₂) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hsU : sphere z r ⊆ U) : LQGMetric.circleAvg g₁ r z = LQGMetric.circleAvg g₂ r z := by
  obtain ⟨ε, hε, hthick⟩ := (isCompact_sphere z r).exists_thickening_subset_open U.isOpen hsU
  obtain ⟨N, hN⟩ := LQGMetric.CONF.exists_circBump_supp hr z (subset_refl _) hε
  have heq : (fun n => LQGMetric.CircleAvg.mollAvg g₁ n z r) =ᶠ[atTop]
      (fun n => LQGMetric.CircleAvg.mollAvg g₂ n z r) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [LQGMetric.CircleAvg.mollAvg_eq, LQGMetric.CircleAvg.mollAvg_eq]
    exact LQGMetric.DFGPS.L217.apply_eq_of_restrictTo_eq he _ ((hN n hn).trans hthick)
  rw [LQGMetric.CircleAvg.circleAvg_eq_limUnder, LQGMetric.CircleAvg.circleAvg_eq_limUnder]
  unfold limUnder
  rw [Filter.map_congr heq]

 
def goodCarrier (w : ℂ) (t : ℝ) : Set ℂ := {y | 3 * t / 4 < ‖y - w‖ ∧ ‖y - w‖ < 9 * t / 4}

 
theorem goodAnn_transfer {ξ : Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric} {M : ℝ} {w : ℂ}
    {t : Ioi (0 : ℝ)} {g₁ g₂ : DistC} {U : TopologicalSpace.Opens ℂ}
    (hB₁ : BiLipschitz.Barrier.Barrier (D g₁)) (hB₂ : BiLipschitz.Barrier.Barrier (D g₂))
    (hL₁ : (D g₁).IsLengthSpace) (hL₂ : (D g₂).IsLengthSpace)
    (hI : ∀ x y, TwoScale.S36.intExt (D g₁) U x y = TwoScale.S36.intExt (D g₂) U x y)
    (hres : restrictTo U g₁ = restrictTo U g₂) (hU : goodCarrier w t ⊆ U) :
    g₁ ∈ goodAnn ξ Q D M w t ↔ g₂ ∈ goodAnn ξ Q D M w t := by
  have ht : (0 : ℝ) < t := t.2
  have hA : (ann12 w t).toSet ⊆ U := by
    intro y hy
    rw [EuclideanAnnulus.toSet_eq] at hy
    simp only [ann12_center, ann12_innerRadius, ann12_outerRadius, mem_ofPred_eq,
      dist_eq_norm] at hy
    exact hU ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hsub : {y : ℂ | (ann12 w t).innerRadius < ‖y - (ann12 w t).center‖ ∧
      ‖y - (ann12 w t).center‖ < 9 * t / 4} ⊆ U := by
    intro y hy
    simp only [ann12_center, ann12_innerRadius, mem_ofPred_eq] at hy
    exact hU ⟨by linarith [hy.1], hy.2⟩
  have hR : (ann12 w t).outerRadius < 9 * t / 4 := by
    rw [ann12_outerRadius]
    linarith
  have hS : sphere w (t : ℝ) ⊆ U := by
    intro y hy
    rw [mem_sphere, dist_eq_norm] at hy
    exact hU ⟨by linarith, by linarith⟩
  have ha := TwoScale.S36.around_transfer hI hA
  have hc := TwoScale.S36.across_transfer hB₁ hB₂ hL₁ hL₂ hI hR hsub
  have hca := circleAvg_congr_restrict hres ht w hS
  simp only [goodAnn, TwoScale.RatioMarginal.normAcrossAt, TwoScale.RatioMarginal.normAroundAt, mem_ofPred_eq]
  change ENNReal.ofReal M⁻¹ ≤ _ * acrossDist (D g₁) (ann12 w t) ∧
      _ * aroundDist (D g₁) (ann12 w t) ≤ _ ↔
    ENNReal.ofReal M⁻¹ ≤ _ * acrossDist (D g₂) (ann12 w t) ∧
      _ * aroundDist (D g₂) (ann12 w t) ≤ _
  rw [ha, hc, hca]

 
theorem ae_goodAnn_addConst_iff {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    (hw : LQGMetric.IsWholePlaneGFF h P) (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (M : ℝ) (w : ℂ) (t : Ioi (0 : ℝ)) (c : Ω → ℝ) :
    ∀ᵐ ω ∂P, (addConst (h ω) (c ω) ∈ goodAnn ξ Q D M w t ↔ h ω ∈ goodAnn ξ Q D M w t) := by
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul P h hh ξ Q D hD c,
    LQGMetric.CircleAvg.ae_circleAvg_addConst hw w t.2] with ω hsc hca
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω)) with hk
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hkt : k ≠ ⊤ := ENNReal.ofReal_ne_top
  have hscale : ∀ x y : ℂ, D (addConst (h ω) (c ω)) (x, y) = k * D (h ω) (x, y) :=
    fun x y => hsc (x, y)
  have hA := Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale (D (h ω)) (D (addConst (h ω) (c ω))) k hk0 hkt
    hscale (ann12 w t)
  have hC := Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale (D (h ω)) (D (addConst (h ω) (c ω))) k hk0
    hkt hscale (ann12 w t)
  have hN : ENNReal.ofReal ((t : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (addConst (h ω) (c ω)) t w))) * k =
      ENNReal.ofReal ((t : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) t w))) := by
    rw [hca (c ω), hk, ← ENNReal.ofReal_mul
      (mul_nonneg (Real.rpow_nonneg t.2.le _) (Real.exp_pos _).le)]
    congr 1
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp only [goodAnn, TwoScale.RatioMarginal.normAcrossAt, TwoScale.RatioMarginal.normAroundAt, mem_ofPred_eq]
  change ENNReal.ofReal M⁻¹ ≤ _ * acrossDist (D (addConst (h ω) (c ω))) (ann12 w t) ∧
      _ * aroundDist (D (addConst (h ω) (c ω))) (ann12 w t) ≤ _ ↔
    ENNReal.ofReal M⁻¹ ≤ _ * acrossDist (D (h ω)) (ann12 w t) ∧
      _ * aroundDist (D (h ω)) (ann12 w t) ≤ _
  rw [hA, hC, ← mul_assoc, ← mul_assoc, hN]

 
theorem canonical_goodAnn_local {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (M : ℝ) (w : ℂ) (t : Ioi (0 : ℝ))
    (U : TopologicalSpace.Opens ℂ) (hU : goodCarrier w t ⊆ U) :
    ∃ S : Set (DistOn U), MeasurableSet S ∧
      goodAnn ξ Q D M w t =ᵐ[TwoScale.S36.muH P h] restrictTo U ⁻¹' S := by
  have hprob := TwoScale.S36.muH_isProb P h hh.1
  have hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) (TwoScale.S36.muH P h) :=
    BiLipschitz.OneScale.canonical_gaussianShift_isGFFPlusCont P h hh.1
  set E := goodAnn ξ Q D M w t with hEdef
  obtain ⟨FD, -, hlocD⟩ := hD.locality (TwoScale.S36.muH P h) id hμ U
  have hGood : ∀ᵐ g ∂(TwoScale.S36.muH P h), BiLipschitz.Barrier.Barrier (D g) ∧ (D g).IsLengthSpace ∧
      (D g).internal U = FD (restrictTo U g) := by
    filter_upwards [BiLipschitz.OneScale.canonical_gaussianShift_barrier P h hh ξ Q hQ D hD,
      hD.length (TwoScale.S36.muH P h) id hμ, hlocD] with g h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨W, hWae, hWm, hWsub⟩ := hGood.exists_measurable_mem
  let R : DistC → LQGMetric.CoordJ → ℝ := fun g => LQGMetric.pairJ U (restrictTo U g)
  have hR : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp (LQGMetric.measurable_restrictTo U)
  have hV : Measurable[LQGMetric.Blueprint.fieldSigma id U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ E → g₂ ∈ E := by
    intro g₁ hg₁ g₂ hg₂ he hE₁
    have hres : restrictTo U g₁ = restrictTo U g₂ := LQGMetric.injective_pairJ U he
    obtain ⟨hB₁, hL₁, hi₁⟩ := hWsub g₁ hg₁
    obtain ⟨hB₂, hL₂, hi₂⟩ := hWsub g₂ hg₂
    have hId : ∀ u v, TwoScale.S36.intExt (D g₁) U u v = TwoScale.S36.intExt (D g₂) U u v :=
      TwoScale.S36.intExt_eq_of_internal_eq (by rw [hi₁, hi₂, hres])
    exact (goodAnn_transfer hB₁ hB₂ hL₁ hL₂ hId hres hU).mp hE₁
  have hB : NullMeasurableSet E ((TwoScale.S36.muH P h).map id) :=
    (measurableSet_goodAnn ξ Q D hD.measurable M w t).nullMeasurableSet
  have hLocal := LQGMetric.LocalEvent.aeEventIn_of_saturated
    (Y := id) (R := R) (V := R) (B := E) (W := W)
    measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl) hWm hB hWae hsat
  obtain ⟨F, hFm, hFe⟩ := hLocal
  obtain ⟨S, hS, hF⟩ := MeasurableSpace.measurableSet_comap.mp hFm
  refine ⟨S, hS, ?_⟩
  rw [← hF] at hFe
  exact hFe

 

theorem goodAnn_centered_local {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (M : ℝ) (w : ℂ) (t : Ioi (0 : ℝ))
    (U : TopologicalSpace.Opens ℂ) (hU : goodCarrier w t ⊆ U) (R : ℝ) :
    LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => addConst (h ω) (-LQGMetric.circleAvg (h ω) R w)) U)
      {ω | h ω ∈ goodAnn ξ Q D M w t} := by
  set E := goodAnn ξ Q D M w t with hEdef
  let q' : Ω → DistOn U := fun ω => restrictTo U (addConst (h ω) (-LQGMetric.circleAvg (h ω) R w))
  obtain ⟨S, hS, hLocal⟩ := canonical_goodAnn_local P h hh ξ Q hQ D hD M w t U hU
  have hmeasH := (BiLipschitz.OneScale.gff_gaussianShift P h hh.1).measurable
  have hLocalProd : {y : Ω × ℝ | BiLipschitz.OneScale.gaussianShift h y ∈ E}
      =ᵐ[P.prod BiLipschitz.OneScale.standardGaussian]
      {y : Ω × ℝ | restrictTo U (BiLipschitz.OneScale.gaussianShift h y) ∈ S} :=
    ae_of_ae_map hmeasH.aemeasurable hLocal
  have hprodW : LQGMetric.IsWholePlaneGFF (fun y : Ω × ℝ => h y.1)
      (P.prod BiLipschitz.OneScale.standardGaussian) :=
    BiLipschitz.OneScale.gff_prod_fst P BiLipschitz.OneScale.standardGaussian h hh.1
  have hprod : LQGMetric.IsGFFPlusCont (fun y : Ω × ℝ => h y.1)
      (P.prod BiLipschitz.OneScale.standardGaussian) :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hprodW
  have hInv := ae_goodAnn_addConst_iff (P.prod BiLipschitz.OneScale.standardGaussian) (fun y => h y.1)
    hprod hprodW ξ Q D hD M w t (fun y => y.2)
  have hAE : ∀ᵐ y ∂P.prod BiLipschitz.OneScale.standardGaussian,
      (h y.1 ∈ E ↔
        BiLipschitz.OneScale.localShift U (q' y.1) (LQGMetric.circleAvg (h y.1) R w + y.2) ∈ S) := by
    filter_upwards [hInv, hLocalProd] with y hi hl
    have hShift : BiLipschitz.OneScale.localShift U (q' y.1) (LQGMetric.circleAvg (h y.1) R w + y.2) =
        restrictTo U (BiLipschitz.OneScale.gaussianShift h y) := by
      calc
        BiLipschitz.OneScale.localShift U (q' y.1) (LQGMetric.circleAvg (h y.1) R w + y.2) =
            restrictTo U (addConst (addConst (h y.1) (-LQGMetric.circleAvg (h y.1) R w))
              (LQGMetric.circleAvg (h y.1) R w + y.2)) :=
          BiLipschitz.OneScale.localShift_restrictTo U _ _
        _ = restrictTo U (addConst (h y.1) y.2) := by
          rw [LQGMetric.GFFLaw.addConst_addConst]
          congr 2
          ring
        _ = restrictTo U (BiLipschitz.OneScale.gaussianShift h y) := rfl
    rw [hShift]
    exact hi.symm.trans (Iff.of_eq hl)
  have hSmooth := BiLipschitz.OneScale.gaussian_smoothing_event P U q'
    (fun ω => LQGMetric.circleAvg (h ω) R w) {ω | h ω ∈ E} S hS hAE
  refine ⟨{ω | BiLipschitz.OneScale.gaussianSmooth U S (q' ω) > 1 / 2}, ?_, ?_⟩
  · have hB : MeasurableSet {v : DistOn U | BiLipschitz.OneScale.gaussianSmooth U S v > 1 / 2} :=
      measurableSet_lt measurable_const (BiLipschitz.OneScale.measurable_gaussianSmooth U hS)
    exact hB.preimage (Measurable.of_comap_le le_rfl)
  · filter_upwards [hSmooth] with ω hω
    exact propext hω

end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
