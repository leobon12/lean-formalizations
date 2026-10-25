import SupercriticalLQGUniqueness.B2.WeakStrong.DilMetric

 

















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC DistOn ofCont addFun addConst IsGFFPlusCont affineComp circleAvg restrictTo
  affinePt)

namespace SupercriticalLQGUniqueness.B2.WeakStrong

 
def normFactor (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (s : Set.Ioi (0 : ℝ)) (g : DistC) : ℝ≥0∞ :=
  ENNReal.ofReal ((s : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * circleAvg g s 0)))

 
def normAcross (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (A : EuclideanAnnulus)
    (s : Set.Ioi (0 : ℝ)) (g : DistC) : ℝ≥0∞ :=
  normFactor ξ Q s g * acrossDist (D g) (A.dilate s s.2)

 
def normAround (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (A : EuclideanAnnulus)
    (s : Set.Ioi (0 : ℝ)) (g : DistC) : ℝ≥0∞ :=
  normFactor ξ Q s g * aroundDist (D g) (A.dilate s s.2)

theorem measurable_normFactor (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (s : Set.Ioi (0 : ℝ)) :
    Measurable (normFactor ξ Q s) :=
  ENNReal.measurable_ofReal.comp (measurable_const.mul
    (Real.measurable_exp.comp ((LQGMetric.measurable_circleAvg_left _ _).const_mul _).neg))

theorem measurable_normAcross {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : Measurable D) (A : EuclideanAnnulus) (s : Set.Ioi (0 : ℝ)) :
    Measurable (normAcross ξ Q D A s) :=
  (measurable_normFactor ξ Q s).mul ((measurable_acrossDist _).comp hD)

theorem measurable_normAround {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : Measurable D) (A : EuclideanAnnulus) (s : Set.Ioi (0 : ℝ)) :
    Measurable (normAround ξ Q D A s) :=
  (measurable_normFactor ξ Q s).mul ((Uniqueness.TwoScale.S36.measurable_aroundDist_fixed _).comp hD)

theorem dilate_dilate (A : EuclideanAnnulus) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    (A.dilate r hr).dilate c hc = A.dilate (c * r) (mul_pos hc hr) := by
  apply Subtype.ext
  simp [EuclideanAnnulus.dilate, EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
    EuclideanAnnulus.outerRadius, mul_smul, mul_assoc]

 
def divIoi (r b : Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(r : ℝ) / b, Set.mem_Ioi.mpr (div_pos r.2 b.2)⟩

theorem scalar_identity (ξ Q r b ar ab : ℝ) (hr : 0 < r) (hb : 0 < b) :
    r ^ (-(ξ * Q)) * Real.exp (-(ξ * ar)) * Real.exp (ξ * (ab + Q * Real.log b)) =
      (r / b) ^ (-(ξ * Q)) * Real.exp (-(ξ * (ar - ab))) := by
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos (div_pos hr hb), Real.log_div hr.ne' hb.ne',
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

 
theorem ae_normalized_dilMetric (hD : IsWeakLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {k : Ω → DistC} (hk : IsNormalizedWholePlaneGFF k P)
    (b r : Set.Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P, ∀ A : EuclideanAnnulus,
      normFactor ξ Q r (k ω) * acrossDist (dilMetric D Q b (k ω)) (A.dilate r r.2) =
          normAcross ξ Q D A (divIoi r b) (B2.Strong.rescaledField (k ω) b) ∧
        normFactor ξ Q r (k ω) * aroundDist (dilMetric D Q b (k ω)) (A.dilate r r.2) =
          normAround ξ Q D A (divIoi r b) (B2.Strong.rescaledField (k ω) b) := by
  have hwp : LQGMetric.IsWholePlaneGFF k P := hk.1
  have hplus : IsGFFPlusCont k P := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hwp
  have hkt := isGFFPlusCont_rescaledField hplus b
  have hb : (0 : ℝ) < b := b.2
  have hr : (0 : ℝ) < r := r.2
  filter_upwards [hD.2.2.2.1 P _ hkt, hD.2.1 P _ hkt,
    ae_circleAvg_rescaledField hwp b (divIoi r b)] with ω hW hL hC A
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = circleAvg (k ω) b 0 + Q * Real.log b := ⟨_, rfl⟩
  set K : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * c))
  have hK0 : K ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hKt : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmet : ∀ x y : ℂ, D (dilField Q b (k ω)) (x, y) =
      K * D (B2.Strong.rescaledField (k ω) b) (x, y) := by
    intro x y
    have := congrFun (hW (ContinuousMap.const ℂ c)) (x, y)
    rw [weylScale_const _ _ _ hL] at this
    rw [dilField_eq_addFun_rescaled, ← hc]
    exact this.symm
  have hbinv : (0 : ℝ) < (b : ℝ)⁻¹ := inv_pos.mpr hb
  have hm : ∀ x y : ℂ, dilMetric D Q b (k ω) (x, y) =
      D (dilField Q b (k ω)) ((b : ℝ)⁻¹ • x, (b : ℝ)⁻¹ • y) := fun _ _ => rfl
  have hA : (A.dilate r hr).dilate (b : ℝ)⁻¹ hbinv = A.dilate (divIoi r b) (divIoi r b).2 := by
    rw [dilate_dilate]
    congr 1
    simp only [divIoi]
    ring
  have hbs : (b : ℝ) * (divIoi r b : ℝ) = r := by
    simp only [divIoi]; field_simp
  have hfac : normFactor ξ Q r (k ω) * K =
      normFactor ξ Q (divIoi r b) (B2.Strong.rescaledField (k ω) b) := by
    simp only [normFactor, K]
    rw [← ENNReal.ofReal_mul (by positivity), hC, hbs, hc, scalar_identity _ _ _ _ _ _ hr hb]
    rfl
  constructor
  · rw [B2.Strong.acrossDist_eq_of_dilate _ _ hbinv hm, hA,
      Uniqueness.Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale _ _ K hK0 hKt hmet,
      ← mul_assoc, hfac]
    rfl
  · rw [B2.Strong.aroundDist_eq_of_dilate _ _ hbinv hm, hA,
      Uniqueness.Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale _ _ K hK0 hKt hmet,
      ← mul_assoc, hfac]
    rfl

 

theorem isTwoSidedTight_of_map_eq_index {Ω ι κ : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ι → Ω → ℝ≥0∞) (Y : κ → Ω → ℝ≥0∞) (hY : IsTwoSidedTight P Y) (σ : ι → κ)
    (hX : ∀ i, AEMeasurable (X i) P) (hlaw : ∀ i, P.map (X i) = P.map (Y (σ i))) :
    IsTwoSidedTight P X := by
  refine ⟨hX, fun ε hε => ?_⟩
  obtain ⟨M, hM, hbd⟩ := hY.2 ε hε
  refine ⟨M, hM, fun i => ?_⟩
  have hset : ∀ S : Set ℝ≥0∞, MeasurableSet S → P (X i ⁻¹' S) = P (Y (σ i) ⁻¹' S) := by
    intro S hS
    rw [← Measure.map_apply_of_aemeasurable (hX i) hS, hlaw i,
      Measure.map_apply_of_aemeasurable (hY.1 (σ i)) hS]
  exact ⟨(hset _ measurableSet_Ioi).trans_le (hbd (σ i)).1,
    (hset _ measurableSet_Iio).trans_le (hbd (σ i)).2⟩

theorem map_comp_eq_of_map_eq {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {P : Measure Ω}
    {g h : Ω → E} (hg : Measurable g) (hh : Measurable h) (hlaw : P.map g = P.map h)
    {Φ : E → ℝ≥0∞} (hΦ : Measurable Φ) : P.map (Φ ∘ g) = P.map (Φ ∘ h) := by
  rw [← Measure.map_map hΦ hg, hlaw, Measure.map_map hΦ hh]

theorem circleAvg_ae_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hwp : LQGMetric.IsWholePlaneGFF h P) {a : Set.Ioi (0 : ℝ) → Ω → ℝ}
    (ha : ∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω)) (r : Set.Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P, a r ω = circleAvg (h ω) r 0 := by
  filter_upwards [ha r, ae_isCircleAverage_old hwp r 0] with ω h₁ h₂
  exact tendsto_nhds_unique h₁ h₂

 
theorem tight_normAcross (hD : IsWeakLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (A : EuclideanAnnulus) :
    IsTwoSidedTight P (fun s ω => normAcross ξ Q D A s (h ω)) ∧
      IsTwoSidedTight P (fun s ω => normAround ξ Q D A s (h ω)) :=
  hD.2.2.2.2.2 P h hh (fun s ω => circleAvg (h ω) s 0)
    (fun s => ae_isCircleAverage_old hh.1 s 0) A

 
theorem tightness_dilMetric (hD : IsWeakLQGMetric ξ Q D) (b : Set.Ioi (0 : ℝ)) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ a : Set.Ioi (0 : ℝ) → Ω → ℝ,
        (∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω)) →
        ∀ A : EuclideanAnnulus,
          IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
            ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * a r ω))) *
              acrossDist (dilMetric D Q b (h ω)) (A.dilate r r.2)) ∧
          IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
            ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * a r ω))) *
              aroundDist (dilMetric D Q b (h ω)) (A.dilate r r.2)) := by
  intro Ω _ P _ h hh a ha A
  have hmeas : Measurable h := hh.1.measurable
  have hkt : Measurable fun ω => B2.Strong.rescaledField (h ω) b :=
    (B2.Strong.measurable_rescaledField b).comp hmeas
  have hlaw : P.map (fun ω => B2.Strong.rescaledField (h ω) b) = P.map h :=
    LQGMetric.CircleAvg.map_affine_sub_circleAvg (isNormalizedWholePlaneGFF_iff_old.mp hh) b.2 0
  obtain ⟨hT₁, hT₂⟩ := tight_normAcross hD hh A
  have hfac : ∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P,
      ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * a r ω))) =
        normFactor ξ Q r (h ω) := fun r => by
    filter_upwards [circleAvg_ae_eq hh.1 ha r] with ω hω
    rw [normFactor, hω]
  constructor
  · refine isTwoSidedTight_of_map_eq_index P _ _ hT₁ (fun r => divIoi r b) (fun r => ?_)
      (fun r => ?_)
    · have he : (fun ω => ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
            Real.exp (-((ξ : ℝ) * a r ω))) * acrossDist (dilMetric D Q b (h ω)) (A.dilate r r.2))
          =ᵐ[P] (normAcross ξ Q D A (divIoi r b)) ∘ fun ω => B2.Strong.rescaledField (h ω) b := by
        filter_upwards [hfac r, ae_normalized_dilMetric hD hh b r] with ω h₁ h₂
        rw [h₁, (h₂ A).1]
        rfl
      exact ((measurable_normAcross hD.1 A _).comp hkt).aemeasurable.congr he.symm
    · have he : (fun ω => ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
            Real.exp (-((ξ : ℝ) * a r ω))) * acrossDist (dilMetric D Q b (h ω)) (A.dilate r r.2))
          =ᵐ[P] (normAcross ξ Q D A (divIoi r b)) ∘ fun ω => B2.Strong.rescaledField (h ω) b := by
        filter_upwards [hfac r, ae_normalized_dilMetric hD hh b r] with ω h₁ h₂
        rw [h₁, (h₂ A).1]
        rfl
      rw [Measure.map_congr he,
        map_comp_eq_of_map_eq hkt hmeas hlaw (measurable_normAcross hD.1 A _)]
      rfl
  · refine isTwoSidedTight_of_map_eq_index P _ _ hT₂ (fun r => divIoi r b) (fun r => ?_)
      (fun r => ?_)
    · have he : (fun ω => ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
            Real.exp (-((ξ : ℝ) * a r ω))) * aroundDist (dilMetric D Q b (h ω)) (A.dilate r r.2))
          =ᵐ[P] (normAround ξ Q D A (divIoi r b)) ∘ fun ω => B2.Strong.rescaledField (h ω) b := by
        filter_upwards [hfac r, ae_normalized_dilMetric hD hh b r] with ω h₁ h₂
        rw [h₁, (h₂ A).2]
        rfl
      exact ((measurable_normAround hD.1 A _).comp hkt).aemeasurable.congr he.symm
    · have he : (fun ω => ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
            Real.exp (-((ξ : ℝ) * a r ω))) * aroundDist (dilMetric D Q b (h ω)) (A.dilate r r.2))
          =ᵐ[P] (normAround ξ Q D A (divIoi r b)) ∘ fun ω => B2.Strong.rescaledField (h ω) b := by
        filter_upwards [hfac r, ae_normalized_dilMetric hD hh b r] with ω h₁ h₂
        rw [h₁, (h₂ A).2]
        rfl
      rw [Measure.map_congr he,
        map_comp_eq_of_map_eq hkt hmeas hlaw (measurable_normAround hD.1 A _)]
      rfl

 
theorem isWeakLQGMetric_dilMetric (hD : IsWeakLQGMetric ξ Q D) (b : Set.Ioi (0 : ℝ)) :
    IsWeakLQGMetric ξ Q (dilMetric D Q b) :=
  ⟨measurable_dilMetric hD.1 b, length_dilMetric hD b, locality_dilMetric hD b,
    weyl_dilMetric hD b, translation_dilMetric hD b, tightness_dilMetric hD b⟩

end SupercriticalLQGUniqueness.B2.WeakStrong
