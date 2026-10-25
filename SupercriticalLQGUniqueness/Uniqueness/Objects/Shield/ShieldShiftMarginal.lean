import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldDeterministic
import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldK0




 






set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

theorem exists_shield_shift_half
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants) :
    ∃ C₁ K₀ : ℝ, 1 ≤ C₁ ∧ 0 ≤ K₀ ∧
      Real.exp ((ξ : ℝ) * -K₀) * C₁ ^ 2 ≤ C.lamConst ∧
      ∀ (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF
          (id : LQGMetric.DistC → LQGMetric.DistC) μ →
        ∀ (t : ℝ) (_ht : 0 < t),
          ENNReal.ofReal (1 / 2 : ℝ) ≤
            μ {g | Objects.Excursions.shieldAt C
              (D (LQGMetric.addFun g
                (LQGMetric.testCont (shieldBumpAt K₀ t 0)))) t} := by
  obtain ⟨M₁, hM₁, hV₁⟩ :=
    TwoScale.RatioMarginal.center_ratio_uniform ξ Q D hD Objects.ProbabilityS7S9.shapeSupInner (3 / 4)
      (by norm_num) (by norm_num)
  obtain ⟨M₂, hM₂, hV₂⟩ :=
    TwoScale.RatioMarginal.center_ratio_uniform ξ Q D hD shieldOuterShape (3 / 4)
      (by norm_num) (by norm_num)
  let C₁ : ℝ := max M₁ M₂
  have hC₁ : 1 ≤ C₁ := hM₁.trans (le_max_left _ _)
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le (by norm_num) hC₁
  let K₀ : ℝ := shieldK0 ξ C₁ C.lamConst
  have hK₀ : 0 ≤ K₀ := shieldK0_nonneg ξ.2
  have hbudget := shieldK0_budget ξ.2 hC₁pos C.lamPos
  refine ⟨C₁, K₀, hC₁, hK₀, hbudget, ?_⟩
  intro μ _ hμ t ht
  let r : Ioi (0 : ℝ) := ⟨t, ht⟩
  let φ : LQGMetric.TestC := shieldBumpAt K₀ t 0
  let f : C(ℂ, ℝ) := LQGMetric.testCont φ
  have hGFF : LQGMetric.IsGFFPlusCont
      (id : LQGMetric.DistC → LQGMetric.DistC) μ :=
    LQGMetric.GM.detGFFPlusCont hμ.1
  let G₁ : Set LQGMetric.DistC :=
    {g | ENNReal.ofReal M₁⁻¹ ≤ TwoScale.RatioMarginal.normAcrossAt ξ Q D g Objects.ProbabilityS7S9.shapeSupInner 0 r ∧
      TwoScale.RatioMarginal.normAroundAt ξ Q D g Objects.ProbabilityS7S9.shapeSupInner 0 r ≤ ENNReal.ofReal M₁}
  let G₂ : Set LQGMetric.DistC :=
    {g | ENNReal.ofReal M₂⁻¹ ≤ TwoScale.RatioMarginal.normAcrossAt ξ Q D g shieldOuterShape 0 r ∧
      TwoScale.RatioMarginal.normAroundAt ξ Q D g shieldOuterShape 0 r ≤ ENNReal.ofReal M₂}
  have hG₁ : ENNReal.ofReal (3 / 4 : ℝ) ≤ μ G₁ := hV₁ μ id hμ 0 r
  have hG₂ : ENNReal.ofReal (3 / 4 : ℝ) ≤ μ G₂ := hV₂ μ id hμ 0 r
  have hG₁m : MeasurableSet G₁ :=
    (measurableSet_le measurable_const
      ((Objects.ProbabilityS7S9.measurable_normAcrossAt' ξ Q hD.measurable Objects.ProbabilityS7S9.shapeSupInner 0 r))).inter
      (measurableSet_le
        (Objects.ProbabilityS7S9.measurable_normAroundAt' ξ Q hD.measurable Objects.ProbabilityS7S9.shapeSupInner 0 r)
        measurable_const)
  have hG₂m : MeasurableSet G₂ :=
    (measurableSet_le measurable_const
      ((Objects.ProbabilityS7S9.measurable_normAcrossAt' ξ Q hD.measurable shieldOuterShape 0 r))).inter
      (measurableSet_le
        (Objects.ProbabilityS7S9.measurable_normAroundAt' ξ Q hD.measurable shieldOuterShape 0 r)
        measurable_const)
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hshift : ∀ᵐ g ∂μ, g ∈ G₁ ∩ G₂ →
      Objects.Excursions.shieldAt C (D (LQGMetric.addFun g f)) t := by
    filter_upwards [hD.weyl μ id hGFF,
      BiLipschitz.Barrier.ae_curves_continuous hD hQ μ id hμ,
      BiLipschitz.Barrier.ae_barrier hD hQ μ id hμ,
      hD.length μ id hGFF] with g hw hc hbar hlen hg
    have he : ∀ x y : ℂ, D (LQGMetric.addFun g f) (x, y) =
        weylScale ξ f (D g) (x, y) := fun x y =>
      (congrFun (hw f) (x, y)).symm
    let n : ℝ≥0∞ := ENNReal.ofReal
      ((t : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg g t 0)))
    have hn0 : n ≠ 0 :=
      (ENNReal.ofReal_pos.mpr
        (mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _))).ne'
    have hM₁pos : 0 < M₁ := lt_of_lt_of_le (by norm_num) hM₁
    have hM₂pos : 0 < M₂ := lt_of_lt_of_le (by norm_num) hM₂
    have hinner : n * Objects.CorrectedEvent.around (D g) 0 ((21 / 20) * t) ((39 / 20) * t) ≤
        ENNReal.ofReal C₁ := by
      have h1 := hg.1.2
      unfold TwoScale.RatioMarginal.normAroundAt at h1
      rw [Objects.ProbabilityS7S9.supInner_eq r 0] at h1
      rw [shieldInnerShape_at r 0] at h1
      rw [← Objects.ProbabilityS7S9.around_eq_aroundDist (D g) 0 ((21 / 20) * t)
        ((39 / 20) * t) (by positivity) (by nlinarith)] at h1
      exact h1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have houter : (ENNReal.ofReal C₁)⁻¹ ≤
        n * Objects.CorrectedEvent.acr (D g) 0 (2 * t) (3 * t) := by
      have h2 := hg.2.1
      unfold TwoScale.RatioMarginal.normAcrossAt at h2
      rw [shieldOuterShape_at r 0] at h2
      have hAcr := Objects.ProbabilityS3.acr_eq_ambientAcross_of_barrier (D g) hbar hlen
        0 (2 * t) (3 * t) (by linarith) (by linarith)
      have h2' : ENNReal.ofReal M₂⁻¹ ≤
          n * Objects.CorrectedEvent.acr (D g) 0 (2 * t) (3 * t) := by
        change ENNReal.ofReal M₂⁻¹ ≤
          n * Objects.CorrectedEvent.ambientAcross (D g) 0 (2 * t) (3 * t) at h2
        rwa [hAcr]
      have hInv : (ENNReal.ofReal C₁)⁻¹ ≤ ENNReal.ofReal M₂⁻¹ := by
        have hr : C₁⁻¹ ≤ M₂⁻¹ :=
          (inv_le_inv₀ hC₁pos hM₂pos).2 (le_max_right _ _)
        simpa only [ENNReal.ofReal_inv_of_pos hC₁pos] using
          ENNReal.ofReal_le_ofReal hr
      exact hInv.trans h2'
    have hreal : Real.exp ((ξ : ℝ) * -K₀) * C₁ ≤ C.lamConst * C₁⁻¹ := by
      apply (le_div_iff₀ hC₁pos).2
      nlinarith only [hbudget]
    have hbud : ENNReal.ofReal (Real.exp ((ξ : ℝ) * -K₀)) *
        ENNReal.ofReal C₁ ≤ ENNReal.ofReal C.lamConst * (ENNReal.ofReal C₁)⁻¹ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_inv_of_pos hC₁pos,
        ← ENNReal.ofReal_mul C.lamPos.le]
      exact ENNReal.ofReal_le_ofReal hreal
    exact shieldAt_of_weyl_shift ξ C (D g) (D (LQGMetric.addFun g f))
      0 t ht K₀ he hc.2.1 hbar hlen n hn0 ENNReal.ofReal_ne_top
      (ENNReal.ofReal C₁) ENNReal.ofReal_ne_top hbud hinner houter
  have hcomp : ∀ {S : Set LQGMetric.DistC}, MeasurableSet S →
      ENNReal.ofReal (3 / 4 : ℝ) ≤ μ S → μ Sᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
    intro S hS hp
    rw [prob_compl_eq_one_sub hS]
    calc
      1 - μ S ≤ 1 - ENNReal.ofReal (3 / 4 : ℝ) := tsub_le_tsub_left hp 1
      _ = ENNReal.ofReal (1 / 4 : ℝ) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
        norm_num
  have hGc : μ (G₁ ∩ G₂)ᶜ ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [compl_inter]
    calc
      μ (G₁ᶜ ∪ G₂ᶜ) ≤ μ G₁ᶜ + μ G₂ᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) :=
        add_le_add (hcomp hG₁m hG₁) (hcomp hG₂m hG₂)
      _ = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
  have hG : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ (G₁ ∩ G₂) := by
    have hsum := measure_add_measure_compl (μ := μ) (hG₁m.inter hG₂m)
    rw [measure_univ] at hsum
    have hP : μ (G₁ ∩ G₂) = 1 - μ (G₁ ∩ G₂)ᶜ :=
      ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) hsum
    rw [hP]
    calc
      ENNReal.ofReal (1 / 2 : ℝ) = 1 - ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
        norm_num
      _ ≤ 1 - μ (G₁ ∩ G₂)ᶜ := tsub_le_tsub_left hGc 1
  exact hG.trans (measure_mono_ae (by
    filter_upwards [hshift] with g hg hgood
    exact hg hgood))

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
