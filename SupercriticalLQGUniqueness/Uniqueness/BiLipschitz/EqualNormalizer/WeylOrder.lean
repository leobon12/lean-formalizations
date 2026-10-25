import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.WeylSigma




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
open LQGMetric.MetricGeometry

theorem weyl_cost_le_of_pointwise
    (ξ : ℝ) (f : C(ℂ, ℝ)) (D E : LSCMetric) (C : ℝ)
    (hC : 0 < C)
    (h : ∀ p : ℂ × ℂ, E p ≤ ENNReal.ofReal C * D p)
    (P : ℝ → ℂ) (L : ℝ)
    (hc : D.IsCurve P 0 L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) :
    ∃ (Q : ℝ → ℂ) (M : ℝ), E.IsCurve Q 0 M ∧
      HasUnitSpeedOn (E.pt ∘ Q) (Icc 0 M) ∧
      Q 0 = P 0 ∧ Q M = P L ∧
      (∫⁻ t in Icc 0 M, ENNReal.ofReal (Real.exp (ξ * f (Q t)))) ≤
        ENNReal.ofReal C *
          (∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))) := by
  have hL : 0 ≤ L := hc.1
  have hEcurve : E.IsCurve P 0 L :=
    isCurve_of_pointwise_le D E C hC.le h P 0 L hc
  have hDlen : D.len P 0 L = ENNReal.ofReal L := by
    exact hasUnitSpeedOn_Icc_iff.mp hu 0 L le_rfl hL le_rfl |>.trans (by simp)
  have hEfin : E.len P 0 L ≠ ∞ := by
    have hb := len_le_mul_of_pointwise D E C hC.le h P 0 L
    rw [hDlen] at hb
    exact ne_top_of_le_ne_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ENNReal.ofReal_lt_top).ne hb
  let M := (E.len P 0 L).toReal
  let σ := variationOnFromTo (E.pt ∘ P) (Icc 0 L) 0
  let Q : ℝ → ℂ := lengthParam (X := E.Space) (E.pt ∘ P) 0 L
  have himage : σ '' Icc 0 L = Icc 0 M :=
    variationOnFromTo_image_Icc hL hEcurve.2 hEfin
  have hunit : HasUnitSpeedOn (E.pt ∘ Q) (Icc 0 M) := by
    change HasUnitSpeedOn (lengthParam (E.pt ∘ P) 0 L) (Icc 0 M)
    exact hasUnitSpeedOn_lengthParam hL hEcurve.2 hEfin
  have hQσ : ∀ t ∈ Icc 0 L, Q (σ t) = P t := by
    intro t ht
    exact lengthParam_variationOnFromTo hEfin ht
  have hσ0 : σ 0 = 0 := variationOnFromTo.self _ _ _
  have hσL : σ L = M := by
    dsimp [σ, M]
    rw [variationOnFromTo.eq_of_le _ _ hL, Set.inter_self]
    rfl
  have hQ0 : Q 0 = P 0 := by
    simpa only [hσ0] using hQσ 0 ⟨le_rfl, hL⟩
  have hQM : Q M = P L := by
    rw [← hσL]
    exact hQσ L ⟨hL, le_rfl⟩
  have hQcurve : E.IsCurve Q 0 M := by
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have hcont := continuousOn_of_hasUnitSpeedOn hunit
    dsimp [LSCMetric.pt, Function.comp, id] at hcont ⊢
    exact hcont
  let K : ℝ≥0 := ⟨C, hC.le⟩
  have hσlip : LipschitzOnWith K σ (Icc 0 L) :=
    subordinate_length_clock_lipschitz D E C hC.le h P L hL hu
  have hcost := lintegral_image_le_mul (Icc 0 L) (Icc 0 M)
    measurableSet_Icc measurableSet_Icc σ K hσlip himage
    (fun t => ENNReal.ofReal (Real.exp (ξ * f (Q t))))
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal C := by
    rw [ENNReal.ofReal_eq_coe_nnreal hC.le]
    congr 1
  rw [hK] at hcost
  refine ⟨Q, M, hQcurve, hunit, hQ0, hQM, ?_⟩
  convert hcost using 1
  congr 1
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  simpa only using congrArg (fun z : ℂ => ENNReal.ofReal (Real.exp (ξ * f z)))
    (hQσ t ht).symm


 
theorem weylScale_le_mul_of_pointwise
    (ξ : ℝ) (f : C(ℂ, ℝ)) (D E : LSCMetric) (C : ℝ)
    (hC : 0 < C)
    (h : ∀ p : ℂ × ℂ, E p ≤ ENNReal.ofReal C * D p) :
    ∀ p : ℂ × ℂ,
      weylScale ξ f E p ≤ ENNReal.ofReal C * weylScale ξ f D p := by
  intro p
  unfold weylScale
  have hcoef0 : ENNReal.ofReal C ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hC)
  have hcoefTop : ENNReal.ofReal C ≠ ∞ := ENNReal.ofReal_ne_top
  simp only [ENNReal.mul_iInf_of_ne hcoef0 hcoefTop]
  refine le_iInf fun P => le_iInf fun L => le_iInf fun hc =>
    le_iInf fun hu => le_iInf fun h0 => le_iInf fun h1 => ?_
  obtain ⟨Q, M, hQc, hQu, hQ0, hQM, hcost⟩ :=
    weyl_cost_le_of_pointwise ξ f D E C hC h P L hc hu
  have hQ0' : Q 0 = p.1 := hQ0.trans h0
  have hQM' : Q M = p.2 := hQM.trans h1
  apply le_trans _ hcost
  apply iInf_le_of_le Q
  apply iInf_le_of_le M
  apply iInf_le_of_le hQc
  apply iInf_le_of_le hQu
  apply iInf_le_of_le hQ0'
  exact iInf_le _ hQM'

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
