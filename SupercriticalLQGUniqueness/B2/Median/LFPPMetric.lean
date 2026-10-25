import SupercriticalLQGUniqueness.B2.Median.Crossing

 






set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal
open LQGMetric (IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness.B2.Median

private theorem lfppDistance_isExtMetric (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    IsExtMetric (lfppDistance ξ φ) := by
  constructor
  · intro x
    rw [B2.LscTop.lfppDistance_eq_lfppD]
    exact LQGMetric.LFPP.lfppDOn_self convex_univ (mem_univ x)
  constructor
  · intro x y h
    have h' : LQGMetric.LFPP.lfppD ξ φ x y = 0 := by
      simpa only [B2.LscTop.lfppDistance_eq_lfppD] using h
    exact LQGMetric.LFPP.lfppDReal_eq_zero (ξ := ξ) φ.continuous
      (by simp only [LQGMetric.LFPP.lfppDReal, h', ENNReal.toReal_zero])
  constructor
  · intro x y
    simp only [B2.LscTop.lfppDistance_eq_lfppD]
    exact LQGMetric.LFPP.lfppDOn_comm x y
  · intro x y z
    simp only [B2.LscTop.lfppDistance_eq_lfppD]
    exact LQGMetric.LFPP.lfppDOn_triangle x y z

def lfppMetricRaw (ξ : ℝ) (φ : C(ℂ, ℝ)) : LSCMetric :=
  ⟨lfppDistance ξ φ, lfppDistance_isExtMetric ξ φ,
    (B2.LscTop.continuous_lfppDistance ξ φ).lowerSemicontinuous⟩

@[simp] theorem lfppMetricRaw_apply (ξ : ℝ) (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    lfppMetricRaw ξ φ p = lfppDistance ξ φ p := rfl

private theorem scaled_lfppDistance_isExtMetric
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) :
    IsExtMetric (fun p => ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDistance ξ φ p) := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((a : ℝ)⁻¹)
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr a.property)).ne'
  have hM := lfppDistance_isExtMetric ξ φ
  constructor
  · intro x
    simp only [hM.1, mul_zero]
  constructor
  · intro x y h
    have hxy : lfppDistance ξ φ (x, y) = 0 :=
      (mul_eq_zero.mp h).resolve_left hc0
    exact hM.2.1 x y hxy
  constructor
  · intro x y
    change c * lfppDistance ξ φ (x, y) = c * lfppDistance ξ φ (y, x)
    rw [hM.2.2.1 x y]
  · intro x y z
    calc
      c * lfppDistance ξ φ (x, z)
          ≤ c * (lfppDistance ξ φ (x, y) + lfppDistance ξ φ (y, z)) :=
        mul_le_mul_of_nonneg_left (hM.2.2.2 x y z) zero_le
      _ = c * lfppDistance ξ φ (x, y) +
            c * lfppDistance ξ φ (y, z) := mul_add _ _ _

def lfppMetric (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) : LSCMetric :=
  ⟨fun p => ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDistance ξ φ p,
    scaled_lfppDistance_isExtMetric ξ a φ,
    ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      (B2.LscTop.continuous_lfppDistance ξ φ)).lowerSemicontinuous⟩

@[simp] theorem lfppMetric_apply (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    lfppMetric ξ a φ p = ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDistance ξ φ p := rfl

theorem lfppMetric_toLSCFun (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) :
    (lfppMetric ξ a φ).toLSCFun.1 = rescaledLFPP ξ a φ := rfl

theorem lfppMetric_isCurve (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) {P : ℝ → ℂ} {z w : ℂ}
    (hP : IsPiecewiseC1Path P z w) :
    (lfppMetric ξ a φ).IsCurve P 0 1 := by
  refine ⟨zero_le_one, ?_⟩
  intro t ht
  apply tendsto_iff_edist_tendsto_0.mpr
  change Tendsto (fun s => lfppMetric ξ a φ (P s, P t))
    (𝓝[Icc (0 : ℝ) 1] t) (𝓝 0)
  have hPt : Tendsto P (𝓝[Icc (0 : ℝ) 1] t) (𝓝 (P t)) :=
    hP.continuousOn t ht
  have hpair : Tendsto (fun s => (P s, P t))
      (𝓝[Icc (0 : ℝ) 1] t) (𝓝 (P t, P t)) :=
    hPt.prodMk_nhds tendsto_const_nhds
  have hc : Continuous (fun p => lfppMetric ξ a φ p) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      (B2.LscTop.continuous_lfppDistance ξ φ)
  have hdist := hc.continuousAt.tendsto.comp hpair
  have hself : lfppMetric ξ a φ (P t, P t) = 0 :=
    (lfppMetric ξ a φ).isExtMetric.1 (P t)
  change Tendsto (fun s => lfppMetric ξ a φ (P s, P t))
    (𝓝[Icc (0 : ℝ) 1] t) (𝓝 (lfppMetric ξ a φ (P t, P t))) at hdist
  simpa only [hself] using hdist

theorem lfppMetric_len_le_lfppLen (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) {P : ℝ → ℂ} {z w : ℂ}
    (hP : IsPiecewiseC1Path P z w) :
    (lfppMetric ξ a φ).len P 0 1 ≤
      ENNReal.ofReal ((a : ℝ)⁻¹) * lfppLen ξ φ P := by
  let M := LQGMetric.LFPP.lfppContMetric ξ φ φ.continuous
  let c : ℝ≥0∞ := ENNReal.ofReal ((a : ℝ)⁻¹)
  have hlen : (lfppMetric ξ a φ).len P 0 1 = c * M.len P 0 1 := by
    unfold LSCMetric.len LQGMetric.ContMetric.len LQGMetric.MetricGeometry.curveLength
    exact LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
      (F := (lfppMetric ξ a φ).pt ∘ P) (G := M.pt ∘ P) (c := c)
      (fun s t => by
        change lfppMetric ξ a φ (P s, P t) =
          c * edist (M.pt (P s)) (M.pt (P t))
        rw [LQGMetric.LFPP.edist_lfppContMetric]
        rw [lfppMetric_apply, B2.LscTop.lfppDistance_eq_lfppD]) (Icc 0 1)
  rw [hlen]
  exact mul_le_mul_of_nonneg_left
    (LQGMetric.LFPP.len_le_lfppLen φ.continuous hP le_rfl le_rfl) zero_le

theorem crossingInf_lfppMetric_le (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) :
    crossingInf (lfppMetric ξ a φ) ≤
      ENNReal.ofReal ((a : ℝ)⁻¹) * lfppCrossingLength ξ φ := by
  simp only [lfppCrossingLength, ENNReal.mul_iInf_of_ne
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr a.property)).ne'
    ENNReal.ofReal_ne_top]
  refine le_iInf fun P => le_iInf fun hP => ?_
  have hc : (lfppMetric ξ a φ).IsCurve P 0 1 :=
    lfppMetric_isCurve ξ a φ hP.1
  calc
    crossingInf (lfppMetric ξ a φ)
        ≤ (lfppMetric ξ a φ).len P 0 1 :=
      compactPathInf_le_of_curve _ unitSquare leftSide rightSide P 0 1 hc
        hP.2.2.2 hP.2.1 hP.2.2.1
    _ ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * crossingLFPP ξ φ P hP :=
      lfppMetric_len_le_lfppLen ξ a φ hP.1

end SupercriticalLQGUniqueness.B2.Median
