import SLUMetricAPI2
import HigherDimLQGMetric.Metric.Reparam




 





set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylLength

private def forget (D : LSCMetric) : D.Space → ℂ := id

private def weight (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ)) : D.Space → ℝ :=
  fun x => Real.exp (ξ * f (forget D x))

private theorem weight_continuous (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (forget D)) :
    Continuous (weight D ξ f) := by
  exact Real.continuous_exp.comp
    (continuous_const.mul (f.continuous.comp hforget))

private theorem weight_pos (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ)) (x : D.Space) :
    0 < weight D ξ f x := Real.exp_pos _

 

theorem weylScale_eq_weylDistOn (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (forget D)) (x y : ℂ) :
    weylScale ξ f D (x, y) =
      HigherDimLQGMetric.weylDistOn (weight D ξ f) Set.univ (D.pt x) (D.pt y) := by
  let w : D.Space → ℝ := weight D ξ f
  have hw : ContinuousOn w (Set.univ : Set D.Space) :=
    (weight_continuous D ξ f hforget).continuousOn
  have hp : ∀ z ∈ (Set.univ : Set D.Space), 0 < w z :=
    fun z _ => weight_pos D ξ f z
  have hrep := HigherDimLQGMetric.weylDistOn_eq_iInf_unitSpeed hw hp (D.pt x) (D.pt y)
  apply le_antisymm
  · rw [hrep]
    refine le_iInf fun L => le_iInf fun P => le_iInf fun hL => le_iInf fun hc =>
      le_iInf fun hu => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun _ => ?_
    exact iInf_le_of_le P <| iInf_le_of_le L <|
      iInf_le_of_le (show D.IsCurve P 0 L from ⟨hL, hc⟩) <|
      iInf_le_of_le hu <| iInf_le_of_le h0 <| iInf_le_of_le h1 le_rfl
  · unfold weylScale
    refine le_iInf fun P => le_iInf fun L => le_iInf fun hc => le_iInf fun hu =>
      le_iInf fun h0 => le_iInf fun h1 => ?_
    rw [hrep]
    exact iInf_le_of_le L <| iInf_le_of_le P <| iInf_le_of_le hc.1 <|
      iInf_le_of_le hc.2 <| iInf_le_of_le hu <| iInf_le_of_le h0 <|
      iInf_le_of_le h1 <| iInf_le_of_le (fun _ _ => Set.mem_univ _) le_rfl


 

theorem weylCurveLength_eq_weightedLength (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (forget D)) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) :
    HigherDimLQGMetric.curveLengthWith
      (fun x y : D.Space => weylScale ξ f D (forget D x, forget D y))
      (D.pt ∘ P) a b =
    HigherDimLQGMetric.weightedLength (weight D ξ f) (D.pt ∘ P) a b := by
  have heq : (fun x y : D.Space => weylScale ξ f D (forget D x, forget D y)) =
      HigherDimLQGMetric.weylDistOn (weight D ξ f) Set.univ := by
    funext x y
    exact weylScale_eq_weylDistOn D ξ f hforget (forget D x) (forget D y)
  rw [heq]
  exact HigherDimLQGMetric.curveLengthWith_weylDistOn isOpen_univ
    (weight_continuous D ξ f hforget).continuousOn hP.2
    (fun _ _ => Set.mem_univ _)

 
theorem weylCurveLength_eq_arclength (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (forget D)) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hfinite : D.len P a b ≠ ⊤) :
    HigherDimLQGMetric.curveLengthWith
      (fun x y : D.Space => weylScale ξ f D (forget D x, forget D y))
      (D.pt ∘ P) a b =
    ∫⁻ t in Icc 0 (D.len P a b).toReal,
      ENNReal.ofReal (Real.exp
        (ξ * f (forget D (LQGMetric.MetricGeometry.lengthParam (D.pt ∘ P) a b t)))) := by
  rw [weylCurveLength_eq_weightedLength D ξ f hforget hP]
  change LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) a b ≠ ⊤ at hfinite
  rw [HigherDimLQGMetric.weightedLength_eq_lengthParam hP.1 hP.2 hfinite]
  obtain ⟨hu, hc, _, _, _⟩ :=
    HigherDimLQGMetric.lengthParam_props hP.1 hP.2 hfinite
      (S := Set.univ) (fun _ _ => Set.mem_univ _)
  exact HigherDimLQGMetric.weightedLength_of_hasUnitSpeedOn
    ENNReal.toReal_nonneg hu
    ((weight_continuous D ξ f hforget).continuousOn.comp hc
      (fun _ _ => Set.mem_univ _))

 
theorem weylCurveLength_eq_top_of_len_eq_top (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (forget D)) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hInfinite : D.len P a b = ⊤) :
    HigherDimLQGMetric.curveLengthWith
      (fun x y : D.Space => weylScale ξ f D (forget D x, forget D y))
      (D.pt ∘ P) a b = ⊤ := by
  rw [weylCurveLength_eq_weightedLength D ξ f hforget hP]
  obtain ⟨m, M, hm, hbound⟩ :=
    HigherDimLQGMetric.exists_bounds_along
      (weight_continuous D ξ f hforget).continuousOn
      (fun x _ => weight_pos D ξ f x) hP.1 hP.2
      (fun _ _ => Set.mem_univ _)
  change LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) a b = ⊤ at hInfinite
  exact HigherDimLQGMetric.weightedLength_eq_top hm hP.1
    (fun s hs => (hbound s hs).1) hInfinite


 
theorem weylCurveLength_factor_bounds (D : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (hforget : Continuous (forget D))
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (m M : ℝ) (hlo : ∀ s ∈ Icc a b, m ≤ f (P s))
    (hhi : ∀ s ∈ Icc a b, f (P s) ≤ M) :
    ENNReal.ofReal (Real.exp (ξ * m)) * D.len P a b ≤
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ f D (forget D x, forget D y))
        (D.pt ∘ P) a b ∧
    HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ f D (forget D x, forget D y))
        (D.pt ∘ P) a b ≤
      ENNReal.ofReal (Real.exp (ξ * M)) * D.len P a b := by
  rw [weylCurveLength_eq_weightedLength D ξ f hforget hP]
  constructor
  · exact HigherDimLQGMetric.ofReal_mul_curveLength_le_weightedLength hP.1
      (fun s hs => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hlo s hs) hξ))
  · exact HigherDimLQGMetric.weightedLength_le_ofReal_mul_curveLength
      (fun s hs => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hhi s hs) hξ))

 
theorem weylCurveLength_trace_extrema (D : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (hforget : Continuous (forget D))
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) :
    ∃ smin ∈ Icc a b, ∃ smax ∈ Icc a b,
      (∀ s ∈ Icc a b, f (P smin) ≤ f (P s) ∧ f (P s) ≤ f (P smax)) ∧
      ENNReal.ofReal (Real.exp (ξ * f (P smin))) * D.len P a b ≤
        HigherDimLQGMetric.curveLengthWith
          (fun x y : D.Space => weylScale ξ f D (forget D x, forget D y))
          (D.pt ∘ P) a b ∧
      HigherDimLQGMetric.curveLengthWith
          (fun x y : D.Space => weylScale ξ f D (forget D x, forget D y))
          (D.pt ∘ P) a b ≤
        ENNReal.ofReal (Real.exp (ξ * f (P smax))) * D.len P a b := by
  have hfc : ContinuousOn (fun s => f (P s)) (Icc a b) := by
    exact (f.continuous.comp hforget).continuousOn.comp hP.2
      (fun _ _ => Set.mem_univ _)
  obtain ⟨smin, hsmin, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hP.1) hfc
  obtain ⟨smax, hsmax, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hP.1) hfc
  refine ⟨smin, hsmin, smax, hsmax, ?_, ?_⟩
  · intro s hs
    exact ⟨hmin hs, hmax hs⟩
  · exact weylCurveLength_factor_bounds D ξ hξ f hforget hP
      (f (P smin)) (f (P smax)) (fun s hs => hmin hs)
      (fun s hs => hmax hs)

 
theorem weylCurveLength_eq_of_zero_on_trace (D : LSCMetric) (ξ : ℝ)
    (f : C(ℂ, ℝ)) (hforget : Continuous (forget D))
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (hf : ∀ s ∈ Icc a b, f (P s) = 0) :
    HigherDimLQGMetric.curveLengthWith
      (fun x y : D.Space => weylScale ξ f D (forget D x, forget D y))
      (D.pt ∘ P) a b = D.len P a b := by
  rw [weylCurveLength_eq_weightedLength D ξ f hforget hP]
  have hw : ∀ s ∈ Icc a b, weight D ξ f ((D.pt ∘ P) s) = 1 := by
    intro s hs
    change Real.exp (ξ * f (P s)) = 1
    rw [hf s hs, mul_zero, Real.exp_zero]
  have hlo := HigherDimLQGMetric.ofReal_mul_curveLength_le_weightedLength
    (w := weight D ξ f) (P := D.pt ∘ P) hP.1
    (fun s hs => (hw s hs).ge)
  have hhi := HigherDimLQGMetric.weightedLength_le_ofReal_mul_curveLength
    (fun s hs => (hw s hs).le)
  have heq := le_antisymm hhi hlo
  simpa only [ENNReal.ofReal_one, one_mul, D.len_eq_curveLength] using heq

 
theorem len_le_weylCurveLength_of_nonneg (D : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (hforget : Continuous (forget D))
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (hf : ∀ s ∈ Icc a b, 0 ≤ f (P s)) :
    D.len P a b ≤
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ f D (forget D x, forget D y))
        (D.pt ∘ P) a b := by
  rw [weylCurveLength_eq_weightedLength D ξ f hforget hP]
  have hlo := HigherDimLQGMetric.ofReal_mul_curveLength_le_weightedLength
    (w := weight D ξ f) (P := D.pt ∘ P) hP.1
    (fun s hs => by
      change (1 : ℝ) ≤ Real.exp (ξ * f (P s))
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hξ (hf s hs)))
  simpa only [ENNReal.ofReal_one, one_mul, D.len_eq_curveLength] using hlo


 
theorem weylScale_isExtMetric (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (forget D)) :
    IsExtMetric (fun p : ℂ × ℂ => weylScale ξ f D p) := by
  let w : D.Space → ℝ := weight D ξ f
  have hw : Continuous w := weight_continuous D ξ f hforget
  have hp : ∀ z : D.Space, 0 < w z := weight_pos D ξ f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    change weylScale ξ f D (x, x) = 0
    rw [weylScale_eq_weylDistOn D ξ f hforget]
    exact HigherDimLQGMetric.weylDistOn_self (Set.mem_univ _)
  · intro x y hxy
    change weylScale ξ f D (x, y) = 0 at hxy
    rw [weylScale_eq_weylDistOn D ξ f hforget] at hxy
    have hz := HigherDimLQGMetric.edist_eq_zero_of_weylDistOn_eq_zero
      (U := Set.univ) hw.continuousAt (hp (D.pt x)) hxy
    exact D.isExtMetric.2.1 x y hz
  · intro x y
    change weylScale ξ f D (x, y) = weylScale ξ f D (y, x)
    rw [weylScale_eq_weylDistOn D ξ f hforget,
      weylScale_eq_weylDistOn D ξ f hforget]
    exact HigherDimLQGMetric.weylDistOn_comm (D.pt x) (D.pt y)
  · intro x y z
    change weylScale ξ f D (x, z) ≤
      weylScale ξ f D (x, y) + weylScale ξ f D (y, z)
    rw [weylScale_eq_weylDistOn D ξ f hforget,
      weylScale_eq_weylDistOn D ξ f hforget,
      weylScale_eq_weylDistOn D ξ f hforget]
    exact HigherDimLQGMetric.weylDistOn_triangle (D.pt x) (D.pt y) (D.pt z)

 
theorem weylScale_internalWith_univ (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (forget D)) (x y : D.Space) :
    HigherDimLQGMetric.internalWith
      (fun u v : D.Space => weylScale ξ f D (forget D u, forget D v))
      Set.univ x y =
    weylScale ξ f D (forget D x, forget D y) := by
  have heq : (fun u v : D.Space => weylScale ξ f D (forget D u, forget D v)) =
      HigherDimLQGMetric.weylDistOn (weight D ξ f) Set.univ := by
    funext u v
    exact weylScale_eq_weylDistOn D ξ f hforget (forget D u) (forget D v)
  rw [heq, weylScale_eq_weylDistOn D ξ f hforget]
  exact HigherDimLQGMetric.weylDistOn_isLength isOpen_univ
    (weight_continuous D ξ f hforget).continuousOn x y


end SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylLength
