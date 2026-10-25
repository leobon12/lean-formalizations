import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.WeylToolsV2




 








set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset Filter LQGMetric.MetricGeometry
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

 
theorem weyl_len_eq_weightedLength (Dbase Dw : LSCMetric) (ξ : ℝ) (F : C(ℂ, ℝ))
    (hWeyl : ∀ p : ℂ × ℂ, Dw p = weylScale ξ F Dbase p) (P : ℝ → ℂ) (a b : ℝ) :
    Dw.len P a b = HigherDimLQGMetric.curveLengthWith
      (fun x y : Dbase.Space => weylScale ξ F Dbase (BiLipschitz.Barrier.forget Dbase x, BiLipschitz.Barrier.forget Dbase y))
      (Dbase.pt ∘ P) a b := by
  have hlen : Dw.len P a b =
      HigherDimLQGMetric.curveLengthWith (fun x y : ℂ => Dw (x, y)) P a b := by
    rw [Dw.len_eq_curveLength, ← HigherDimLQGMetric.curveLengthWith_edist]
    rfl
  rw [hlen]
  have heq : (fun x y : ℂ => Dw (x, y)) = (fun x y : ℂ => weylScale ξ F Dbase (x, y)) := by
    funext x y; exact hWeyl (x, y)
  rw [heq]
  rfl

 
theorem weyl_allPairs_transfer (Dh D'h Dsh D'sh : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (F : C(ℂ, ℝ)) (hforget : Continuous (BiLipschitz.Barrier.forget Dh))
    (hforget' : Continuous (BiLipschitz.Barrier.forget D'h))
    (hWeyl : ∀ p : ℂ × ℂ, Dsh p = weylScale ξ F Dh p)
    (hWeyl' : ∀ p : ℂ × ℂ, D'sh p = weylScale ξ F D'h p)
    (hLsh : Dsh.IsLengthSpace) (hFn : ∀ x, 0 ≤ F x)
    (C : NNReal) (hcomp : ∀ x y : ℂ, D'h (x, y) ≤ (C : ℝ≥0∞) * Dh (x, y)) :
    ∀ x y : ℂ, D'sh (x, y) ≤ (C : ℝ≥0∞) * Dsh (x, y) := by
  intro x y
  by_cases hC : C = 0
  · exfalso
    have h01 := hcomp 0 1
    rw [hC, ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at h01
    exact zero_ne_one (D'h.isExtMetric.2.1 0 1 h01)
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC
  by_cases htop : Dsh (x, y) = ⊤
  · rw [htop, ENNReal.mul_top hC0]; exact le_top
  have hDle : ∀ u v : ℂ, Dh (u, v) ≤ ((1 : NNReal) : ℝ≥0∞) * Dsh (u, v) := by
    intro u v
    rw [ENNReal.coe_one, one_mul]
    exact EndSaving.Spent.metric_le_weyl Dh Dsh ξ hξ F hforget hWeyl hFn u v
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  set δ : ℝ := (ε : ℝ) / ((C : ℝ) + 1) with hδ
  have hCr : (0 : ℝ) ≤ C := C.property
  have hδ0 : 0 < δ := div_pos (by exact_mod_cast hε) (by linarith)
  obtain ⟨P, a, b, hP, hPa, hPb, hlen⟩ := hLsh x y (lt_top_iff_ne_top.mpr htop) δ hδ0
  have hPh : Dh.IsCurve P a b := EndSaving.PathSurgery.isCurve_of_metric_le Dsh Dh 1 hDle hP
  have hP'h : D'h.IsCurve P a b := EndSaving.PathSurgery.isCurve_of_metric_le Dh D'h C hcomp hPh
  have h1 : D'sh (x, y) ≤ D'sh.len P a b := by
    rw [← hPa, ← hPb]
    exact eVariationOn.edist_le (D'sh.pt ∘ P) (left_mem_Icc.mpr hP.1) (right_mem_Icc.mpr hP.1)
  have hw' := (weyl_len_eq_weightedLength D'h D'sh ξ F hWeyl' P a b).trans
    (Toolkit.WeylLength.weylCurveLength_eq_weightedLength D'h ξ F hforget' hP'h)
  have hw := (weyl_len_eq_weightedLength Dh Dsh ξ F hWeyl P a b).trans
    (Toolkit.WeylLength.weylCurveLength_eq_weightedLength Dh ξ F hforget hPh)
  have hcmp : D'sh.len P a b ≤ (C : ℝ≥0∞) * Dsh.len P a b := by
    rw [hw', hw]
    unfold HigherDimLQGMetric.weightedLength
    rw [← HigherDimLQGMetric.partitionSup_const_mul]
    apply HigherDimLQGMetric.partitionSup_mono
    intro u v _ _ _
    have hcl : curveLength (D'h.pt ∘ P) u v ≤ (C : ℝ≥0∞) * curveLength (Dh.pt ∘ P) u v := by
      have := EndSaving.PathSurgery.curve_length_le_of_metric_le Dh D'h C hcomp P u v
      rwa [D'h.len_eq_curveLength, Dh.len_eq_curveLength] at this
    calc HigherDimLQGMetric.infAlong _ (D'h.pt ∘ P) u v * curveLength (D'h.pt ∘ P) u v
        ≤ HigherDimLQGMetric.infAlong _ (D'h.pt ∘ P) u v *
            ((C : ℝ≥0∞) * curveLength (Dh.pt ∘ P) u v) := by gcongr
      _ = (C : ℝ≥0∞) * (HigherDimLQGMetric.infAlong _ (Dh.pt ∘ P) u v *
            curveLength (Dh.pt ∘ P) u v) := by
          rw [mul_left_comm]
          rfl
  calc D'sh (x, y) ≤ (C : ℝ≥0∞) * Dsh.len P a b := h1.trans hcmp
    _ ≤ (C : ℝ≥0∞) * (Dsh (x, y) + ENNReal.ofReal δ) := by gcongr
    _ = (C : ℝ≥0∞) * Dsh (x, y) + (C : ℝ≥0∞) * ENNReal.ofReal δ := mul_add _ _ _
    _ ≤ (C : ℝ≥0∞) * Dsh (x, y) + ε := by
        gcongr
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hCr, ENNReal.coe_nnreal_eq]
        apply ENNReal.ofReal_le_ofReal
        rw [hδ, mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
