import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.ChoicesASV2




 












set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset Filter LQGMetric.MetricGeometry
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 
theorem isCircleAverage_addFun_of_zero_sphere (g : DistC) (f : C(ℂ, ℝ))
    (r : Set.Ioi (0 : ℝ)) (z : ℂ) (a : ℝ)
    (ha : IsCircleAverage g r z a)
    (hf : ∀ x ∈ Metric.sphere z (r : ℝ), f x = 0) :
    IsCircleAverage (LQGMetric.addFun g f) r z a := by
  unfold IsCircleAverage at ha ⊢
  have hseq : ∀ n : ℕ,
      Real.circleAverage
        (fun x => LQGMetric.addFun g f (LQGMetric.bumpTest n x)) z (r : ℝ) =
      Real.circleAverage (fun x => g (LQGMetric.bumpTest n x)) z (r : ℝ) +
      Real.circleAverage
        (fun x => LQGMetric.ofCont f (LQGMetric.bumpTest n x)) z (r : ℝ) := by
    intro n
    rw [LQGMetric.CircleAvg.circleAverage_pairing,
      LQGMetric.CircleAvg.circleAverage_pairing,
      LQGMetric.CircleAvg.circleAverage_pairing]
    simp only [LQGMetric.addFun, add_apply]
  have hfavg : Real.circleAverage f z (r : ℝ) = 0 := by
    rw [Real.circleAverage_congr_sphere (f₂ := fun _ => 0)]
    · simp [Real.circleAverage_def]
    · intro x hx
      have hr : (0 : ℝ) < (r : ℝ) := r.property
      exact hf x (by simpa only [abs_of_pos hr] using hx)
  simp_rw [hseq]
  have := ha.add (LQGMetric.CircleAvg.tendsto_mollAvg_ofCont f r z)
  rwa [hfavg, add_zero] at this

 
theorem weyl_metric_le_exp (Dbase Dw : LSCMetric) (ξ M : ℝ) (hξ : 0 ≤ ξ)
    (F : C(ℂ, ℝ)) (hforget : Continuous (BiLipschitz.Barrier.forget Dbase)) (hL : Dbase.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, Dw p = weylScale ξ F Dbase p) (hF : ∀ x, F x ≤ M) (x y : ℂ) :
    Dw (x, y) ≤ ENNReal.ofReal (Real.exp (ξ * M)) * Dbase (x, y) := by
  set C := ENNReal.ofReal (Real.exp (ξ * M)) with hC
  have hC0 : C ≠ 0 := by simpa [hC] using Real.exp_pos (ξ * M)
  have hCtop : C ≠ ⊤ := ENNReal.ofReal_ne_top
  by_cases htop : Dbase (x, y) = ⊤
  · rw [htop, ENNReal.mul_top hC0]; exact le_top
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  set δ : ℝ := (ε : ℝ) / (C.toReal + 1) with hδ
  have hCt : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hδ0 : 0 < δ := div_pos (by exact_mod_cast hε) (by linarith)
  obtain ⟨P, a, b, hP, hPa, hPb, hlen⟩ := hL x y (lt_top_iff_ne_top.mpr htop) δ hδ0
  have h1 : Dw (x, y) ≤ Dw.len P a b := by
    rw [← hPa, ← hPb]
    exact eVariationOn.edist_le (Dw.pt ∘ P) (left_mem_Icc.mpr hP.1) (right_mem_Icc.mpr hP.1)
  have h2 := weyl_len_le_exp Dbase Dw ξ M hξ F hforget hWeyl hP (fun u _ => hF (P u))
  calc Dw (x, y) ≤ C * Dbase.len P a b := h1.trans h2
    _ ≤ C * (Dbase (x, y) + ENNReal.ofReal δ) := by gcongr
    _ = C * Dbase (x, y) + C * ENNReal.ofReal δ := mul_add _ _ _
    _ ≤ C * Dbase (x, y) + ε := by
        gcongr
        rw [← ENNReal.ofReal_toReal hCtop, ← ENNReal.ofReal_mul hCt, ENNReal.coe_nnreal_eq]
        apply ENNReal.ofReal_le_ofReal
        rw [hδ, mul_div_assoc']
        rw [div_le_iff₀ (by linarith)]
        nlinarith

 

theorem weyl_internal_le_of_zero (Dbase Dw : LSCMetric) (ξ : ℝ) (F : C(ℂ, ℝ))
    (hforget : Continuous (BiLipschitz.Barrier.forget Dbase))
    (hWeyl : ∀ p : ℂ × ℂ, Dw p = weylScale ξ F Dbase p)
    (C : NNReal) (hcomp : ∀ x y : ℂ, Dw (x, y) ≤ (C : ℝ≥0∞) * Dbase (x, y))
    (Y : Set ℂ) (hY : ∀ x ∈ Y, F x = 0) (p : Y × Y) :
    Dw.internal Y p ≤ Dbase.internal Y p := by
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hPY => le_iInf fun h0 => le_iInf fun h1 => ?_
  have hPw : Dw.IsCurve P a b := EndSaving.PathSurgery.isCurve_of_metric_le Dbase Dw C hcomp hP
  have hlen : Dw.len P a b = Dbase.len P a b :=
    EndSaving.PathSurgery.weyl_len_eq_of_zero_trace Dbase Dw ξ F hforget hWeyl hP
      (fun u hu => hY _ (hPY u hu))
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hPw <|
    iInf_le_of_le hPY <| iInf_le_of_le h0 <| iInf_le_of_le h1 hlen.le

 
theorem allPairs_le_upperOptimal (D D' : LSCMetric) (hpos : 0 < OptimalConstants.Ratios.upperOptimal D D')
    (x y : ℂ) : D' (x, y) ≤ OptimalConstants.Ratios.upperOptimal D D' * D (x, y) := by
  by_cases h0 : D (x, y) = 0
  · have hxy : x = y := D.isExtMetric.2.1 x y h0
    subst hxy
    simp only [D.isExtMetric.1, D'.isExtMetric.1, mul_zero, le_refl]
  by_cases ht : D (x, y) = ⊤
  · rw [ht, ENNReal.mul_top hpos.ne']; exact le_top
  have hp : OptimalConstants.Ratios.RatioPair D x y := by
    refine (OptimalConstants.Ratios.ratioPair_iff_finite_positive D x y).mpr ⟨?_, pos_iff_ne_zero.mpr h0,
      lt_top_iff_ne_top.mpr ht⟩
    intro hxy; apply h0; rw [hxy]; exact D.isExtMetric.1 y
  simpa only [mul_comm] using (ENNReal.div_le_iff' h0 ht).1 (OptimalConstants.Ratios.ratio_le_upperOptimal D D' hp)


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
