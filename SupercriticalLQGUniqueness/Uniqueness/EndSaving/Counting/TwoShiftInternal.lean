import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.OffBumpInternal




 
set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting

private def euclidForget' (D : LSCMetric) : D.Space → ℂ := id

private theorem shifted_len_eq_weighted (D E : LSCMetric) (ξ : ℝ)
    (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget' D))
    (hWeyl : ∀ p : ℂ × ℂ, E p = weylScale ξ f D p)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) :
    E.len P a b = HigherDimLQGMetric.weightedLength
      (fun x : D.Space => Real.exp (ξ * f (x : ℂ))) (D.pt ∘ P) a b := by
  have hE : E.len P a b =
      HigherDimLQGMetric.curveLengthWith
        (fun x y : ℂ => E (x, y)) P a b := by
    rw [E.len_eq_curveLength, ← HigherDimLQGMetric.curveLengthWith_edist]
    rfl
  rw [hE]
  have heq : (fun x y : ℂ => E (x, y)) =
      (fun x y : ℂ => weylScale ξ f D (x, y)) := by
    funext x y
    exact hWeyl (x, y)
  rw [heq]
  exact Toolkit.WeylLength.weylCurveLength_eq_weightedLength D ξ f hforget hP

private theorem shifted_len_eq_of_agree_on_trace
    (D E F : LSCMetric) (ξ : ℝ) (f g : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget' D))
    (hE : ∀ p : ℂ × ℂ, E p = weylScale ξ f D p)
    (hF : ∀ p : ℂ × ℂ, F p = weylScale ξ g D p)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (hfg : ∀ t ∈ Icc a b, f (P t) = g (P t)) :
    E.len P a b = F.len P a b := by
  rw [shifted_len_eq_weighted D E ξ f hforget hE hP,
    shifted_len_eq_weighted D F ξ g hforget hF hP]
  apply HigherDimLQGMetric.weightedLength_congr_weight
  intro t ht
  exact congrArg (fun y : ℝ => Real.exp (ξ * y)) (hfg t ht)

 


theorem internal_eq_of_shifts_agree_on_carrier
    (D E F : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f g : C(ℂ, ℝ)) (mE ME mF MF : ℝ)
    (hforget : Continuous (euclidForget' D))
    (hLength : D.IsLengthSpace)
    (hE : ∀ p : ℂ × ℂ, E p = weylScale ξ f D p)
    (hF : ∀ p : ℂ × ℂ, F p = weylScale ξ g D p)
    (hf : ∀ x : ℂ, mE ≤ f x ∧ f x ≤ ME)
    (hg : ∀ x : ℂ, mF ≤ g x ∧ g x ≤ MF)
    (Y : Set ℂ) (hfg : ∀ x ∈ Y, f x = g x) (p : Y × Y) :
    E.internal Y p = F.internal Y p := by
  apply le_antisymm
  · unfold LSCMetric.internal
    apply le_iInf
    intro P
    apply le_iInf
    intro a
    apply le_iInf
    intro b
    apply le_iInf
    intro hP
    apply le_iInf
    intro hY
    apply le_iInf
    intro ha
    apply le_iInf
    intro hb
    have hPD := Toolkit.WeylShift.curve_back_all_continuous D F ξ hξ g hforget hF hP
    have hPE := Toolkit.WeylShift.curve_forward D E ξ hξ f mE ME hforget hE hf hLength hPD
    have hLen := shifted_len_eq_of_agree_on_trace D E F ξ f g hforget hE hF
      hPD (fun t ht => hfg (P t) (hY t ht))
    exact (internal_le_curve_len E Y p hPE hY ha hb).trans_eq hLen
  · unfold LSCMetric.internal
    apply le_iInf
    intro P
    apply le_iInf
    intro a
    apply le_iInf
    intro b
    apply le_iInf
    intro hP
    apply le_iInf
    intro hY
    apply le_iInf
    intro ha
    apply le_iInf
    intro hb
    have hPD := Toolkit.WeylShift.curve_back_all_continuous D E ξ hξ f hforget hE hP
    have hPF := Toolkit.WeylShift.curve_forward D F ξ hξ g mF MF hforget hF hg hLength hPD
    have hLen := shifted_len_eq_of_agree_on_trace D E F ξ f g hforget hE hF
      hPD (fun t ht => hfg (P t) (hY t ht))
    exact (internal_le_curve_len F Y p hPF hY ha hb).trans_eq hLen.symm

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
