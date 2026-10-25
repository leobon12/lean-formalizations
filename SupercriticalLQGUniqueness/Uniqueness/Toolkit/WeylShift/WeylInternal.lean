import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylBridge




 




set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

private theorem internal_le_len (D : LSCMetric) (Y : Set ℂ) (p : Y × Y)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (hY : ∀ t ∈ Icc a b, P t ∈ Y)
    (ha : P a = (p.1 : ℂ)) (hb : P b = (p.2 : ℂ)) :
    D.internal Y p ≤ D.len P a b := by
  unfold LSCMetric.internal
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hP <| iInf_le_of_le hY <|
    iInf_le_of_le ha <| iInf_le_of_le hb le_rfl

 
theorem internal_lower (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ)) (m M : ℝ)
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ q : ℂ × ℂ, E q = weylScale ξ g D q)
    (hg : ∀ x : ℂ, m ≤ g x ∧ g x ≤ M)
    (Y : Set ℂ) (p : Y × Y) :
    ENNReal.ofReal (Real.exp (ξ * m)) * D.internal Y p ≤ E.internal Y p := by
  unfold LSCMetric.internal
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
  have hPD := curve_back D E ξ hξ g m hforget hWeyl (fun x => (hg x).1) hP
  have hlow := (length_bounds D E ξ hξ g m M hforget hWeyl hg hPD).1
  have hd := internal_le_len D Y p hPD hY ha hb
  exact (mul_le_mul' le_rfl hd).trans hlow

 
theorem internal_upper (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ)) (m M : ℝ)
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ q : ℂ × ℂ, E q = weylScale ξ g D q)
    (hg : ∀ x : ℂ, m ≤ g x ∧ g x ≤ M)
    (hLength : D.IsLengthSpace) (Y : Set ℂ) (p : Y × Y) :
    E.internal Y p ≤ ENNReal.ofReal (Real.exp (ξ * M)) * D.internal Y p := by
  have hc0 : ENNReal.ofReal (Real.exp (ξ * M)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hct : ENNReal.ofReal (Real.exp (ξ * M)) ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold LSCMetric.internal
  simp only [ENNReal.mul_iInf_of_ne hc0 hct]
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
  have hPE := curve_forward D E ξ hξ g m M hforget hWeyl hg hLength hP
  have hup := (length_bounds D E ξ hξ g m M hforget hWeyl hg hP).2
  have he := internal_le_len E Y p hPE hY ha hb
  exact he.trans hup

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift
