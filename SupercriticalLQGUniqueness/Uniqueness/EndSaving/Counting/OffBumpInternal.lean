import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylInternal
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylLocalTopology




 
set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

theorem internal_le_curve_len (D : LSCMetric) (Y : Set ℂ) (p : Y × Y)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (hY : ∀ t ∈ Icc a b, P t ∈ Y)
    (ha : P a = (p.1 : ℂ)) (hb : P b = (p.2 : ℂ)) :
    D.internal Y p ≤ D.len P a b := by
  unfold LSCMetric.internal
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hP <| iInf_le_of_le hY <|
    iInf_le_of_le ha <| iInf_le_of_le hb le_rfl

 

theorem internal_eq_of_zero_on_carrier
    (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ)) (m M : ℝ)
    (hforget : Continuous (euclidForget D))
    (hLength : D.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, E p = weylScale ξ g D p)
    (hg : ∀ x : ℂ, m ≤ g x ∧ g x ≤ M)
    (Y : Set ℂ) (hzero : ∀ x ∈ Y, g x = 0) (p : Y × Y) :
    E.internal Y p = D.internal Y p := by
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
    have hPE := Toolkit.WeylShift.curve_forward D E ξ hξ g m M hforget hWeyl hg hLength hP
    have hEq := Toolkit.WeylShift.length_eq_of_zero_trace_all D E ξ hξ g hforget hWeyl
      hPE (fun t ht => hzero (P t) (hY t ht))
    exact (internal_le_curve_len E Y p hPE hY ha hb).trans_eq hEq
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
    have hPD := Toolkit.WeylShift.curve_back_all_continuous D E ξ hξ g hforget hWeyl hP
    have hEq := Toolkit.WeylShift.length_eq_of_zero_trace_all D E ξ hξ g hforget hWeyl
      hP (fun t ht => hzero (P t) (hY t ht))
    exact (internal_le_curve_len D Y p hPD hY ha hb).trans_eq hEq.symm

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
