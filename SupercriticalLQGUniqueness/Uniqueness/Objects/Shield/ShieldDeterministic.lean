import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldBump




 






set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

theorem shieldAt_of_weyl_shift
    (ξ : ℝ) (C : Objects.CorrectedEvent.Constants) (d e : LSCMetric)
    (w : ℂ) (t : ℝ) (ht : 0 < t) (K : ℝ)
    (he : ∀ x y : ℂ,
      e (x, y) = weylScale ξ (LQGMetric.testCont (shieldBumpAt K t w)) d (x, y))
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), d.IsCurve γ a b →
      ContinuousOn γ (Icc a b))
    (hbarrier : BiLipschitz.Barrier.Barrier d) (hlength : d.IsLengthSpace)
    (n : ℝ≥0∞) (hn0 : n ≠ 0) (hnt : n ≠ ⊤)
    (M : ℝ≥0∞) (hMt : M ≠ ⊤)
    (hbudget : ENNReal.ofReal (Real.exp (ξ * -K)) * M ≤
      ENNReal.ofReal C.lamConst * M⁻¹)
    (hinner : n * Objects.CorrectedEvent.around d w ((21 / 20) * t) ((39 / 20) * t) ≤ M)
    (houter : M⁻¹ ≤ n * Objects.CorrectedEvent.acr d w (2 * t) (3 * t)) :
    Objects.CorrectedEvent.around e w t (2 * t) < ⊤ ∧
      Objects.CorrectedEvent.around e w t (2 * t) ≤
        ENNReal.ofReal C.lamConst * Objects.CorrectedEvent.acr e w (2 * t) (3 * t) := by
  let f : C(ℂ, ℝ) := LQGMetric.testCont (shieldBumpAt K t w)
  have haround : Objects.CorrectedEvent.around e w t (2 * t) ≤
      ENNReal.ofReal (Real.exp (ξ * -K)) *
        Objects.CorrectedEvent.around d w ((21 / 20) * t) ((39 / 20) * t) := by
    apply around_wide_le_weyl_narrow ξ f d e he w t ht (-K)
    intro y hy1 hy2
    change shieldBumpAt K t w y = -K
    exact shieldBumpAt_eq_neg K ht w hy1.le hy2.le
  have hacr : Objects.CorrectedEvent.acr d w (2 * t) (3 * t) ≤
      Objects.CorrectedEvent.acr e w (2 * t) (3 * t) := by
    apply acr_le_weyl_off_bump ξ f d e he hcont hbarrier hlength w t ht
    intro y hy1 _
    change shieldBumpAt K t w y = 0
    exact shieldBumpAt_eq_zero_outer K ht w hy1
  have hscaled : n * Objects.CorrectedEvent.around e w t (2 * t) ≤
      ENNReal.ofReal (Real.exp (ξ * -K)) * M := by
    calc
      n * Objects.CorrectedEvent.around e w t (2 * t) ≤
          n * (ENNReal.ofReal (Real.exp (ξ * -K)) *
            Objects.CorrectedEvent.around d w ((21 / 20) * t) ((39 / 20) * t)) :=
        mul_le_mul' le_rfl haround
      _ = ENNReal.ofReal (Real.exp (ξ * -K)) *
          (n * Objects.CorrectedEvent.around d w ((21 / 20) * t) ((39 / 20) * t)) := by ring
      _ ≤ ENNReal.ofReal (Real.exp (ξ * -K)) * M :=
        mul_le_mul' le_rfl hinner
  constructor
  · have hfin : n * Objects.CorrectedEvent.around e w t (2 * t) < ⊤ :=
      lt_of_le_of_lt hscaled
        (ENNReal.mul_lt_top ENNReal.ofReal_ne_top.lt_top hMt.lt_top)
    exact (Objects.ProbabilityS7S9.enn_mul_lt_top_iff hn0 hnt _).mp hfin
  · rw [← ENNReal.mul_le_mul_iff_right hn0 hnt]
    calc
      n * Objects.CorrectedEvent.around e w t (2 * t) ≤
          ENNReal.ofReal (Real.exp (ξ * -K)) * M := hscaled
      _ ≤ ENNReal.ofReal C.lamConst * M⁻¹ := hbudget
      _ ≤ ENNReal.ofReal C.lamConst *
          (n * Objects.CorrectedEvent.acr e w (2 * t) (3 * t)) :=
        mul_le_mul' le_rfl (houter.trans (mul_le_mul' le_rfl hacr))
      _ = n * (ENNReal.ofReal C.lamConst *
          Objects.CorrectedEvent.acr e w (2 * t) (3 * t)) := by ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
