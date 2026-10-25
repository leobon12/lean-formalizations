import SupercriticalLQGUniqueness.B2.PfeWeyl.AroundWeylBound
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylBridge

 


set_option autoImplicit false
noncomputable section

open Filter Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

theorem smallAnnulusCosts_of_bounded_weyl
    (ξ : ℝ) (hξ : 0 ≤ ξ)
    (G W : ℕ → LSCMetric) (D E : LSCMetric)
    (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hE : ∀ p : ℂ × ℂ, E p = weylScale ξ f D p)
    (hW : ∀ n p, W n p = weylScale ξ (fn n) (G n) p)
    (M : ℝ) (hfLower : ∀ z, -M ≤ f z)
    {K V : Set ℂ} (hfnUpper : ∀ n, ∀ z ∈ V, fn n z ≤ M)
    (hsmall : PfeWeyl.SmallAnnulusCosts G D K V) :
    PfeWeyl.SmallAnnulusCosts W E K V := by
  intro z hz hNS δ hδ ρ hρ
  obtain ⟨w, hw, hfin⟩ := hNS
  have hDfin : D (z, w) < ⊤ := by
    have hbound :=
      Uniqueness.Toolkit.WeylShift.distance_lower D E ξ f (-M)
        hforget hE hfLower hξ z w
    have hc0 : ENNReal.ofReal (Real.exp (ξ * -M)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    by_contra hn
    have htop : D (z, w) = ⊤ := top_le_iff.mp (le_of_not_gt hn)
    rw [htop, ENNReal.mul_top hc0] at hbound
    exact (not_lt_of_ge hbound) hfin
  exact PfeWeyl.smallAnnulusCosts_weyl ξ hξ fn hsmall hW M hfnUpper
    z hz ⟨w, hw, hDfin⟩ δ hδ ρ hρ

end SupercriticalLQGUniqueness.B2.PfeAxioms
