import SupercriticalLQGUniqueness.B2.PfeWeyl.W3XCountable
import SupercriticalLQGUniqueness.B2.PfeWeyl.W2ApproxRecovery

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

theorem eventually_weylScale_le_of_local_upper
    (D : LSCMetric) (hDforget : Continuous (euclidForget D))
    (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (g : ℕ → C(ℂ, ℝ))
    (hg : ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ j in atTop, ∀ x ∈ K, g j x ≤ f x + δ)
    {z w : ℂ} (hfin : weylScale ξ f D (z, w) ≠ ⊤)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∀ᶠ j in atTop, weylScale ξ (g j) D (z, w) ≤
      ENNReal.ofReal (Real.exp (ξ * δ)) *
        (weylScale ξ f D (z, w) + ENNReal.ofReal η) := by
  obtain ⟨P, L, hP, hu, hP0, hPL, hcost⟩ :=
    exists_near_min_weyl_curve D ξ f z w hfin hη
  have hPc := continuousOn_of_isCurve_of_forget D hDforget hP
  let K : Set ℂ := P '' Icc 0 L
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hPc
  filter_upwards [hg K hK δ hδ] with j hj
  have hpath : ∀ t ∈ Icc 0 L, ξ * g j (P t) ≤ ξ * f (P t) + ξ * δ := by
    intro t ht
    have htK : P t ∈ K := ⟨t, ht, rfl⟩
    nlinarith [hj (P t) htK]
  have hlin : (∫⁻ t in Icc (0 : ℝ) L,
      ENNReal.ofReal (Real.exp (ξ * g j (P t)))) ≤
      ENNReal.ofReal (Real.exp (ξ * δ)) *
        (∫⁻ t in Icc (0 : ℝ) L,
          ENNReal.ofReal (Real.exp (ξ * f (P t)))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Icc fun t _ => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
      simpa only [add_comm] using hpath t ‹_›))
  have hw : weylScale ξ (g j) D (z, w) ≤
      ∫⁻ t in Icc (0 : ℝ) L, ENNReal.ofReal (Real.exp (ξ * g j (P t))) := by
    unfold weylScale
    exact iInf_le_of_le P (iInf_le_of_le L (iInf_le_of_le hP
      (iInf_le_of_le hu (iInf_le_of_le hP0 (iInf_le_of_le hPL le_rfl)))))
  exact hw.trans (hlin.trans (mul_le_mul' le_rfl hcost.le))

end SupercriticalLQGUniqueness.B2.PfeWeyl
