/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrTip
import InteractingSLE.Spec.Sec7.R6TrGrowth

/-!
# Exposed landings may have several active prime ends

PROVE-R6-TWO, Astra Lemma 4.2. The only singleton fibre is the
current tip's, transported through the ambient Jordan-face chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.R6Tr

/-- Factorization through the ambient Jordan face transports Aux. 136
to the relative current chart. The normalization at the driver is an
incident-prime-end assertion, not equality of physical tips alone. -/
theorem singleton_tip_of_ambient_factorization {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) (hs : IsSingletonTipFiber W t)
    {E L : ℂ → ℂ} (hL : MapsTo L Hbar Hbar) (hLi : InjOn L Hbar) (hL0 : L 0 = 0)
    (hfactor : ∀ x : ℝ, E (x : ℂ) = extendFrom H (fwdMapInv W t) (L x)) :
    ∀ x : ℝ, E (x : ℂ) = η t → x = 0 := by
  intro x hx
  have hzero : L (x : ℂ) = 0 := singletonTipFiber_full hη hW hW0 ht hs _
    (hL (R6Fc.real_mem_Hbar x)) ((hfactor x).symm.trans hx)
  have hx0 : (x : ℂ) = 0 := hLi (R6Fc.real_mem_Hbar x) (R6Fc.real_mem_Hbar 0)
    (by simpa only [Complex.ofReal_zero, hL0] using hzero)
  exact_mod_cast hx0

/-- Once the outer current domain agrees with the inner current
domain near the tip, an exposed landing can be chosen arbitrarily
close to the driver. Its own fibre is unrestricted. -/
theorem exists_negative_exposed_landing {D D₀ U : Set ℂ} {E : ℂ → ℂ} {p : ℂ}
    (hE : ContinuousOn E Hbar) (hE0 : E 0 = p)
    (hfibre : ∀ x : ℝ, E (x : ℂ) = p → x = 0)
    (hU : IsOpen U) (hpU : p ∈ U)
    (hloc : ∃ r > 0, D ∩ ball p r ⊆ D₀) {v : ℝ} (hv : v < 0) :
    ∃ ξ : ℝ, v < ξ ∧ ξ < 0 ∧ E (ξ : ℂ) ∈ U ∧ E (ξ : ℂ) ≠ p ∧
      ∃ e > 0, D ∩ ball (E (ξ : ℂ)) e ⊆ D₀ := by
  obtain ⟨r₀, hr₀, h₀⟩ := hloc
  obtain ⟨rU, hrU, hballU⟩ := Metric.isOpen_iff.1 hU p hpU
  let r := min r₀ rU
  have hr : 0 < r := lt_min hr₀ hrU
  obtain ⟨δ, hδ, hδE⟩ := Metric.continuousWithinAt_iff.1
    (hE 0 (R6Fc.real_mem_Hbar 0)) (r / 2) (half_pos hr)
  let d := min δ (-v)
  have hd : 0 < d := lt_min hδ (neg_pos.2 hv)
  let ξ := -d / 2
  have hξneg : ξ < 0 := by dsimp [ξ]; linarith
  have hvξ : v < ξ := by have := min_le_right δ (-v); dsimp [ξ, d]; linarith
  have hland : dist (E (ξ : ℂ)) p < r / 2 := by
    rw [← hE0]
    apply hδE (R6Fc.real_mem_Hbar ξ)
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hξneg]
    have := min_le_left δ (-v)
    dsimp [ξ, d]
    linarith
  refine ⟨ξ, hvξ, hξneg, ?_, fun heq => hξneg.ne (hfibre ξ heq), r / 2, half_pos hr, ?_⟩
  · exact hballU (mem_ball.2 (hland.trans_le ((half_le_self hr.le).trans (min_le_right _ _))))
  · intro w hw
    apply h₀
    refine ⟨hw.1, mem_ball.2 ?_⟩
    have ht := dist_triangle w (E (ξ : ℂ)) p
    have hwnear := mem_ball.1 hw.2
    have hrr : r ≤ r₀ := min_le_left _ _
    linarith

/-- Aux. 136 and the common-time ambient driver collar supply the
physical local agreement used in the exposed-point choice. This works
for both finite and infinite outgoing targets. -/
theorem exists_negative_exposed_landing_of_ambient_collar
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (hs : IsSingletonTipFiber W t)
    {D D₀ U : Set ℂ} (hD : D ⊆ H \ fwdHull W t)
    {r : ℝ} (hr : 0 < r) (hcollar : H ∩ ball (0 : ℂ) r ⊆ (fwdMapInv W t) ⁻¹' D₀)
    {E : ℂ → ℂ} (hE : ContinuousOn E Hbar) (hE0 : E 0 = η t)
    (hfibre : ∀ x : ℝ, E (x : ℂ) = η t → x = 0)
    (hU : IsOpen U) (hpU : η t ∈ U) {v : ℝ} (hv : v < 0) :
    ∃ ξ : ℝ, v < ξ ∧ ξ < 0 ∧ E (ξ : ℂ) ∈ U ∧ E (ξ : ℂ) ≠ η t ∧
      ∃ e > 0, D ∩ ball (E (ξ : ℂ)) e ⊆ D₀ := by
  obtain ⟨e, he, hlocal⟩ := local_inclusion_of_tip_collar hη hW hW0 ht hs hr hcollar
  exact exists_negative_exposed_landing hE hE0 hfibre hU hpU
    ⟨e, he, fun w hw => hlocal ⟨hD hw.1, hw.2⟩⟩ hv

end InteractingSLE.Sec7.R6Tr
