import QuantumZipper.Proofs.Zipper.SWCoreA5Win

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A5 (2): the uniform variable-scale window limit (all resolutions)

Combines `SWCore.unifWin_fixedN` with `c N, c' N → 1` (SW Thm 1.1, p. 9: the window constants
tend to `1`): for an equicontinuous family of weights and scales (hypotheses of
`unifWin_fixedN`), `vsInt γ x (g i) (s i) k → ∫ g i dμ` uniformly in `i`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6

variable {γ : ℝ} {x : FieldSample} {c c' : ℕ → ℝ}

/-- **Uniform variable-scale window limit** (SW Cor. 3.2 / proof of Thm 1.4, uniform over an
equicontinuous family). -/
theorem unifWin (hc : Tendsto c atTop (𝓝 1)) (hc' : Tendsto c' atTop (𝓝 1))
    (hWin : WindowLimits γ x c c')
    (hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ x K < ⊤)
    (hsupm : ∀ N j, Measurable (supWin γ x N j)) (hinfm : ∀ N j, Measurable (infWin γ x N j))
    {ι : Type*} {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) {g s : ι → ℂ → ℝ} {B A : ℝ}
    (hB : 0 ≤ B) (hg0 : ∀ i w, 0 ≤ g i w) (hgB : ∀ i w, g i w ≤ B)
    (hgC : ∀ i w, g i w ≠ 0 → w ∈ C)
    (hgeq : ∀ ε > 0, ∃ δ > 0, ∀ i w w', dist w w' < δ → |g i w - g i w'| ≤ ε)
    (hspos : ∀ i w, g i w ≠ 0 → 0 < s i w ∧ s i w ≤ A)
    (hseq : ∀ ε > 0, ∃ δ > 0, ∀ i w w', g i w ≠ 0 → g i w' ≠ 0 → dist w w' < δ →
      |Real.logb 2 (s i w) - Real.logb 2 (s i w')| ≤ ε)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ i, vsInt γ x (g i) (s i) k ≤
        ENNReal.ofReal (∫ w, g i w ∂qAreaMeasure γ x + η) ∧
      ENNReal.ofReal (∫ w, g i w ∂qAreaMeasure γ x) ≤
        vsInt γ x (g i) (s i) k + ENNReal.ofReal η := by
  set μ := qAreaMeasure γ x with hμ
  set Im := B * μ.real C with hImdef
  have hIm0 : 0 ≤ Im := mul_nonneg hB measureReal_nonneg
  have hIle : ∀ i, 0 ≤ ∫ w, g i w ∂μ ∧ ∫ w, g i w ∂μ ≤ Im := by
    intro i
    refine ⟨integral_nonneg (hg0 i), ?_⟩
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := C) fun w hw => by
      by_contra h; exact hw (hgC i w h)]
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := g i)
      (hμK C hC hCH) (C := B) fun w _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 i w)]; exact hgB i w
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans this)
  set τ := (η / 2) / (Im + η + 1) with hτdef
  have hτ : 0 < τ := by positivity
  have hτI : τ * (Im + η + 1) = η / 2 := by rw [hτdef]; field_simp
  have hcN : ∀ᶠ N in atTop, 1 - τ < c N ∧ c' N < 1 + τ ∧ 1 ≤ N ∧ 0 < c' N := by
    filter_upwards [hc.eventually (lt_mem_nhds (by linarith : 1 - τ < 1)),
      hc'.eventually (gt_mem_nhds (by linarith : 1 < 1 + τ)), eventually_ge_atTop 1,
      hc'.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with N h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N, hN1, hN2, hN, hc'pos⟩ := hcN.exists
  have hτ1 : τ < 1 := by
    rw [hτdef, div_lt_one (by positivity)]; linarith
  have hcpos : 0 < c N := by linarith
  filter_upwards [unifWin_fixedN hWin hμK hsupm hinfm hC hCH hB hg0 hgB hgC hgeq hspos hseq hN
    (half_pos hη)] with k hk i
  obtain ⟨hup, hlo⟩ := hk i
  obtain ⟨hI0, hIM⟩ := hIle i
  set I := ∫ w, g i w ∂μ
  set V := vsInt γ x (g i) (s i) k
  constructor
  · have h1 : V = ENNReal.ofReal (1 / c N) * (ENNReal.ofReal (c N) * V) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div,
        inv_mul_cancel₀ hcpos.ne', ENNReal.ofReal_one, one_mul]
    rw [h1]
    calc ENNReal.ofReal (1 / c N) * (ENNReal.ofReal (c N) * V)
        ≤ ENNReal.ofReal (1 / c N) * ENNReal.ofReal (I + η / 2) := by gcongr
      _ = ENNReal.ofReal ((I + η / 2) / c N) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
      _ ≤ ENNReal.ofReal (I + η) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_le_iff₀ hcpos]
          have : τ * (I + η) ≤ η / 2 := by
            rw [← hτI]; exact mul_le_mul_of_nonneg_left (by linarith) hτ.le
          nlinarith
  · by_cases hIη : I - η ≤ 0
    · calc ENNReal.ofReal I ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ V + ENNReal.ofReal η := le_add_self
    · push_neg at hIη
      have h2 : ENNReal.ofReal ((I - η / 2) / c' N) ≤ V := by
        calc ENNReal.ofReal ((I - η / 2) / c' N)
            = ENNReal.ofReal (1 / c' N) * ENNReal.ofReal (I - η / 2) := by
              rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
          _ ≤ ENNReal.ofReal (1 / c' N) * (ENNReal.ofReal (c' N) * V) := by gcongr
          _ = V := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div,
                inv_mul_cancel₀ hc'pos.ne', ENNReal.ofReal_one, one_mul]
      have h3 : I - η ≤ (I - η / 2) / c' N := by
        rw [le_div_iff₀ hc'pos]
        have : τ * (I - η) ≤ η / 2 := by
          rw [← hτI]; exact mul_le_mul_of_nonneg_left (by linarith) hτ.le
        nlinarith
      calc ENNReal.ofReal I ≤ ENNReal.ofReal (I - η) + ENNReal.ofReal η := by
            rw [← ENNReal.ofReal_add hIη.le hη.le]; exact ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ V + ENNReal.ofReal η := by gcongr; exact (ENNReal.ofReal_le_ofReal h3).trans h2

end SWCore
end QuantumZipper
