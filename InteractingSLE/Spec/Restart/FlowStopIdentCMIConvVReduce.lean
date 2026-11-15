/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVLifetime

/-! # The proved per-stop kernels feed the measurable-exit converse -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open StoppedExtend

/-- The landed path data and reference kernel discharge all inputs of the V converse. -/
theorem cmiStoppedVStatement_of_converse (h2 : CMIConverseVStatement.{u}) :
    CMIStoppedVStatement.{u} := by
  classical
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN a c haO hVa hsN F q hq hFq hFΔ y θ S _ Q₀ _ H₀ hH
    s hsle hslim Λ hΛm hΛ k hk hprob Γ U hΓ
  obtain ⟨h', 𝓕₀, W₀, VL₀, VR₀, B₀, htr, hC, hgen⟩ := hΓ
  obtain ⟨hX, -⟩ := hC.2.2.2
  obtain ⟨W₁, hW₁⟩ := cmiStopDataStatement κ hκ b J hb N hN V hV hVb hVN a c hVa hsN y θ Q₀
    Γ U h' 𝓕₀ W₀ VL₀ VR₀ B₀ hC hgen hX
  refine h2 κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN a c haO hVa hsN F q hq hFq hFΔ y θ Q₀ H₀ hH s
    hsle hslim Λ hΛm hΛ k hk hprob Γ U h' 𝓕₀ W₀ VL₀ VR₀ B₀ htr hC hgen hX W₁ hW₁ ?_
  intro τ hτ hτe uR huR φ
  by_cases hyN : (y : ℂ) ∈ N
  · have hyO : y ∈ O := by simpa using hNO _ hyN (by simp)
    have hτU : ∀ᵐ ω ∂Q₀, (τ ω : ℝ≥0∞) < U ω := hτe.mono fun ω h => h.trans_le (min_le_left _ _)
    exact ae_condExp_shift_eq_ref hκ hb hbR hO hbO hyO θ hq hN hNO hFq hFΔ hyN hsle hslim hΛm hΛ hk hprob htr hC hX
      hτ hτU (hW₁ τ hτ hτe) huR φ
  · -- the seed is outside the buffer: the exit time is `0`, so there is no stop before it
    have hfalse : ∀ᵐ ω ∂Q₀, False := by
      filter_upwards [hτe, hgen] with ω h1' h2'
      have h0 : Γ ω 0 = y := sub_eq_zero.1 h2'.1
      have hnV : Γ ω 0 ∉ V := by
        rw [h0]; exact fun hy => hyN (hVN (subset_closure hy))
      rw [RLC.exitTime_eq_zero (U ω) hnV] at h1'
      exact absurd h1' (not_lt.2 bot_le)
    obtain ⟨_, hω⟩ := hfalse.exists
    exact hω.elim

/-- R66's full explicit-shift identification, including the lifetime clause. -/
theorem flowLineStopIdentCMIVStatement_of_converse (h : CMIConverseVStatement.{u}) :
    FlowLineStopIdentCMIVStatement.{u} :=
  flowLineStopIdentCMIVStatement_of_stopped (cmiStoppedVStatement_of_converse h)

end InteractingSLE.Restart.FlowStopIdentCMI
