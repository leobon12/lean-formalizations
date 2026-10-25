import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 
theorem laneC_eventually_two_le_K_pow {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → 2 ≤ (K : ℝ) ^ ε := by
  have hlim : Tendsto (fun K : ℕ => (K : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.1 (hlim.eventually_ge_atTop 2)

 


theorem laneC_eventual_physical_support_le_source_radius
    (Q : PsiParams) (hR : Q.r₀ ≤ (1 : ℝ) / 100)
    (hε : Q.ε₀ ≤ (1 : ℝ) / 100) :
    ∃ K₀ : ℕ, ∀ K m : ℕ, K₀ ≤ K → m + 1 ≤ K →
      (K : ℝ) ^ Q.ε₀ ≤ (2 : ℝ) ^ m →
      ∀ t : ℝ, 0 < t → t ≤ (((2 : ℝ)⁻¹ ^ K) ^ 2) →
        (2 : ℝ)⁻¹ ^ K + 2 * Q.sigma t ≤ LaneCInputs.sourceRadius K m := by
  obtain ⟨K₁, hK₁⟩ := laneC_eventually_two_le_K_pow Q.ε₀_pos
  refine ⟨max 1 K₁, ?_⟩
  intro K m hK hmK hmHi t ht0 ht
  exact laneC_physical_support_le_source_radius Q hR hε
    (le_trans (le_max_left 1 K₁) hK) hmK
    (hK₁ K (le_trans (le_max_right 1 K₁) hK)) hmHi t ht0 ht

end SupercriticalLQGUniqueness.B2.DG20Conc
