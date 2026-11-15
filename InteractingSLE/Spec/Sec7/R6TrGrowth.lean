/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TpIncrement

/-!
# Full relative-hull increments and fixed physical balls

PROVE-R6-TWO, Astra §§3.2 and 5. All later times here are real.
The estimate controls newly filled components as well as the trace.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.R6Tr

/-- The entire newly removed physical set is confined to any prescribed
ball about the old tip, uniformly for short real capacity increments. -/
theorem full_increment_localization {V : Set ℂ} {ψ E₀ : ℂ → ℂ}
    (hψ : SupercriticalConformalCovariance.IsConformalBijection ψ V H)
    (hE₀ : EqOn E₀ (Function.invFunOn ψ V) H)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q₀ : ℝ} (hq₀ : 0 ≤ q₀)
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q₀) z)) Hbar)
    {p : ℂ} (htip : E₀ (extendFrom H (fwdMapInv W q₀) 0) = p)
    {e : ℝ} (he : 0 < e) :
    ∃ θ > 0, ∀ q : ℝ, q₀ ≤ q → q < q₀ + θ →
      (V ∩ ψ ⁻¹' (H \ fwdHull W q₀)) \ (V ∩ ψ ⁻¹' (H \ fwdHull W q)) ⊆ ball p e := by
  obtain ⟨ρ, hρ, hρE⟩ := Metric.continuousWithinAt_iff.1
    (hEc 0 (R6Fc.real_mem_Hbar 0)) e he
  have hB : ∀ z ∈ H, ‖z‖ ≤ ρ / 2 → E₀ (fwdMapInv W q₀ z) ∈ ball p e := by
    intro z hz hzn
    have hc := hρE (QuantumZipper.H_subset_Hbar hz) (show dist z (0 : ℂ) < ρ by
      rw [dist_zero_right]; linarith)
    rw [htip, extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 hq₀) hz] at hc
    exact hc
  obtain ⟨θ, hθ, hsmall⟩ := R6Fc.exists_shift_hull_small hW q₀ hρ
  refine ⟨θ, hθ, fun q hq hqθ w hw => ?_⟩
  by_contra hwb
  have hfree := R6Fc.mem_of_increment hE₀ hψ hW hW0 hq₀ hB hq
    (hsmall _ (sub_nonneg.2 hq) (by linarith)) hw.1.1 hw.1.2.2 hwb
  exact hw.2 ⟨hw.1.1, hw.1.2.1, hfree⟩

/-- Both physical landing balls can be fixed before the later inner
time is selected. Multiple prime ends above either landing are allowed. -/
theorem two_fixed_balls_persist {D V : Set ℂ} {ψ E₀ : ℂ → ℂ}
    (hψ : SupercriticalConformalCovariance.IsConformalBijection ψ V H)
    (hE₀ : EqOn E₀ (Function.invFunOn ψ V) H)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q₀ : ℝ} (hq₀ : 0 ≤ q₀)
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q₀) z)) Hbar)
    {p p₁ p₂ : ℂ} (htip : E₀ (extendFrom H (fwdMapInv W q₀) 0) = p)
    (hne₁ : p₁ ≠ p) (hne₂ : p₂ ≠ p)
    (hloc₁ : ∃ r > 0, D ∩ ball p₁ r ⊆ V ∩ ψ ⁻¹' (H \ fwdHull W q₀))
    (hloc₂ : ∃ r > 0, D ∩ ball p₂ r ⊆ V ∩ ψ ⁻¹' (H \ fwdHull W q₀)) :
    ∃ θ > 0, ∃ e₁ > 0, ∃ e₂ > 0, ∀ q : ℝ, q₀ ≤ q → q < q₀ + θ →
      D ∩ ball p₁ e₁ ⊆ V ∩ ψ ⁻¹' (H \ fwdHull W q) ∧
      D ∩ ball p₂ e₂ ⊆ V ∩ ψ ⁻¹' (H \ fwdHull W q) := by
  obtain ⟨r₁, hr₁, h₁⟩ := hloc₁
  obtain ⟨r₂, hr₂, h₂⟩ := hloc₂
  obtain ⟨θ₁, hθ₁, e₁, he₁, hf₁⟩ := R6Tp.local_inclusion_persists hψ hE₀ hW hW0 hq₀ hEc htip hne₁ hr₁ h₁
  obtain ⟨θ₂, hθ₂, e₂, he₂, hf₂⟩ := R6Tp.local_inclusion_persists hψ hE₀ hW hW0 hq₀ hEc htip hne₂ hr₂ h₂
  exact ⟨min θ₁ θ₂, lt_min hθ₁ hθ₂, e₁, he₁, e₂, he₂, fun q hq hqθ =>
    ⟨hf₁ q hq (hqθ.trans_le (add_le_add le_rfl (min_le_left _ _))),
      hf₂ q hq (hqθ.trans_le (add_le_add le_rfl (min_le_right _ _)))⟩⟩

end InteractingSLE.Sec7.R6Tr
