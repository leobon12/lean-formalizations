/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkNoise10Complete
import InteractingSLE.WangWu.CouplingFrozenTwo

/-!
# Continuous freezing of announced local noise

The finite endpoint is frozen after the lifetime. A conull event will ensure
strict localization, cofinality, and existence of the endpoint on every retained path.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Freeze11

variable {Ω : Type*} {N : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞}
  {Q : ℕ → Ω → ℝ≥0} {G : Set Ω}

/-- The noise before its lifetime, frozen at its left limit afterwards and zero off `G`. -/
def frozenNoise (N : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞) (G : Set Ω)
    (u : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then
    if (u : ℝ≥0∞) < τ ω then N u ω
    else limUnder (𝓝[<] (τ ω).toNNReal) (N · ω)
  else 0

/-- Stopped continuity and cofinality give continuity on every compact interval before the lifetime. -/
theorem continuousOn_noise_before
    (hc : ∀ n ω, Continuous fun u => N (min u (Q n ω)) ω)
    {ω : Ω} (hexh : ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ ω → ∃ n, u ≤ Q n ω)
    {U : ℝ≥0} (hU : (U : ℝ≥0∞) < τ ω) :
    ContinuousOn (N · ω) (Icc 0 U) := by
  obtain ⟨n, hn⟩ := hexh U hU
  refine (hc n ω).continuousOn.congr fun u hu => ?_
  dsimp only
  rw [min_eq_left (hu.2.trans hn)]

/-- Every path of the frozen noise is continuous. -/
theorem continuous_frozenNoise
    (hc : ∀ n ω, Continuous fun u => N (min u (Q n ω)) ω)
    (hpos : ∀ ω ∈ G, 0 < τ ω)
    (hexh : ∀ ω ∈ G, ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ ω → ∃ n, u ≤ Q n ω)
    (hlim : ∀ ω ∈ G, τ ω ≠ ⊤ → ∃ L : ℝ,
      Tendsto (N · ω) (𝓝[<] (τ ω).toNNReal) (𝓝 L)) (ω : Ω) :
    Continuous (frozenNoise N τ G · ω) := by
  by_cases hω : ω ∈ G
  · by_cases htop : τ ω = ⊤
    · have heq : (frozenNoise N τ G · ω) = (N · ω) := by
        funext u
        simp only [frozenNoise, hω, ↓reduceIte, htop, ENNReal.coe_lt_top]
      rw [heq]
      refine continuous_iff_continuousAt.2 fun u => ?_
      have hU : ((u + 1 : ℝ≥0) : ℝ≥0∞) < τ ω := by
        rw [htop]; exact ENNReal.coe_lt_top
      apply (continuousOn_noise_before hc (hexh ω hω) hU).continuousAt
      rw [show Icc (0 : ℝ≥0) (u + 1) = Iic (u + 1) by ext x; simp]
      exact Iic_mem_nhds (lt_add_one u)
    · obtain ⟨L, hL⟩ := hlim ω hω htop
      have hcoe : ((τ ω).toNNReal : ℝ≥0∞) = τ ω := ENNReal.coe_toNNReal htop
      have hnb : (𝓝[<] (τ ω).toNNReal).NeBot := by
        refine nhdsLT_neBot_of_exists_lt ⟨0, ?_⟩
        have hp := hpos ω hω
        rw [← hcoe] at hp
        exact_mod_cast hp
      have hf := WangWu.continuous_frozen_path (S := τ ω) (σ := (τ ω).toNNReal)
        (fun U hU _ => continuousOn_noise_before hc (hexh ω hω) hU)
        (fun _ => by rwa [hL.limUnder_eq])
      convert hf using 1
      funext u
      simp only [frozenNoise, hω, ↓reduceIte]
      by_cases hu : (u : ℝ≥0∞) < τ ω
      · have hus : u ≤ (τ ω).toNNReal := by
          rw [← hcoe] at hu
          exact_mod_cast hu.le
        simp only [hu, ↓reduceIte, min_eq_left hus]
      · have hus : (τ ω).toNNReal ≤ u := by
          rw [← hcoe, not_lt] at hu
          exact_mod_cast hu
        have hnot : ¬ ((min u (τ ω).toNNReal : ℝ≥0) : ℝ≥0∞) < τ ω := by
          rw [min_eq_right hus, hcoe]
          exact lt_irrefl _
        simp only [hu, hnot, ↓reduceIte]
  · simp only [frozenNoise, hω, ↓reduceIte]
    exact continuous_const

/-- The frozen version starts at zero on every sample. -/
theorem frozenNoise_zero (h0 : ∀ ω, N 0 ω = 0) (hpos : ∀ ω ∈ G, 0 < τ ω) (ω : Ω) :
    frozenNoise N τ G 0 ω = 0 := by
  by_cases hω : ω ∈ G
  · simp only [frozenNoise, hω, ↓reduceIte, ENNReal.coe_zero, hpos ω hω, h0]
  · simp only [frozenNoise, hω, ↓reduceIte]

/-- Before an announced stop the frozen noise is precisely the conull modification of the local noise. -/
theorem frozenNoise_min
    (hstrict : ∀ ω ∈ G, ∀ n, (Q n ω : ℝ≥0∞) < τ ω) (n : ℕ) (u : ℝ≥0) (ω : Ω) :
    frozenNoise N τ G (min u (Q n ω)) ω =
      if ω ∈ G then N (min u (Q n ω)) ω else 0 := by
  by_cases hω : ω ∈ G
  · have hu : ((min u (Q n ω) : ℝ≥0) : ℝ≥0∞) < τ ω :=
      lt_of_le_of_lt (by exact_mod_cast min_le_right u (Q n ω)) (hstrict ω hω n)
    simp only [frozenNoise, hω, hu, ↓reduceIte]
  · simp only [frozenNoise, hω, ↓reduceIte]

/-- Cofinality makes the announcing clock equal to the original time before the lifetime. -/
theorem annClock_eq_before {ω : Ω}
    (hexh : ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ ω → ∃ n, u ≤ Q n ω)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < τ ω) : WholeField.annClock Q u ω = u := by
  obtain ⟨n, hn⟩ := hexh u hu
  exact WholeField.annClock_eq_of_le hn

end InteractingSLE.Sec5.TwoMark.Freeze11
