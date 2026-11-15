import InteractingSLE.Spec.Sec5.Aux61RestartPrep

/-!
# Connecting positive boundary collars to the physical target

Packet PROVE-AUX61-R1. A compact positive real interval has a uniformly free
neighborhood when the retained closed obstacle avoids the positive real axis.
Horizontal segments just above this interval identify a collar at any positive
real point with the physical original target 1.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61Restart

/-- Vertical translation by height h has distance |h| from its real base. -/
theorem dist_real_add_height (x h : ℝ) :
    dist ((x : ℂ) + (h : ℂ) * I) (x : ℂ) = |h| := by
  simp only [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_real, norm_I, mul_one,
    Real.norm_eq_abs]

/-- A component having a positive-real collar carries the physical target 1,
provided the closed obstacle avoids the whole positive real boundary. -/
theorem original_target_mem_closure_of_positive_collar
    {A : Set ℂ} {b : ℂ}
    (hfree : ∀ x : ℝ, 0 < x → (x : ℂ) ∉ closure A)
    (hcollar : ∃ x : ℝ, 0 < x ∧
      ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ connectedComponentIn (H \ A) b) :
    (1 : ℂ) ∈ closure (connectedComponentIn (H \ A) b) := by
  obtain ⟨x, hx, hc⟩ := hcollar
  obtain ⟨δ, hδ, hcol⟩ := Metric.mem_nhdsWithin_iff.1 hc
  let J : Set ℝ := Icc (min x 1) (max x 1)
  have hJ : IsCompact ((fun t : ℝ => (t : ℂ)) '' J) :=
    isCompact_Icc.image continuous_ofReal
  have hJfree : (fun t : ℝ => (t : ℂ)) '' J ⊆ (closure A)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    exact hfree t ((lt_min hx zero_lt_one).trans_le ht.1)
  obtain ⟨ε, hε, hεfree⟩ :=
    hJ.exists_thickening_subset_open isClosed_closure.isOpen_compl hJfree
  apply Metric.mem_closure_iff.2
  intro ρ hρ
  let h : ℝ := min ε (min δ ρ) / 2
  have hh : 0 < h := by dsimp [h]; positivity
  have hhε : h < ε := by
    have := min_le_left ε (min δ ρ)
    dsimp [h]
    linarith only [this, lt_min hε (lt_min hδ hρ)]
  have hhδ : h < δ := by
    have := (min_le_right ε (min δ ρ)).trans (min_le_left δ ρ)
    dsimp [h]
    linarith only [this, lt_min hε (lt_min hδ hρ)]
  have hhρ : h < ρ := by
    have := (min_le_right ε (min δ ρ)).trans (min_le_right δ ρ)
    dsimp [h]
    linarith only [this, lt_min hε (lt_min hδ hρ)]
  let γ : ℝ → ℂ := fun t => (t : ℂ) + (h : ℂ) * I
  have hγH : ∀ t, γ t ∈ H := by
    intro t
    simpa only [γ, QuantumZipper.H, mem_ofPred_eq, add_im, ofReal_im, mul_im,
      ofReal_re, I_im, I_re, mul_one, mul_zero, add_zero, zero_add] using hh
  have hγfree : γ '' J ⊆ H \ A := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨hγH t, fun htA => ?_⟩
    apply hεfree (mem_thickening_iff.2 ⟨(t : ℂ), ⟨t, ht, rfl⟩, ?_⟩)
      (subset_closure htA)
    simpa only [γ, dist_real_add_height, abs_of_pos hh] using hhε
  have hxJ : x ∈ J := ⟨min_le_left _ _, le_max_left _ _⟩
  have h1J : (1 : ℝ) ∈ J := ⟨min_le_right _ _, le_max_right _ _⟩
  have hxC : γ x ∈ connectedComponentIn (H \ A) b := by
    apply hcol ⟨?_, hγH x⟩
    simpa only [mem_ball, γ, dist_real_add_height, abs_of_pos hh] using hhδ
  have hγC : γ '' J ⊆ connectedComponentIn (H \ A) b := by
    rw [connectedComponentIn_eq hxC]
    exact (isPreconnected_Icc.image _
      ((continuous_ofReal.add continuous_const).continuousOn)).subset_connectedComponentIn
        ⟨x, hxJ, rfl⟩ hγfree
  refine ⟨γ 1, hγC ⟨1, h1J, rfl⟩, ?_⟩
  rw [dist_comm]
  change dist ((1 : ℂ) + (h : ℂ) * I) (1 : ℂ) < ρ
  have hd := dist_real_add_height 1 h
  simp only [ofReal_one] at hd
  rw [hd, abs_of_pos hh]
  exact hhρ

end InteractingSLE.Sec5.Aux61Restart
