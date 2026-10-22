import HigherDimLQGMetric.DGZ.NondegUniformSmall

/-! A crossing of any box shell crosses a member of a finite family of small shells. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

theorem nd_across_general_ge_inf (hd0 : 0 < d) {ξ : ℝ} {φ : Rd d → ℝ}
    (hφ : Continuous φ) {c : Rd d} {r₁ r₂ ρ : ℝ}
    (hr₂ : 0 < r₂) (_hr : r₂ < r₁) (hρ : 0 < ρ)
    (hρgap : 2 * ρ ≤ (r₁ - r₂) / 2)
    {Z : Finset (Rd d)} (hZne : Z.Nonempty)
    (hZs : ∀ g ∈ Z, g ∈ lsph c ((r₁ + r₂) / 2))
    (hZcov : lsph c ((r₁ + r₂) / 2) ⊆ ⋃ g ∈ Z, obox g ρ) :
    Z.inf' hZne (fun g => acrossDist ξ φ g (2 * ρ) ρ) ≤
      acrossDist ξ φ c r₁ r₂ := by
  rw [acrossDist]
  have hr₁ : 0 ≤ r₁ := by linarith
  refine le_lfppSetDist (lsph_nonempty hd0 c hr₂.le) (lsph_nonempty hd0 c hr₁)
    fun x hx y hy => ?_
  refine HigherDimLFPP.le_lfppDistOn (pcwJoined_univ x y) fun γ hγ _ => ?_
  have hsh := isShellPair_box c (by linarith : (r₁ + r₂) / 2 < r₁)
  obtain ⟨t₀, t₁, ht₀, ht₀₁, ht₁, hγt₀, -, -, -⟩ := hsh.exists_crossing_of_le zero_le_one
    hγ.continuousOn (by rw [hγ.source]; exact cbox_mono (by linarith) hx.1)
    (by rw [hγ.target]; exact hy.2)
  obtain ⟨g, hg, hpg⟩ := mem_iUnion₂.1 (hZcov hγt₀)
  have hy2 : γ 1 ∉ obox g (2 * ρ) := by
    rw [hγ.target]
    intro hyo
    have hyn := hy.2
    simp only [HigherDimLFPP.DGZ.obox, mem_ofPred_eq, not_forall, not_lt] at hyn
    obtain ⟨j, hj⟩ := hyn
    have h1 := hyo j
    have h2 := (hZs g hg).1 j
    have htri := abs_sub_abs_le_abs_sub (y j - c j) (g j - c j)
    have hsub : (y j - c j) - (g j - c j) = y j - g j := by ring
    rw [hsub] at htri
    linarith
  have h1 : acrossDist ξ φ g (2 * ρ) ρ ≤ ∫ t in t₀..1, lfppIntegrand ξ φ γ t :=
    acrossDist_le_integral hφ (by linarith) hγ ht₀ (by linarith) le_rfl
      (Or.inl ⟨HigherDimLFPP.DGZ.obox_subset_cbox g ρ hpg, hy2⟩)
  have h2 := integral_le_lfppLength (ξ := ξ) hφ hγ ht₀ (by linarith) le_rfl
  exact (Finset.inf'_le _ hg).trans (h1.trans h2)

end HigherDimLQGMetric.DGZ
