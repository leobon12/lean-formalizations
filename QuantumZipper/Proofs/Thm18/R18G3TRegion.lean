import QuantumZipper.Proofs.Thm18.R18G3TRSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (R-bc): schemes `B` and `C` agree on both half-discs

For every index `i = (δ, η, C)` the cut-off profile `g3wCut γ η` equals the wedge profile
`g3wProf γ` on both half-discs of `i`, because they lie in the annulus `3η/4 ≤ ‖z‖ < 1/2 + η/4`.
Hence the region fields of the two shifted fields coincide (`restrictField_circIn_g3pField_congr`),
and so do the region boundary measures `g3pν₁`, `g3pν₂` of schemes `B` and `C`
(`g3pν₁_cut_eq`, `g3pν₂_cut_eq`). This is the first input of (R-bc) (D85). Own elementary
bookkeeping.
-/

noncomputable section

open MeasureTheory Metric Set Filter

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- Points of the two half-discs of an index have `3η/4 ≤ ‖z‖ ≤ 1/2 + η/4`. -/
theorem norm_bounds_of_mem_ball₁ (i : G3Idx) {z : ℂ} (hz : z ∈ ball (i.t₁ : ℂ) i.r₁) :
    3 * i.η / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2 + i.η / 4 := by
  have hη := i.hη; have hηδ := i.hηδ; have hδ := i.hδ
  rw [mem_ball, dist_eq_norm] at hz
  have ht : ‖(i.t₁ : ℂ)‖ = (i.δ + i.η) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, G3Idx.t₁, abs_of_neg (by linarith)]; ring
  have h1 : ‖(i.t₁ : ℂ)‖ ≤ ‖z - i.t₁‖ + ‖z‖ := by
    calc ‖(i.t₁ : ℂ)‖ = ‖z - (z - i.t₁)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖z - i.t₁‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have h2 : ‖z‖ ≤ ‖z - i.t₁‖ + ‖(i.t₁ : ℂ)‖ := by
    calc ‖z‖ = ‖(z - i.t₁) + i.t₁‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  unfold G3Idx.r₁ at hz
  constructor <;> nlinarith

theorem norm_bounds_of_mem_ball₂ (i : G3Idx) {z : ℂ} (hz : z ∈ ball (i.t₂ : ℂ) i.r₂) :
    3 * i.η / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2 + i.η / 4 := by
  have hη := i.hη; have hηδ := i.hηδ; have hδ := i.hδ
  rw [mem_ball, dist_eq_norm] at hz
  have ht : ‖(i.t₂ : ℂ)‖ = (1 / 2 + i.η) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, G3Idx.t₂, abs_of_pos (by linarith)]
  have h1 : ‖(i.t₂ : ℂ)‖ ≤ ‖z - i.t₂‖ + ‖z‖ := by
    calc ‖(i.t₂ : ℂ)‖ = ‖z - (z - i.t₂)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖z - i.t₂‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have h2 : ‖z‖ ≤ ‖z - i.t₂‖ + ‖(i.t₂ : ℂ)‖ := by
    calc ‖z‖ = ‖(z - i.t₂) + i.t₂‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  unfold G3Idx.r₂ at hz
  constructor <;> nlinarith

/-- The cut-off profile is the wedge profile on the annulus `η/2 ≤ ‖z‖ ≤ 7/8`. -/
theorem g3wCut_eq_of_norm (γ η : ℝ) (hη : 0 < η) {z : ℂ} (h1 : η / 2 ≤ ‖z‖) (h2 : ‖z‖ ≤ 7 / 8) :
    g3wCut γ η z = g3wProf γ z := by
  have a1 : 1 ≤ (‖z‖ - η / 4) / (η / 4) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have a2 : 1 ≤ (1 - ‖z‖) * 8 := by linarith
  simp only [g3wCut, Real.smoothTransition.one_of_one_le a1,
    Real.smoothTransition.one_of_one_le a2, one_mul]

/-- The cut-off profile is the wedge profile on both half-discs of the index. -/
theorem g3wCut_eqOn_ball (γ : ℝ) (i : G3Idx) (k : Bool) :
    EqOn (g3wCut γ i.η) (g3wProf γ)
      (ball ((if k then i.t₁ else i.t₂ : ℝ) : ℂ) (if k then i.r₁ else i.r₂)) := by
  intro z hz
  have hη := i.hη; have hηδ := i.hηδ; have hδ := i.hδ
  have hb : 3 * i.η / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2 + i.η / 4 := by
    cases k
    · exact norm_bounds_of_mem_ball₂ i (by simpa using hz)
    · exact norm_bounds_of_mem_ball₁ i (by simpa using hz)
  exact g3wCut_eq_of_norm γ i.η hη (by linarith [hb.1]) (by linarith [hb.2])

/-- Region fields only see the profile on the half-disc. -/
theorem restrictField_circIn_g3pField_congr (γ : ℝ) {g₁ g₂ : ℂ → ℝ} {t r : ℝ}
    (h : EqOn g₁ g₂ (ball (t : ℂ) r)) (ω : gffBase.Ω) :
    restrictField (circIn t r) (g3pField γ g₁ ω) = restrictField (circIn t r) (g3pField γ g₂ ω) := by
  classical
  funext μ
  by_cases hμ : μ ∈ circIn t r
  · simp only [restrictField, if_pos hμ, g3pField, Pi.add_apply, ofFun]
    congr 1
    obtain ⟨d, ρ, hρ, rfl, r', hr', hnull⟩ := hμ
    refine integral_congr_ae ?_
    have hae : ∀ᵐ z ∂(foldedCircle d ρ), z ∈ closedBall (t : ℂ) r' := by
      rw [ae_iff]; exact hnull
    filter_upwards [hae] with z hz
    exact h (closedBall_subset_ball hr' hz)
  · simp only [restrictField, if_neg hμ]

/-- Schemes `B` and `C` have the same region-1 boundary measure. -/
theorem g3pν₁_cut_eq (γ : ℝ) (i : G3Idx) (ω : gffBase.Ω) :
    g3pν₁ γ (g3wCut γ i.η) i ω = g3pν₁ γ (g3wProf γ) i ω := by
  unfold g3pν₁
  rw [restrictField_circIn_g3pField_congr γ (by simpa using g3wCut_eqOn_ball γ i true) ω]

/-- Schemes `B` and `C` have the same region-2 boundary measure. -/
theorem g3pν₂_cut_eq (γ : ℝ) (i : G3Idx) (ω : gffBase.Ω) :
    g3pν₂ γ (g3wCut γ i.η) i ω = g3pν₂ γ (g3wProf γ) i ω := by
  unfold g3pν₂
  rw [restrictField_circIn_g3pField_congr γ (by simpa using g3wCut_eqOn_ball γ i false) ω]

end R18
end QuantumZipper
