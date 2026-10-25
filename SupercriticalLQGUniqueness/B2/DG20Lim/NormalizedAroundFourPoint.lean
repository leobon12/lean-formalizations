import SupercriticalLQGUniqueness.B2.DG20Lim.NormalizedLFPPPathLen

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem normalizedContLFPP_aroundDist_lt_of_four_point_crossLen
    (A : EuclideanAnnulus) (ξ : ℝ) (φ : C(ℂ, ℝ))
    (a : Ioi (0 : ℝ)) (z w : Fin 4 → ℂ)
    (hz : ∀ j, z j ∈ B2.Strong.cfgSet₁ A j)
    (hw : ∀ j, w j ∈ B2.Strong.cfgSet₂ A j)
    (a₀ a₁ a₂ a₃ B L : ℝ≥0∞)
    (h₀ : crossLenIn ξ φ (B2.Strong.cfgOpens A 0 : Set ℂ)
      {z 0} {w 0} < a₀)
    (h₁ : crossLenIn ξ φ (B2.Strong.cfgOpens A 1 : Set ℂ)
      {z 1} {w 1} < a₁)
    (h₂ : crossLenIn ξ φ (B2.Strong.cfgOpens A 2 : Set ℂ)
      {z 2} {w 2} < a₂)
    (h₃ : crossLenIn ξ φ (B2.Strong.cfgOpens A 3 : Set ℂ)
      {z 3} {w 3} < a₃)
    (hbudget : a₀ + a₁ + a₂ + a₃ < B)
    (hscaled : ENNReal.ofReal ((a : ℝ)⁻¹) * B < L) :
    (normalizedContLFPP ξ a φ).aroundDist A.toSet
      A.innerBoundary A.outerBoundary < L := by
  obtain ⟨γ, u, v, hγ, hA, hsep, hlen⟩ :=
    B2.DG20Pt.around_loop_of_four_crossLen A ξ φ a₀ a₁ a₂ a₃ B
      ((crossLenIn_le_of_singleton_endpoints ξ φ _ _ _ _ _ (hz 0) (hw 0)).trans_lt h₀)
      ((crossLenIn_le_of_singleton_endpoints ξ φ _ _ _ _ _ (hz 1) (hw 1)).trans_lt h₁)
      ((crossLenIn_le_of_singleton_endpoints ξ φ _ _ _ _ _ (hz 2) (hw 2)).trans_lt h₂)
      ((crossLenIn_le_of_singleton_endpoints ξ φ _ _ _ _ _ (hz 3) (hw 3)).trans_lt h₃)
      hbudget
  have hle :
      (normalizedContLFPP ξ a φ).aroundDist A.toSet
        A.innerBoundary A.outerBoundary ≤
      (normalizedContLFPP ξ a φ).len γ 0 1 := by
    unfold ContMetric.aroundDist
    exact iInf_le_of_le (0 : ℝ) (iInf_le_of_le (1 : ℝ)
      (iInf_le_of_le γ (iInf_le_of_le zero_le_one
        (iInf_le_of_le hγ.continuousOn
          (iInf_le_of_le (Set.image_subset_iff.mpr hA)
            (iInf_le_of_le hsep le_rfl))))))
  have hc0 : ENNReal.ofReal ((a : ℝ)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr a.property)).ne'
  have hct : ENNReal.ofReal ((a : ℝ)⁻¹) ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    (normalizedContLFPP ξ a φ).aroundDist A.toSet
        A.innerBoundary A.outerBoundary
        ≤ (normalizedContLFPP ξ a φ).len γ 0 1 := hle
    _ ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * lfppLen ξ φ γ :=
      normalizedContLFPP_len_le_lfppLen ξ a φ hγ
    _ < ENNReal.ofReal ((a : ℝ)⁻¹) * B :=
      by simpa only [mul_comm] using (ENNReal.mul_lt_mul_iff_left hc0 hct).2 hlen
    _ < L := hscaled

end SupercriticalLQGUniqueness.B2.DG20Lim
