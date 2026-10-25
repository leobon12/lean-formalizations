import SupercriticalLQGUniqueness.B2.DG20Pt.AroundFourCrossing
import LQGMetric.LFPP.Length

 

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem lfppContMetric_aroundDist_lt_of_four_crossLen
    (A : EuclideanAnnulus) (ξ : ℝ) (φ : ℂ → ℝ) (hφ : Continuous φ)
    (a₀ a₁ a₂ a₃ L : ℝ≥0∞)
    (h₀ : crossLenIn ξ φ (B2.Strong.cfgOpens A 0 : Set ℂ)
      (B2.Strong.cfgSet₁ A 0) (B2.Strong.cfgSet₂ A 0) < a₀)
    (h₁ : crossLenIn ξ φ (B2.Strong.cfgOpens A 1 : Set ℂ)
      (B2.Strong.cfgSet₁ A 1) (B2.Strong.cfgSet₂ A 1) < a₁)
    (h₂ : crossLenIn ξ φ (B2.Strong.cfgOpens A 2 : Set ℂ)
      (B2.Strong.cfgSet₁ A 2) (B2.Strong.cfgSet₂ A 2) < a₂)
    (h₃ : crossLenIn ξ φ (B2.Strong.cfgOpens A 3 : Set ℂ)
      (B2.Strong.cfgSet₁ A 3) (B2.Strong.cfgSet₂ A 3) < a₃)
    (hbudget : a₀ + a₁ + a₂ + a₃ < L) :
    (lfppContMetric ξ φ hφ).aroundDist A.toSet
      A.innerBoundary A.outerBoundary < L := by
  obtain ⟨γ, u, v, hγ, hA, hsep, hlen⟩ :=
    B2.DG20Pt.around_loop_of_four_crossLen
      A ξ φ a₀ a₁ a₂ a₃ L h₀ h₁ h₂ h₃ hbudget
  have hle :
      (lfppContMetric ξ φ hφ).aroundDist A.toSet
        A.innerBoundary A.outerBoundary ≤
      (lfppContMetric ξ φ hφ).len γ 0 1 := by
    unfold ContMetric.aroundDist
    exact iInf_le_of_le (0 : ℝ) (iInf_le_of_le (1 : ℝ)
      (iInf_le_of_le γ (iInf_le_of_le zero_le_one
        (iInf_le_of_le hγ.continuousOn
          (iInf_le_of_le (Set.image_subset_iff.mpr hA)
            (iInf_le_of_le hsep le_rfl))))))
  have hlenD : (lfppContMetric ξ φ hφ).len γ 0 1 ≤
      lfppLen ξ φ γ := by
    simpa only [lfppLen_eq] using
      (len_le_lfppLen hφ hγ le_rfl le_rfl :
        (lfppContMetric ξ φ hφ).len γ 0 1 ≤
          ∫⁻ τ in Icc (0 : ℝ) 1, lenDens ξ φ γ τ)
  exact hle.trans_lt (hlenD.trans_lt hlen)

end SupercriticalLQGUniqueness.B2.DG20Lim
