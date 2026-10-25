import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAroundFourSector

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
theorem crossLenIn_le_of_singleton_endpoints
    (ξ : ℝ) (f : ℂ → ℝ) (U K₁ K₂ : Set ℂ) (z w : ℂ)
    (hz : z ∈ K₁) (hw : w ∈ K₂) :
    crossLenIn ξ f U K₁ K₂ ≤ crossLenIn ξ f U {z} {w} := by
  unfold crossLenIn
  calc
    (⨅ x ∈ K₁, ⨅ y ∈ K₂,
      ⨅ P : {P : ℝ → ℂ // IsPiecewiseC1Path P x y ∧
        ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ U}, lfppLen ξ f P.1)
        ≤ ⨅ P : {P : ℝ → ℂ // IsPiecewiseC1Path P z w ∧
          ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ U}, lfppLen ξ f P.1 :=
      iInf₂_le_of_le z hz (iInf₂_le w hw)
    _ = (⨅ x ∈ ({z} : Set ℂ), ⨅ y ∈ ({w} : Set ℂ),
        ⨅ P : {P : ℝ → ℂ // IsPiecewiseC1Path P x y ∧
          ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ U}, lfppLen ξ f P.1) := by simp

 

theorem lfppContMetric_aroundDist_lt_of_four_point_crossLen
    (A : EuclideanAnnulus) (ξ : ℝ) (φ : ℂ → ℝ) (hφ : Continuous φ)
    (z w : Fin 4 → ℂ)
    (hz : ∀ j, z j ∈ B2.Strong.cfgSet₁ A j)
    (hw : ∀ j, w j ∈ B2.Strong.cfgSet₂ A j)
    (a₀ a₁ a₂ a₃ L : ℝ≥0∞)
    (h₀ : crossLenIn ξ φ (B2.Strong.cfgOpens A 0 : Set ℂ)
      {z 0} {w 0} < a₀)
    (h₁ : crossLenIn ξ φ (B2.Strong.cfgOpens A 1 : Set ℂ)
      {z 1} {w 1} < a₁)
    (h₂ : crossLenIn ξ φ (B2.Strong.cfgOpens A 2 : Set ℂ)
      {z 2} {w 2} < a₂)
    (h₃ : crossLenIn ξ φ (B2.Strong.cfgOpens A 3 : Set ℂ)
      {z 3} {w 3} < a₃)
    (hbudget : a₀ + a₁ + a₂ + a₃ < L) :
    (lfppContMetric ξ φ hφ).aroundDist A.toSet
      A.innerBoundary A.outerBoundary < L := by
  apply lfppContMetric_aroundDist_lt_of_four_crossLen A ξ φ hφ
    a₀ a₁ a₂ a₃ L
  · exact (crossLenIn_le_of_singleton_endpoints ξ φ _ _ _ _ _ (hz 0) (hw 0)).trans_lt h₀
  · exact (crossLenIn_le_of_singleton_endpoints ξ φ _ _ _ _ _ (hz 1) (hw 1)).trans_lt h₁
  · exact (crossLenIn_le_of_singleton_endpoints ξ φ _ _ _ _ _ (hz 2) (hw 2)).trans_lt h₂
  · exact (crossLenIn_le_of_singleton_endpoints ξ φ _ _ _ _ _ (hz 3) (hw 3)).trans_lt h₃
  · exact hbudget

end SupercriticalLQGUniqueness.B2.DG20Lim
