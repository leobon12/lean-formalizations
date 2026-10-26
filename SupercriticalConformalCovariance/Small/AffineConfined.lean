import SupercriticalConformalCovariance.Small.ConfinedScale

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness

/-- The diagonal-corrected intrinsic kernel transforms under any similarity
of lower-semicontinuous metrics, including outside its carrier. -/
theorem extendMetric_internal_affine
    {Dorig Dzoom : LSCMetric} (F : ℂ ≃ ℂ) {s : ℝ≥0∞}
    (hs0 : s ≠ 0) (hst : s ≠ ⊤)
    (h : ∀ u v : ℂ, Dzoom (u,v) = s * Dorig (F u,F v))
    (A : Set ℂ) (x y : ℂ) :
    extendMetric (F.symm '' A)
      (Dzoom.internal (F.symm '' A)) (F.symm x,F.symm y) =
      s * extendMetric A (Dorig.internal A) (x,y) := by
  by_cases hxy : x = y
  · subst y
    simp [extendMetric]
  have hxy' : F.symm x ≠ F.symm y := F.symm.injective.ne hxy
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ A
    · have hxx : F.symm x ∈ F.symm '' A := ⟨x,hx,rfl⟩
      have hyy : F.symm y ∈ F.symm '' A := ⟨y,hy,rfl⟩
      rw [extendMetric_on _ _ (Dzoom.isExtMetric_internal _) hxx hyy,
        extendMetric_on _ _ (Dorig.isExtMetric_internal _) hx hy]
      exact internal_of_rescaled_pointwise F hs0 hst h A (⟨x,hx⟩) (⟨y,hy⟩)
    · have hno : ¬ (F.symm x ∈ F.symm '' A ∧ F.symm y ∈ F.symm '' A) := by
        rintro ⟨_,⟨t,ht,heq⟩⟩
        exact hy (Eq.mp (congrArg (· ∈ A) (F.symm.injective heq)) ht)
      rw [extendMetric_off _ _ hxy' hno,
        extendMetric_off _ _ hxy (by simp [hy])]
      simp [hs0]
  · have hno : ¬ (F.symm x ∈ F.symm '' A ∧ F.symm y ∈ F.symm '' A) := by
      rintro ⟨⟨t,ht,heq⟩,_⟩
      exact hx (Eq.mp (congrArg (· ∈ A) (F.symm.injective heq)) ht)
    rw [extendMetric_off _ _ hxy' hno,
      extendMetric_off _ _ hxy (by simp [hx])]
    simp [hs0]

/-- Pulling the confined target metric back along a map commutes with the
target affine zoom. -/
theorem pullback_extendMetric_internal_affine
    {Dorig Dzoom : LSCMetric} (B : ℂ ≃ ℂ) {s : ℝ≥0∞}
    (hs0 : s ≠ 0) (hst : s ≠ ⊤)
    (h : ∀ u v : ℂ, Dzoom (u,v) = s * Dorig (B u,B v))
    (A : Set ℂ) (φ ψ : ℂ → ℂ)
    (hψ : ∀ w, ψ w = B.symm (φ w)) (u v : ℂ) :
    extendMetric (B.symm '' A)
      (Dzoom.internal (B.symm '' A)) (ψ u,ψ v) =
      s * extendMetric A (Dorig.internal A) (φ u,φ v) := by
  rw [hψ u,hψ v]
  exact extendMetric_internal_affine B hs0 hst h A (φ u) (φ v)

end SupercriticalConformalCovariance.Small
