import SupercriticalConformalCovariance.Small.ConfinedLSC
import SupercriticalConformalCovariance.Small.TargetConfinedLSC
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness

/-- Any curve of an extended metric supported on a compact set has bounded
Euclidean trace, even if its starting point is outside the support. -/
theorem euclidean_regular_of_compact_support
    (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K)
    (hoff : ∀ x y : ℂ, x ≠ y → ¬ (x ∈ K ∧ y ∈ K) → D (x,y) = ⊤)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b) :
    ContinuousOn P (Icc a b) := by
  have htrace : P '' Icc a b ⊆ insert (P a) K := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases hEq : P t = P a
    · exact Or.inl hEq
    · right
      have hsub : D.IsCurve P a t := by
        refine ⟨ht.1, hP.2.mono ?_⟩
        intro s hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      have hfin : D (P a,P t) < ⊤ := hsub.apply_lt_top
      by_contra hnot
      have htop := hoff (P a) (P t) (Ne.symm hEq) (fun hpair => hnot hpair.2)
      rw [htop] at hfin
      exact (lt_irrefl (⊤ : ℝ≥0∞)) hfin
  exact SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.continuousOn_euclidean_of_compact_trace
    D P hP (hK.insert (P a)) htrace

theorem conf_euclidean_regular_any
    (D : LSCMetric) (c : ℂ) (R : ℝ)
    (P : ℝ → ℂ) (a b : ℝ) (hP : (conf D c R).IsCurve P a b) :
    ContinuousOn P (Icc a b) := by
  apply euclidean_regular_of_compact_support (conf D c R)
    (closedBall c R) (isCompact_closedBall c R) ?_ P a b hP
  intro x y hxy h
  exact confKernel_outside D c R hxy h

theorem confPullCompact_euclidean_regular_any
    (D : LSCMetric) (L K : Set ℂ) (hK : IsCompact K)
    (hL : IsCompact L) (j : C(K,L)) (hj : Function.Injective j)
    (P : ℝ → ℂ) (a b : ℝ)
    (hP : (confPullCompact D L K hK hL j hj).IsCurve P a b) :
    ContinuousOn P (Icc a b) := by
  apply euclidean_regular_of_compact_support
    (confPullCompact D L K hK hL j hj) K hK ?_ P a b hP
  intro x y hxy h
  exact extendMetric_off K (pullInner D L K j) hxy h

end SupercriticalConformalCovariance.Small
