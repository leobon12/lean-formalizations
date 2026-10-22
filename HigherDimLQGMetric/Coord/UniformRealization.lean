import HigherDimLQGMetric.Coord.Transfer

/-!
# Uniform local realization with a prescribed lower modulus

This is MA1 A5, Lemma 2.3′, in the form used by a compact configuration
family.  The modulus is the configuration bound `φ_m`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

/-- Lemma 2.3′: the lower modulus supplies a common boundary barrier and hence
one short-geodesic threshold for every member of the family and its limit. -/
theorem lemma23
    {X : Type*} [MetricSpace X]
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsLengthCoordinate (ρ n))
    (hconv : TendstoLocallyUniformly ρ ρlim atTop)
    (hmod : ∀ L : Set X, IsCompact L → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ L, ∀ v ∈ L,
        ρ n (u, v) < δ → dist u v < ε)
    {K O : Set X} (hKO : K ⊆ O) (hO : IsOpen O)
    (hOc : IsCompact (closure O))
    (φ : ℝ → ℝ) (hφmono : Monotone φ)
    (hφpos : ∀ ε : ℝ, 0 < ε → 0 < φ ε)
    (hφlower : ∀ n, ∀ u ∈ closure O, ∀ v ∈ closure O,
      φ (dist u v) ≤ ρ n (u, v))
    (η : ℝ) (hη : 0 < η)
    (hsep : ∀ x ∈ K, ∀ z ∈ frontier O, η ≤ dist x z) :
    (∀ n, ∀ x ∈ K, ∀ y ∈ K, ρ n (x, y) < φ η / 4 →
      ∃ Q : I →ᵇ X, (∀ t, Q t ∈ closure O) ∧ Q 0 = x ∧ Q 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
          (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal (ρ n (x, y))) ∧
    (∀ x ∈ K, ∀ y ∈ K, ρlim (x, y) < φ η / 4 →
      ∃ Q : I →ᵇ X, (∀ t, Q t ∈ closure O) ∧ Q 0 = x ∧ Q 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
          (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal (ρlim (x, y))) := by
  apply lemma22ii ρ ρlim hρ hconv hmod hKO hO hOc (hφpos η hη)
  intro n x hx z hz
  have hxO : x ∈ closure O := subset_closure (hKO hx)
  have hzO : z ∈ closure O := frontier_subset_closure hz
  exact (hφmono (hsep x hx z hz)).trans (hφlower n x hxO z hzO)

end HigherDimLQGMetric
