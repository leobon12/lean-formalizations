import HigherDimLQGMetric.Coord.LemmaCC
import LQGMetric.Metric.LengthLimit

/-!
# Metric axioms in a coordinate limit

The first part of MA1 Lemma 2.2′(i).  A compact lower modulus prevents distinct
points from collapsing in a pointwise limit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry

namespace HigherDimLQGMetric

/-- The limit of coordinate metrics is a metric if every compact set has the uniform
lower modulus of MA1 A3.  This includes the separation argument missing from a bare
pointwise limit of metrics. -/
theorem isMetricFun_of_uniformLowerModulus
    {X : Type*} [MetricSpace X] (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsMetricFun (ρ n))
    (hconv : ∀ x y, Tendsto (fun n => ρ n (x, y)) atTop (𝓝 (ρlim (x, y))))
    (hmod : ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ x ∈ K, ∀ y ∈ K,
        ρ n (x, y) < δ → dist x y < ε) :
    IsMetricFun ρlim := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    have hzero : Tendsto (fun n => ρ n (x, x)) atTop (𝓝 (0 : ℝ)) := by
      have heq : (fun n => ρ n (x, x)) = fun _ : ℕ => (0 : ℝ) :=
        funext fun n => (hρ n).self_eq_zero x
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hconv x x) hzero
  · intro x y hzero
    by_contra hne
    have hxy : 0 < dist x y := dist_pos.mpr hne
    let K : Set X := {x, y}
    obtain ⟨δ, hδ, hδmod⟩ := hmod K (Set.Finite.isCompact (by simp [K])) (dist x y) hxy
    have hbound : ∀ n, δ ≤ ρ n (x, y) := by
      intro n
      by_contra hnot
      have hsmall := hδmod n x (by simp [K]) y (by simp [K]) (lt_of_not_ge hnot)
      exact (lt_irrefl (dist x y)) hsmall
    have hlimbound : δ ≤ ρlim (x, y) :=
      ge_of_tendsto (hconv x y) (Eventually.of_forall hbound)
    exact (lt_of_lt_of_le hδ hlimbound).ne hzero.symm
  · intro x y
    have heq : (fun n => ρ n (x, y)) = (fun n => ρ n (y, x)) :=
      funext fun n => (hρ n).symm x y
    exact tendsto_nhds_unique (heq ▸ hconv x y) (hconv y x)
  · intro x y z
    exact le_of_tendsto_of_tendsto' (hconv x z)
      ((hconv x y).add (hconv y z)) (fun n => (hρ n).triangle x y z)

/-- The same compact lower modulus works for the limit coordinate. -/
theorem uniformLowerModulus_limit
    {X : Type*} [MetricSpace X] (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hconv : ∀ x y, Tendsto (fun n => ρ n (x, y)) atTop (𝓝 (ρlim (x, y))))
    (hmod : ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ x ∈ K, ∀ y ∈ K,
        ρ n (x, y) < δ → dist x y < ε)
    (K : Set X) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ K,
      ρlim (x, y) < δ → dist x y < ε := by
  obtain ⟨δ, hδ, hδmod⟩ := hmod K hK ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hlt
  obtain ⟨n, hn⟩ := ((hconv x y).eventually (gt_mem_nhds hlt)).exists
  exact hδmod n x hx y hy hn

end HigherDimLQGMetric
