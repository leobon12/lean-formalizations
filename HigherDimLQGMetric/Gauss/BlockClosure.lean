import HigherDimLQGMetric.Gauss.BlockGeom

/-!
# Extending a correlation estimate to Hilbert-space closures

Separate continuity of the inner product preserves a uniform correlation
bound on the closures of two sets of generators.
-/

set_option autoImplicit false
namespace HigherDimLQGMetric

/-- A bilinear correlation estimate extends from generators to both closures. -/
theorem inner_abs_le_of_mem_closure {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {s t : Set H} {C : ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ t,
      |inner ℝ x y| ≤ C * (‖x‖ * ‖y‖)) :
    ∀ x ∈ closure s, ∀ y ∈ closure t,
      |inner ℝ x y| ≤ C * (‖x‖ * ‖y‖) := by
  have h₁ (y : H) (hy : y ∈ t) (x : H) (hx : x ∈ closure s) :
      |inner ℝ x y| ≤ C * (‖x‖ * ‖y‖) := by
    let U : Set H := {x | |inner ℝ x y| ≤ C * (‖x‖ * ‖y‖)}
    have hU : IsClosed U := by
      apply isClosed_le
      · fun_prop
      · fun_prop
    have hsub : s ⊆ U := by
      intro z hz
      exact h z hz y hy
    exact hU.closure_subset_iff.mpr hsub hx
  intro x hx y hy
  let U : Set H := {y | |inner ℝ x y| ≤ C * (‖x‖ * ‖y‖)}
  have hU : IsClosed U := by
    apply isClosed_le
    · fun_prop
    · fun_prop
  have hsub : t ⊆ U := by
    intro z hz
    exact h₁ z hz x hx
  exact hU.closure_subset_iff.mpr hsub hy
end HigherDimLQGMetric
