import HigherDimLQGMetric.Weak.DetInternalTight

/-!
# Deterministic internal metric facts

Adapters for the internal-distance continuity and locality results already proved in
`HigherDimLQGMetric`.
-/

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped ENNReal

namespace HigherDimLFPPAS.Det

open HigherDimLFPPAS
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- On a connected open set, the internal distance of a continuous length metric is finite and
continuous as a real-valued function on pairs of points in the set. -/
theorem internal_finite_continuous
    (D : ContMetric d) (hD : D.IsLength) {U : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsConnected U) :
    (∀ x ∈ U, ∀ y ∈ U, D.internal U x y ≠ ∞) ∧
      ContinuousOn (fun p : Rd d × Rd d => (D.internal U p.1 p.2).toReal) (U ×ˢ U) := by
  have hfinite : ∀ x ∈ U, ∀ y ∈ U, D.internal U x y ≠ ∞ := by
    intro x hx y hy
    exact D.internal_ne_top_of_isPreconnected hD hU hUc.isPreconnected hx hy
  have hC := (internalC D hD hU hUc.isPreconnected).continuous
  have hcont : ContinuousOn (fun p : Rd d × Rd d => (D.internal U p.1 p.2).toReal)
      (U ×ˢ U) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let e : {p : Rd d × Rd d // p ∈ U ×ˢ U} → U × U := fun p =>
      (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
    have he₁ : Continuous (fun p : {q : Rd d × Rd d // q ∈ U ×ˢ U} =>
        (⟨p.1.1, p.2.1⟩ : U)) :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk (fun p => p.2.1)
    have he₂ : Continuous (fun p : {q : Rd d × Rd d // q ∈ U ×ˢ U} =>
        (⟨p.1.2, p.2.2⟩ : U)) :=
      (continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.2.2)
    have he : Continuous e := he₁.prodMk he₂
    change Continuous (fun p : {q : Rd d × Rd d // q ∈ U ×ˢ U} =>
      (D.internal U p.1.1 p.1.2).toReal)
    rw [show (fun p : {q : Rd d × Rd d // q ∈ U ×ˢ U} =>
        (D.internal U p.1.1 p.1.2).toReal) =
        (⇑(internalC D hD hU hUc.isPreconnected)) ∘ e by
          funext p
          rfl]
    exact hC.comp he
  exact ⟨hfinite, hcont⟩

/-- At each point of an open set, sufficiently close points have the same global and internal
distance for a continuous length metric. -/
theorem internal_eq_global_near
    (D : ContMetric d) (hD : D.IsLength) {U : Set (Rd d)}
    (hU : IsOpen U) {x : Rd d} (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ y : Rd d, D.1 (x, y) < r →
      D.internal U x y = ENNReal.ofReal (D.1 (x, y)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (D.isOpen_image_pt hU) (D.pt x)
    ⟨x, hx, rfl⟩
  refine ⟨ε, hε, fun y hy => ?_⟩
  have hballU : ∀ z : Rd d, D.1 (x, z) < ε → z ∈ U := by
    intro z hz
    apply D.mem_image_pt.1
    apply hball
    rw [Metric.mem_ball, D.dist_pt, D.apply_comm]
    exact hz
  exact D.internal_eq_of_ball_subset hD hballU hy

end HigherDimLFPPAS.Det

