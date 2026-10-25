import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.JointCompact
import SupercriticalLQGUniqueness.B2.PfeAxioms.InternalConvergence

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem buffered_internal_liminf
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {V K U : Set ℂ} (hVK : V ⊆ K) (hK : IsCompact K) (hKU : K ⊆ U)
    (x y : ℕ → V) (x₀ y₀ : V)
    (hx : Tendsto (fun n => (x n : ℂ)) atTop (𝓝 (x₀ : ℂ)))
    (hy : Tendsto (fun n => (y n : ℂ)) atTop (𝓝 (y₀ : ℂ))) :
    D.internal U (⟨x₀, hKU (hVK x₀.property)⟩,
        ⟨y₀, hKU (hVK y₀.property)⟩) ≤
      liminf (fun n => (G n).internal V (x n, y n)) atTop := by
  let xK : ℕ → K := fun n => ⟨x n, hVK (x n).property⟩
  let yK : ℕ → K := fun n => ⟨y n, hVK (y n).property⟩
  let xK₀ : K := ⟨x₀, hVK x₀.property⟩
  let yK₀ : K := ⟨y₀, hVK y₀.property⟩
  have hcore : D.internal K (xK₀, yK₀) ≤
      liminf (fun n => (G n).internal K (xK n, yK n)) atTop := by
    rw [Uniqueness.Toolkit.MovingEndpoints.internal_compact_eq_compactPointInf]
    simpa only [Uniqueness.Toolkit.MovingEndpoints.internal_compact_eq_compactPointInf]
      using Uniqueness.Toolkit.MovingEndpoints.compactPathInf_seq_liminf_moving
        hG hK hx hy
  have hleft : D.internal U
      (⟨x₀, hKU (hVK x₀.property)⟩, ⟨y₀, hKU (hVK y₀.property)⟩) ≤
      D.internal K (xK₀, yK₀) := by
    rw [LSCMetric.internal_eq_internalEDist, LSCMetric.internal_eq_internalEDist]
    exact LQGMetric.MetricGeometry.internalEDist_anti (image_mono hKU) _ _
  have hright : ∀ n, (G n).internal K (xK n, yK n) ≤
      (G n).internal V (x n, y n) := by
    intro n
    rw [LSCMetric.internal_eq_internalEDist, LSCMetric.internal_eq_internalEDist]
    exact LQGMetric.MetricGeometry.internalEDist_anti (image_mono hVK) _ _
  calc
    _ ≤ D.internal K (xK₀, yK₀) := hleft
    _ ≤ liminf (fun n => (G n).internal K (xK n, yK n)) atTop := hcore
    _ ≤ liminf (fun n => (G n).internal V (x n, y n)) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall hright)

end SupercriticalLQGUniqueness.B2.PfeAxioms
