import MeshOnly.MeshOnlyLocalization

/-! A single radius and mesh index for the uniform spike argument.
The existing compact-collar localization supplies all geometric inclusions. -/

open scoped Classical Topology ENNReal

namespace BouRabeeGwynne.TilingSequence

theorem exists_meshOnly_uniform_radius {d : ℕ} (G : TilingSequence d)
    (hmesh : G.MeshConverges) {U W : Set (Euc d)}
    (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain)
    (hW : IsOpen W) (hUW : closure U ⊆ W) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ M * r ≤ η / 4 ∧
      (∀ z ∈ U, Metric.ball z r ⊆ W) ∧
      ∀ᶠ k in Filter.atTop,
        (G.tiling k).mesh ≠ ∞ ∧ (G.tiling k).mesh.toReal ≤ 1 ∧
        2 * (G.tiling k).mesh.toReal < r ∧
        (∀ z ∈ U, Metric.closedBall z (3 * r + (G.tiling k).mesh.toReal) ⊆
          interior (G.tiling k).domain) ∧
        ∀ v ∈ (G.tiling k).closedVertices U,
          (G.tiling k).pos v ∈ W ∧
          ((G.tiling k).cell v).carrier ⊆ interior (G.tiling k).domain := by
  obtain ⟨ρ, hρ, hρQ⟩ := hU.isCompact_closure.exists_cthickening_subset_open
    (hW.inter isOpen_interior) (fun x hx => ⟨hUW hx, hUD hx⟩)
  let Q := Metric.cthickening ρ (closure U)
  let r := min (ρ / 8) (η / (4 * (M + 1)))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrρ : r ≤ ρ / 8 := min_le_left _ _
  have hrM : r * (4 * (M + 1)) ≤ η :=
    (le_div_iff₀ (by positivity : 0 < 4 * (M + 1))).mp (min_le_right _ _)
  refine ⟨r, hr, by nlinarith, ?_, ?_⟩
  · intro z hz
    exact Metric.ball_subset_closedBall.trans
      ((Metric.closedBall_subset_cthickening (subset_closure hz) r).trans
        ((Metric.cthickening_mono (by linarith : r ≤ ρ) (closure U)).trans
          (fun y hy => (hρQ hy).1)))
  filter_upwards [G.eventually_mesh_finite_le hmesh (by positivity : 0 < r / 4),
    G.eventually_mesh_finite_le hmesh zero_lt_one,
    G.eventually_closedRegion_in_compact_collar hmesh hρ (Q := Q) Set.Subset.rfl]
    with k hsmall hone hclosed
  refine ⟨hsmall.1, hone.2, by linarith [hsmall.2], ?_, ?_⟩
  · intro z hz
    have hrad : 3 * r + (G.tiling k).mesh.toReal ≤ ρ := by linarith [hsmall.2]
    have hsub := (Metric.closedBall_subset_cthickening (subset_closure hz)
      (3 * r + (G.tiling k).mesh.toReal)).trans
      ((Metric.cthickening_mono hrad (closure U)).trans (fun y hy => (hρQ hy).2))
    simpa only [G.common_domain k] using hsub
  · intro v hv
    have hcell := (hclosed.2 v hv).1
    refine ⟨(hρQ (hcell (interior_subset ((G.tiling k).pos_mem_interior v)))).1, ?_⟩
    simpa only [G.common_domain k] using
      hcell.trans (fun y hy => (hρQ hy).2)

end BouRabeeGwynne.TilingSequence
