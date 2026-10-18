import MeshOnly.MeshOnlyHeatTiling

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal NNReal

namespace BouRabeeGwynne.MeshRates

/-- A finite mesh of a tiling of `ℝ^(n+1)` is positive: a cell has nonempty interior, hence two
distinct points, whose distance is at most the mesh. -/
lemma mesh_toReal_pos_of_ne_top {n : ℕ} (T : OrthogonalTiling (n + 1)) (hmesh : T.mesh ≠ ∞)
    (v : T.V) : 0 < T.mesh.toReal := by
  rcases (ENNReal.toReal_nonneg (a := T.mesh)).lt_or_eq with h | h
  · exact h
  exfalso
  have hsub : interior (T.cell v).carrier ⊆ {T.pos v} := by
    intro y hy
    have := T.toTilingData.dist_le_mesh (interior_subset hy)
      (interior_subset (T.pos_mem_interior v)) hmesh
    rw [← h] at this
    exact dist_le_zero.mp this
  have h2 := interior_mono hsub
  rw [interior_interior, interior_singleton] at h2
  exact (h2 (T.pos_mem_interior v))

/-- `meshOnly_cellVolume_toReal_pos` for every dimension (same proof; the original is stated only
for `OrthogonalTiling (n + 1)`, so it cannot be applied to a tiling of a variable dimension `d`). -/
lemma cellVolume_toReal_pos {d : ℕ} (T : OrthogonalTiling d) (v : T.V) :
    0 < (T.cell v).volume.toReal := by
  rw [ConvexPolytope.volume, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact ENNReal.toReal_pos
    (MeasureTheory.Measure.measure_pos_of_nonempty_interior _ (T.cell v).interior_nonempty).ne'
    (T.cell v).compact.measure_lt_top.ne

open Classical in
/-- MR Proposition 3.1: on-diagonal bound (30) and survival bound (31) for the chain (27) (rates
`a(v,w)/m_v`) killed on leaving the finite set `S`, inside a finite region `R` that contains every
neighbour of `S`; `P_x(τ_S > t)` is the time-`t` law of the absorbed chain charged on `S`. -/
theorem prop31_onDiagonal_and_survival {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : OrthogonalTiling d) (R : Set T.V) [Fintype R] [MeasurableSpace R]
      [MeasurableSingletonClass R] (S : Set R),
      T.mesh ≠ ∞ →
      (∀ v ∈ S, (T.cell v).carrier ⊆ interior T.domain) →
      (∀ v ∈ S, ∀ w : T.V, T.adj v w → w ∈ R) →
      ∀ x ∈ S,
        (∀ t : ℝ, 0 < t →
          (T.finiteNetwork R).killedHeatDensity (fun v : R => (T.cell v).volume.toReal) S x
              (2 * t) x ≤
            C * (t ^ (-(d : ℝ) / 2) + T.mesh.toReal ^ d * t ^ (-(d : ℝ)))) ∧
        (∀ t : ℝ≥0, T.mesh.toReal ^ 2 ≤ (t : ℝ) →
          ((T.finiteNetwork R).poissonizedUniformizedLaw (fun v : R => (T.cell v).volume.toReal)
              (fun v => cellVolume_toReal_pos T v) S x t S).toReal ≤
            C * Real.sqrt (∑ v : R, S.indicator (fun v => (T.cell v).volume.toReal) v) *
              (t : ℝ) ^ (-(d : ℝ) / 4)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨K, hK, hb⟩ := meshOnly_local_heat_and_survival hd
  refine ⟨K, hK, ?_⟩
  intro T R _ _ _ S hmesh hcell hnb x hx
  have hpos := mesh_toReal_pos_of_ne_top T hmesh (x : T.V)
  obtain ⟨h1, h2⟩ := hb T R S hmesh hcell hnb _ hpos le_rfl x hx
  exact ⟨h1, fun t ht => h2 t (lt_of_lt_of_le (by positivity) ht) ht⟩

end BouRabeeGwynne.MeshRates
