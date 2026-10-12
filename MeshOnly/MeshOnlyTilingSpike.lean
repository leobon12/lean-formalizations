import MeshOnly.MeshOnlyHeatTiling
import MeshOnly.MeshOnlyFiniteSpike
import MeshOnly.MeshOnlyTilingClock
import MeshOnly.MeshOnlySpikeScales

/-! The quantitative spike contradiction for the actual tiling-volume walk.
This combines the proved heat, clock, and harmonic mean-value estimates on
the same absorbed region, at the time prescribed by the actual mesh. -/

open MeasureTheory
open scoped Classical BigOperators NNReal ENNReal

namespace BouRabeeGwynne

theorem meshOnly_tiling_spike_bound {n : ℕ} (hd : 2 ≤ n + 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : OrthogonalTiling (n + 1))
      (R : Set T.V) [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
      (A : Set R) (f g : R → ℝ) (x : R) (α H E r : ℝ),
      0 < α → 0 ≤ H → 0 ≤ E → 0 < r → T.mesh ≠ ∞ →
      0 < T.mesh.toReal → T.mesh.toReal ≤ 1 → 2 * T.mesh.toReal < r →
      Metric.closedBall (T.pos x) (3 * r + T.mesh.toReal) ⊆ interior T.domain →
      (∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain) →
      (∀ v ∈ A, ∀ w : T.V, T.adj v w → w ∈ R) →
      (∀ v, v ∉ A → f v = g v) →
      (∀ v ∈ A, (T.finiteNetwork R).laplacian f v = 0) →
      -H ≤ g x → (∀ w, f w ≤ H) → g x + α ≤ f x →
      (∀ w : R, dist (T.pos w) (T.pos x) < r → g w - g x ≤ α / 4) →
      (∑ v : R, (T.cell v).volume.toReal * (f v - g v) ^ 2) ≤
        E * T.mesh.toReal ^ 2 →
      (α / 4) / (2 * H + 3 * α / 4) ≤
        K * Real.sqrt ((4 / α ^ 2) * E) * T.mesh.toReal ^ (1 / 2 : ℝ) +
          (2 * ((n + 1 : ℕ) : ℝ) * T.mesh.toReal ^ (2 / ((n + 1 : ℕ) : ℝ)) +
            2 * T.mesh.toReal * (r + 2 * T.mesh.toReal)) / r ^ 2 := by
  obtain ⟨K, hK, hheat⟩ := meshOnly_local_heat_and_survival hd
  refine ⟨K, hK, ?_⟩
  intro T R _ _ _ A f g x α H E r hα hH hE hr hmesh hε hε1 hsmall
    hcollar hcell hneighbors hboundary hharmonic hbase hmax hspike hosc hL2
  let ε := T.mesh.toReal
  let m : R → ℝ := fun v => (T.cell v).volume.toReal
  have hm : ∀ v, 0 < m v := fun v => T.meshOnly_cellVolume_toReal_pos v
  let N := T.finiteNetwork R
  let ρ : R → ℝ := fun v => dist (T.pos v) (T.pos x)
  let C := meshOnlySpikeRegion f g ρ α r
  have hCA : C ⊆ A := by
    intro v hv
    by_contra hout
    have hzero := hboundary v hout
    have hgap : α / 2 < f v - g v := hv.1
    rw [hzero, sub_self] at hgap
    linarith
  have hx : x ∈ C := by
    constructor
    · linarith
    · simpa only [ρ, dist_self] using hr
  let t : ℝ≥0 := NNReal.mk (ε ^ (2 / ((n + 1 : ℕ) : ℝ)))
    (Real.rpow_nonneg hε.le _)
  have ht : (t : ℝ) = ε ^ (2 / ((n + 1 : ℕ) : ℝ)) := rfl
  have htpos : 0 < (t : ℝ) := by rw [ht]; exact Real.rpow_pos_of_pos hε _
  have htmesh : ε ^ 2 ≤ (t : ℝ) := by
    rw [ht]
    exact mesh_only_time_ge_square hd hε hε1
  let μ := N.poissonizedUniformizedLaw m hm C x t
  have hsurvival := (hheat T R C hmesh
    (fun v hv => hcell v (hCA hv))
    (fun v hv => hneighbors v (hCA hv)) ε hε le_rfl x hx).2 t htpos htmesh
  change (μ C).toReal ≤ K * Real.sqrt (∑ v, C.indicator m v) *
    (t : ℝ) ^ (-((n + 1 : ℕ) : ℝ) / 4) at hsurvival
  let D := (4 / α ^ 2) * E
  have hD : 0 ≤ D := mul_nonneg (by positivity) hE
  have hmass : (∑ v, C.indicator m v) ≤ D * ε ^ 2 := by
    apply (meshOnly_spikeRegion_mass_le m f g ρ (fun v => (hm v).le) hα r).trans
    simpa only [D, ε, mul_assoc] using
      mul_le_mul_of_nonneg_left hL2 (by positivity : 0 ≤ 4 / α ^ 2)
  have hsqrt : Real.sqrt (∑ v, C.indicator m v) ≤ Real.sqrt D * ε := by
    calc
      _ ≤ Real.sqrt (D * ε ^ 2) := Real.sqrt_le_sqrt hmass
      _ = _ := by rw [Real.sqrt_mul hD, Real.sqrt_sq hε.le]
  have hsurvival' : (μ C).toReal ≤ K * Real.sqrt D * ε ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ K * Real.sqrt (∑ v, C.indicator m v) *
          (ε ^ (2 / ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ) / 4) := by
        simpa only [ht] using hsurvival
      _ ≤ K * (Real.sqrt D * ε) *
          (ε ^ (2 / ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hK.le)
          (Real.rpow_nonneg (Real.rpow_nonneg hε.le _) _)
      _ = K * Real.sqrt D * ε ^ (1 / 2 : ℝ) := by
        rw [mul_assoc, mul_assoc, mesh_only_survival_scale hd hε, ← mul_assoc]
  have hcrossing := T.meshOnly_local_ball_crossing_le R C x hr hmesh hsmall hcollar
    (fun v hv => hv.2) (fun v hv => hneighbors v (hCA hv)) t
  have hlower := N.poissonizedUniformizedLaw_spike_lower_bound m hm f g ρ
    hα hH r x hbase hmax hspike hosc (fun v hv => hharmonic v (hCA hv)) t
  change (α / 4) / (2 * H + 3 * α / 4) ≤
    (μ C).toReal + (μ {w | r ≤ ρ w}).toReal at hlower
  exact hlower.trans (add_le_add hsurvival' (by simpa only [ht] using hcrossing))

end BouRabeeGwynne
