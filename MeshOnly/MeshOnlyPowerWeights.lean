import MeshOnly.MeshOnlyPowerConvolution
import MeshOnly.MeshOnlyPowerArzela
import MeshOnly.MeshOnlyPowerBumps
import MeshOnly.MeshOnlyPowerLimits

/-! Local power weights constructed from an orthogonal tiling. Mollification,
smooth Poincaré, a single compact-ball subsequence, and classical derivative
convergence on cell interiors supply the primitive; it is not a hypothesis. -/

open scoped NNReal Topology
open Filter

namespace BouRabeeGwynne.OrthogonalTiling

/-- A genuine local power primitive from mesh and a compact ambient collar. -/
theorem exists_meshOnly_local_power_primitive {n : ℕ}
    (T : OrthogonalTiling (n + 1)) (z : Euc (n + 1)) (r ρ : ℝ)
    (hρ : 0 < ρ) (hρr : ρ < r) (hmesh : T.mesh ≠ ⊤)
    (hcollar : Metric.closedBall z (r + T.mesh.toReal) ⊆ interior T.domain) :
    ∃ ψ : Euc (n + 1) → ℝ, ψ z = 0 ∧
      LipschitzWith (NNReal.mk (2 * T.mesh.toReal) (by positivity)) ψ ∧
      ∀ v, ∀ x ∈ interior (T.cell v).carrier ∩ Metric.ball z ρ,
        HasFDerivAt ψ (2 • innerSL ℝ (x - T.pos v)) x := by
  classical
  let R := T.meshOnlyBallCells z r
  have hRD : Metric.closedBall z r ⊆ T.domain := by
    intro x hx
    apply interior_subset (hcollar ?_)
    exact Metric.closedBall_subset_closedBall (le_add_of_nonneg_right ENNReal.toReal_nonneg) hx
  haveI : Fintype R := (T.meshOnlyBallCells_finite z r hRD).fintype
  let η := (ρ + r) / 2
  let δ := r - η
  have hρη : ρ < η := by dsimp [η]; linarith
  have hηr : η < r := by dsimp [η]; linarith
  have hδ : 0 < δ := sub_pos.mpr hηr
  let φ : ℕ → ContDiffBump (0 : Euc (n + 1)) := meshOnlyShrinkingBump δ hδ
  have hφ (k : ℕ) : (φ k).rOut + η ≤ r := by
    have h := meshOnlyShrinkingBump_rOut_le (d := n + 1) δ hδ k
    change (φ k).rOut ≤ δ at h
    dsimp [δ] at h
    linarith
  have hex (k : ℕ) := T.exists_meshOnly_mollified_primitive z r η hmesh hcollar (φ k) (hφ k)
  choose f hfzero hfderiv hflip using hex
  let C : ℝ≥0 := NNReal.mk (2 * T.mesh.toReal) (by positivity)
  have hsub : Metric.closedBall z ρ ⊆ Metric.ball z η :=
    Metric.closedBall_subset_ball hρη
  have hlip (k : ℕ) : LipschitzOnWith C (f k) (Metric.closedBall z ρ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := hflip k y (hsub hy) x (hsub hx)
    simpa only [C, NNReal.coe_mk, dist_eq_norm, Real.norm_eq_abs] using h
  obtain ⟨ψ, σ, hσ, hψlip, hψzero, hlim⟩ :=
    meshOnly_exists_lipschitz_ball_limit z ρ hρ.le C f hfzero hlip
  refine ⟨ψ, hψzero, hψlip, ?_⟩
  intro v x hx
  have hvR : v ∈ R := by
    refine ⟨x, interior_subset hx.1, ?_⟩
    exact Metric.closedBall_subset_closedBall hρr.le (Metric.ball_subset_closedBall hx.2)
  let a : R := ⟨v, hvR⟩
  have hradius : Tendsto (fun k => (φ (σ k)).rOut) atTop (𝓝 0) :=
    (meshOnlyShrinkingBump_rOut_tendsto (d := n + 1) δ hδ).comp hσ.tendsto_atTop
  have hfield := T.meshOnlyMollifiedDisplacement_tendstoLocallyUniformlyOn R a
    (fun k => φ (σ k)) hradius
  have hforms := (innerSL ℝ (E := Euc (n + 1))).uniformContinuous.comp_tendstoLocallyUniformlyOn
    (hfield.mono (Set.inter_subset_left (t := Metric.ball z ρ)))
  have hforms' : TendstoLocallyUniformlyOn
      (fun k => T.meshOnlyMollifiedPowerForm R (φ (σ k)))
      (fun y => 2 • innerSL ℝ (y - T.pos v)) atTop
      (interior (T.cell v).carrier ∩ Metric.ball z ρ) := by
    change TendstoLocallyUniformlyOn
      (fun k y => innerSL ℝ (T.meshOnlyMollifiedDisplacement R (φ (σ k)) y))
      (fun y => 2 • innerSL ℝ (y - T.pos v)) atTop
      (interior (T.cell v).carrier ∩ Metric.ball z ρ)
    simpa only [Function.comp_def, a, Subtype.coe_mk, two_smul, map_add] using hforms
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn (isOpen_interior.inter Metric.isOpen_ball)
    hforms'
    (fun k y hy => hfderiv (σ k) y (hsub (Metric.ball_subset_closedBall hy.2)))
    (fun y hy => hlim y (Metric.ball_subset_closedBall hy.2)) hx

/-- Power weights with the Euclidean mesh Lipschitz estimate, constructed from
actual orthogonal cells on a ball with a positive ambient margin. -/
theorem exists_meshOnly_local_power_weights {n : ℕ}
    (T : OrthogonalTiling (n + 1)) (z : Euc (n + 1)) (r ρ : ℝ)
    (hρ : 0 < ρ) (hρr : ρ < r) (hmesh : T.mesh ≠ ⊤)
    (hcollar : Metric.closedBall z (r + T.mesh.toReal) ⊆ interior T.domain) :
    ∃ ω : T.V → ℝ,
      (∀ v w, T.adj v w → T.pos v ∈ Metric.ball z ρ → T.pos w ∈ Metric.ball z ρ →
        (T.facet v w ∩ Metric.ball z ρ).Nonempty →
        ω w - ω v = T.powerEdgeGap v w) ∧
      (∀ v w, T.pos v ∈ Metric.ball z ρ → T.pos w ∈ Metric.ball z ρ →
        |ω w - ω v| ≤ (2 * T.mesh.toReal) * ‖T.pos w - T.pos v‖) := by
  obtain ⟨ψ, _, hψlip, hψderiv⟩ :=
    T.exists_meshOnly_local_power_primitive z r ρ hρ hρr hmesh hcollar
  apply T.exists_power_weights_of_primitive Metric.isOpen_ball (convex_ball z ρ)
    ψ hψlip.continuous.continuousOn hψderiv (2 * T.mesh.toReal)
  intro x _ y _
  simpa only [NNReal.coe_mk, dist_eq_norm, Real.norm_eq_abs] using hψlip.dist_le_mul y x

end BouRabeeGwynne.OrthogonalTiling
