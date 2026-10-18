import MeshRates.Corollary12.Section4BallExitConvergence
import MeshRates.Corollary12.BallDirichlet
import MeshRates.Corollary12.LevyProkhorovCompact
import MeshRates.Statement.Corollary12

/-! Harmonic-measure part of MR Corollary 1.2 (BRG Proposition 4.2), uniform over all interior
vertices of the ball. Follows BRG `eventually_ball_exit_levyProkhorov_error` with the compact
starting set replaced by compactness of the probability measures carried by the closed ball. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical BoundedContinuousFunction

namespace BouRabeeGwynne.MeshRates

theorem corollary12_harmonicMeasure : MeshRatesCorollary12HarmonicMeasureStatement := by
  intro d hd2 G N happrox c r hr hUD μ hμ ε hε
  have hd : 1 ≤ d := by omega
  have hD : BallDirichletInput G := ballDirichletInput_of_meshConverges hd2 (N.mesh_tendsto_zero happrox)
  let V : ℕ → Type _ := fun n => {v : (G.tiling n).V //
    v ∈ (G.tiling n).interiorVertices (Metric.ball c r)}
  let ν : ∀ n, V n → ProbabilityMeasure (Euc d) := fun n v =>
    brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball μ hμ ((G.tiling n).pos v)
  let μd : ∀ n, V n → ProbabilityMeasure (Euc d) := fun n v =>
    if hg : (G.tiling n).HasFiniteAccessibleRegion (Metric.ball c r) then
      (G.tiling n).spatialExitProbability (Metric.ball c r) hg v
        ((G.tiling n).interiorVertices_subset_closedVertices _ v.property)
    else ν n v
  have hcar : ∀ n (v : V n), ν n v (Metric.closedBall c r)ᶜ = 0 := by
    intro n v
    have hmem : (G.tiling n).pos v.val ∈ Metric.ball c r :=
      v.property
    have hae := brownianSpatialHarmonicMeasure_ae_mem_frontier hd hμ Metric.isOpen_ball
      Metric.isBounded_ball hmem
    have h0 : (ν n v : Measure (Euc d)) (Metric.closedBall c r)ᶜ = 0 := by
      refine measure_mono_null (fun x hx => ?_) (ae_iff.mp hae)
      intro hfr
      exact hx (Metric.sphere_subset_closedBall (Metric.frontier_ball_subset_sphere hfr))
    exact (ProbabilityMeasure.null_iff_toMeasure_null _ _).mpr h0
  have hgood : ∀ᶠ n in atTop,
      (G.tiling n).HasFiniteAccessibleRegion (Metric.ball c r) := by
    filter_upwards [eventually_ball_exit_test_error_of_ballDirichlet hd G N c hr hUD happrox hD hμ
      (fun _ => 0) continuous_const zero_lt_one] with n hn
    obtain ⟨hfin, ha, _⟩ := hn
    exact ⟨hfin, ha⟩
  have htest : ∀ f : Euc d →ᵇ ℝ, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      ∀ v : V n, |(∫ x, f x ∂(μd n v : Measure (Euc d))) -
        ∫ x, f x ∂(ν n v : Measure (Euc d))| < η := by
    intro f η hη
    filter_upwards [hgood, eventually_ball_exit_test_error_of_ballDirichlet hd G N c hr hUD
      happrox hD hμ f f.continuous (half_pos hη)] with n hg hn
    obtain ⟨hfin, hdata⟩ := hn
    letI : Fintype ((G.tiling n).closedVertices (Metric.ball c r)) := hfin.fintype
    letI : MeasurableSpace ((G.tiling n).closedVertices (Metric.ball c r)) := ⊤
    obtain ⟨ha, hbound⟩ := hdata
    intro v
    let vr : (G.tiling n).closedVertices (Metric.ball c r) :=
      ⟨v.val, (G.tiling n).interiorVertices_subset_closedVertices _ v.property⟩
    have herr := (hbound vr v.property).trans_lt (half_lt_self hη)
    simpa only [μd, dif_pos hg,
      (G.tiling n).spatialExitProbability_eq _ hg hfin _ _ ha, ν, vr] using herr
  have hLP := uniform_levyProkhorovDist_of_uniform_test_error_carried
    (isCompact_closedBall c r) V μd ν hcar htest
  filter_upwards [hgood, hLP ε hε] with n hg hn
  refine ⟨hg, ?_⟩
  intro v hv
  simpa only [μd, dif_pos hg, ν] using hn ⟨v, hv⟩

end BouRabeeGwynne.MeshRates
