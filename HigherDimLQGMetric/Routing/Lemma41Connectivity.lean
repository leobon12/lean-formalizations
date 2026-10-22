import HigherDimLQGMetric.Routing.Lemma41Trim
import HigherDimLQGMetric.Coord.LimitTopology
import LQGMetric.Metric.LengthSpace
import Mathlib.Topology.Connected.Clopen

/-!
# Rectifiable connectivity in a routing region

Local finite-length realizers propagate over a preconnected region by the open-and-closed
reachability argument. This is the analytic part of the routing argument in Lemma 4.1′.
-/

set_option autoImplicit false

open Set Filter Topology LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

/-- Local finite-length coordinate paths connect every pair in a preconnected region. -/
theorem lemma41_rectifiable_connected
    {X : Type*} [MetricSpace X] (ρ : X × X → ℝ) (hρ : IsCoordinate ρ)
    {A : Set X} (hA : IsPreconnected A)
    (hlocal : ∀ x ∈ A, ∀ᶠ y in 𝓝[A] x,
      ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
          (MetricFunSpace.pt ρ hρ.metric y),
        (∀ t, LQGMetric.metricFunSpaceVal ρ hρ.metric (P t) ∈ A) ∧
        pathLength P ≠ ∞)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
    ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
        (MetricFunSpace.pt ρ hρ.metric y),
      (∀ t, LQGMetric.metricFunSpaceVal ρ hρ.metric (P t) ∈ A) ∧
      pathLength P ≠ ∞ := by
  let R : X → X → Prop := fun x y =>
    ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
        (MetricFunSpace.pt ρ hρ.metric y),
      (∀ t, LQGMetric.metricFunSpaceVal ρ hρ.metric (P t) ∈ A) ∧
      pathLength P ≠ ∞
  have hnear (z : X) (hz : z ∈ A) : ∀ᶠ w in 𝓝[A] z, R z w ∧ R w z := by
    filter_upwards [hlocal z hz] with w ⟨P, hPA, hPfin⟩
    refine ⟨⟨P, hPA, hPfin⟩, ⟨P.symm, ?_, ?_⟩⟩
    · intro t
      rw [Path.symm_apply]
      exact hPA _
    · rwa [pathLength_symm]
  have htrans : ∀ a b c : X, a ∈ A → b ∈ A → c ∈ A →
      R a b → R b c → R a c := by
    intro a b c _ _ _ ⟨P, hPA, hPfin⟩ ⟨Q, hQA, hQfin⟩
    refine ⟨P.trans Q, ?_, ?_⟩
    · intro t
      rw [Path.trans_apply]
      split_ifs
      · exact hPA _
      · exact hQA _
    · rw [pathLength_trans]
      exact ENNReal.add_ne_top.mpr ⟨hPfin, hQfin⟩
  exact hA.induction₂' R hnear htrans hx hy

/-- An open connected region is rectifiably connected under local coordinate realization.
The realization hypothesis is the direct local consequence of Lemma 2.3′ used in routing. -/
theorem lemma41_open_connected_rectifiable
    {X : Type*} [MetricSpace X] (ρ : X × X → ℝ) (hρ : IsCoordinate ρ)
    (hreal : ∀ {O : Set X}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ρ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
            (MetricFunSpace.pt ρ hρ.metric y),
          (∀ t, LQGMetric.metricFunSpaceVal ρ hρ.metric (P t) ∈ O) ∧
          pathLength P ≠ ∞)
    {O : Set X} (hO : IsOpen O) (hOc : IsConnected O)
    {x y : X} (hx : x ∈ O) (hy : y ∈ O) :
    ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
        (MetricFunSpace.pt ρ hρ.metric y),
      (∀ t, LQGMetric.metricFunSpaceVal ρ hρ.metric (P t) ∈ O) ∧
      pathLength P ≠ ∞ := by
  apply lemma41_rectifiable_connected ρ hρ hOc.isPreconnected ?_ hx hy
  intro z hz
  obtain ⟨a, ha, hza⟩ := hreal hO z hz
  obtain ⟨r, hr, hzr⟩ :=
    (Metric.continuousAt_iff.mp hρ.pt_continuous.continuousAt) a ha
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z hr), self_mem_nhdsWithin]
    with w hzw hw
  apply hza w hw
  have hdist := hzr (by simpa only [Metric.mem_ball] using hzw)
  simpa only [MetricFunSpace.dist_pt, hρ.metric.symm] using hdist

end HigherDimLQGMetric
