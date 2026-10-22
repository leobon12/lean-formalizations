import HigherDimLQGMetric.Routing.Lemma41Route
import HigherDimLQGMetric.Topology.NonSep

/-!
# Left connector around a marked tail

The codimension-two nonseparation theorem leaves the routing region connected after removing
the protected tail of a witness arc. A simple finite-length connector therefore first meets
the witness before the left cut time.
-/

set_option autoImplicit false

noncomputable section

open Set Topology LQGMetric.MetricGeometry HigherDimLFPP
open scoped ENNReal

namespace HigherDimLQGMetric

theorem lemma41_left_connector {d : ℕ} (hd : 3 ≤ d)
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (hreal : ∀ {O : Set (Rd d)}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ρ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
            (MetricFunSpace.pt ρ hρ.metric y),
          (∀ t, LQGMetric.metricFunSpaceVal ρ hρ.metric (P t) ∈ O) ∧
          pathLength P ≠ ∞)
    {Ω : Set (Rd d)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (γ : ℝ → Rd d) (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1))
    {s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1)
    {x : Rd d} (hxΩ : x ∈ Ω) (hxγ : x ∉ γ '' Icc 0 1)
    (hγ0Ω : γ 0 ∈ Ω) :
    ∃ u : ℝ, 0 ≤ u ∧ u < s ∧
      ∃ β : ℝ → MetricFunSpace ρ hρ.metric,
        ContinuousOn β (Icc 0 1) ∧ InjOn β (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          LQGMetric.metricFunSpaceVal ρ hρ.metric (β t) ∈
            Ω \ (γ '' Icc s 1)) ∧
        β 0 = MetricFunSpace.pt ρ hρ.metric x ∧
        β 1 = MetricFunSpace.pt ρ hρ.metric (γ u) ∧
        curveLength β 0 1 ≠ ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, t < 1 →
          β t ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) := by
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hs₀.le, hs₁.le⟩
  have htailc : ContinuousOn γ (Icc s 1) :=
    hγc.mono (Icc_subset_Icc hs.1 le_rfl)
  have htaili : InjOn γ (Icc s 1) :=
    hγi.mono (Icc_subset_Icc hs.1 le_rfl)
  let O : Set (Rd d) := Ω \ γ '' Icc s 1
  have hOp : IsPathConnected O :=
    Topology.ns_arc_Icc hd hΩo hΩc hs₁ htailc htaili
  have hOo : IsOpen O :=
    hΩo.sdiff (isCompact_Icc.image_of_continuousOn htailc).isClosed
  have hxO : x ∈ O := ⟨hxΩ, fun h => hxγ ((image_mono (Icc_subset_Icc hs.1 le_rfl)) h)⟩
  have hγ0O : γ 0 ∈ O := by
    refine ⟨hγ0Ω, ?_⟩
    rintro ⟨t, ht, heq⟩
    have hzero : (0 : ℝ) = t := hγi (by norm_num) (Icc_subset_Icc hs.1 le_rfl ht) heq.symm
    linarith [ht.1]
  obtain ⟨u, hu, β, hβc, hβi, hβO, hβ0, hβ1, hβlen, hβavoid⟩ :=
    lemma41_route_first_contact ρ hρ hreal hOo hOp.isConnected γ hγc hxO
      (by norm_num : (0 : ℝ) ∈ Icc 0 1) hγ0O hxγ
  have hu_lt : u < s := by
    by_contra hnot
    have huTail : γ u ∈ γ '' Icc s 1 := ⟨u, ⟨le_of_not_gt hnot, hu.2⟩, rfl⟩
    have huO := hβO 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    rw [hβ1] at huO
    exact huO.2 huTail
  exact ⟨u, hu.1, hu_lt, β, hβc, hβi, hβO, hβ0, hβ1, hβlen, hβavoid⟩

end HigherDimLQGMetric
