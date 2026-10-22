import HigherDimLQGMetric.Routing.Lemma41Arc

/-!
# Routing a connector to its first contact with a witness arc

In an open connected routing region, local coordinate realization gives a finite length path.
Intrinsic shortest-path extraction turns it into a simple connector meeting the witness arc
only at its terminal point.
-/

set_option autoImplicit false

noncomputable section

open Set Topology LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

/-- Route from a point to a compact witness arc inside a connected open region. -/
theorem lemma41_route_first_contact
    {X : Type*} [MetricSpace X] (ρ : X × X → ℝ) (hρ : IsCoordinate ρ)
    (hreal : ∀ {O : Set X}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ρ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
            (MetricFunSpace.pt ρ hρ.metric y),
          (∀ t, LQGMetric.metricFunSpaceVal ρ hρ.metric (P t) ∈ O) ∧
          pathLength P ≠ ∞)
    {O : Set X} (hO : IsOpen O) (hOc : IsConnected O)
    (γ : ℝ → X) (hγ : ContinuousOn γ (Icc 0 1))
    {x : X} (hx : x ∈ O) {e : ℝ} (he : e ∈ Icc (0 : ℝ) 1)
    (hγe : γ e ∈ O)
    (hxγ : x ∉ γ '' Icc 0 1) :
    ∃ u ∈ Icc (0 : ℝ) 1, ∃ β : ℝ → MetricFunSpace ρ hρ.metric,
      ContinuousOn β (Icc 0 1) ∧ InjOn β (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        LQGMetric.metricFunSpaceVal ρ hρ.metric (β t) ∈ O) ∧
      β 0 = MetricFunSpace.pt ρ hρ.metric x ∧
      β 1 = MetricFunSpace.pt ρ hρ.metric (γ u) ∧
      curveLength β 0 1 ≠ ∞ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, t < 1 →
        β t ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) := by
  obtain ⟨P, hPO, hPfin⟩ :=
    lemma41_open_connected_rectifiable ρ hρ hreal hO hOc hx hγe
  let C : Set (MetricFunSpace ρ hρ.metric) :=
    MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)
  have hCcompact : IsCompact C :=
    (isCompact_Icc.image_of_continuousOn hγ).image hρ.pt_continuous
  have hxC : MetricFunSpace.pt ρ hρ.metric x ∉ C := by
    rintro ⟨z, ⟨t, ht, rfl⟩, heq⟩
    apply hxγ
    change γ t = x at heq
    exact ⟨t, ht, heq⟩
  have hyC : MetricFunSpace.pt ρ hρ.metric (γ e) ∈ C :=
    ⟨γ e, ⟨e, he, rfl⟩, rfl⟩
  obtain ⟨z, hz, β, hβc, hβinj, hβP, hβ0, hβ1, hβlen, hβavoid⟩ :=
    lemma41_first_contact_arc P hPfin hCcompact.isClosed hxC hyC
  obtain ⟨v, ⟨u, hu, rfl⟩, hv⟩ := hz.1
  refine ⟨u, hu, β, hβc, hβinj, ?_, hβ0, hβ1.trans hv.symm, hβlen, hβavoid⟩
  intro t ht
  obtain ⟨s, hs⟩ := hβP ht
  rw [← hs]
  exact hPO s

end HigherDimLQGMetric
