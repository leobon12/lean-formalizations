import HigherDimLQGMetric.Routing.Lemma41Right

/-!
# Both connectors for one routing edge

The left connector first meets the witness before its marked middle, and the right connector
avoids the left connector and first meets the witness after the marked middle.
-/

set_option autoImplicit false

noncomputable section

open Set Topology LQGMetric.MetricGeometry HigherDimLFPP
open scoped ENNReal

namespace HigherDimLQGMetric

/-- The geometric inputs for routing one witness through two opposite regions. -/
structure Lemma41EdgeRegions {d : ℕ} (ρ : Rd d × Rd d → ℝ)
    (γ : ℝ → Rd d) (s t : ℝ) (v w : Rd d)
    (Ωl Ωr : Set (Rd d)) : Prop where
  left_open : IsOpen Ωl
  left_connected : IsConnected Ωl
  right_open : IsOpen Ωr
  right_connected : IsConnected Ωr
  vertex_left : v ∈ Ωl
  vertex_right : w ∈ Ωr
  witness_left : γ 0 ∈ Ωl
  witness_right : γ 1 ∈ Ωr
  opposite_excluded : w ∉ Ωl
  left_vertex_off_witness : v ∉ γ '' Icc 0 1
  right_vertex_off_witness : w ∉ γ '' Icc 0 1
  cuts : 0 < s ∧ s < t ∧ t < 1

/-- Route both sides of one marked witness arc. -/
theorem lemma41_pair_connectors {d : ℕ} (hd : 3 ≤ d)
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (hreal : ∀ {O : Set (Rd d)}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ρ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
            (MetricFunSpace.pt ρ hρ.metric y),
          (∀ r, LQGMetric.metricFunSpaceVal ρ hρ.metric (P r) ∈ O) ∧
          pathLength P ≠ ∞)
    (γ : ℝ → Rd d) (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1))
    (s t : ℝ) (v w : Rd d) (Ωl Ωr : Set (Rd d))
    (hreg : Lemma41EdgeRegions ρ γ s t v w Ωl Ωr) :
    ∃ u q : ℝ, 0 ≤ u ∧ u < s ∧ t < q ∧ q ≤ 1 ∧
      ∃ βl βr : ℝ → MetricFunSpace ρ hρ.metric,
        ContinuousOn βl (Icc 0 1) ∧ InjOn βl (Icc 0 1) ∧
        curveLength βl 0 1 ≠ ∞ ∧
        βl 0 = MetricFunSpace.pt ρ hρ.metric v ∧
        βl 1 = MetricFunSpace.pt ρ hρ.metric (γ u) ∧
        (∀ r ∈ Icc (0 : ℝ) 1,
          LQGMetric.metricFunSpaceVal ρ hρ.metric (βl r) ∈ Ωl) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, r < 1 →
          βl r ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) ∧
        ContinuousOn βr (Icc 0 1) ∧ InjOn βr (Icc 0 1) ∧
        curveLength βr 0 1 ≠ ∞ ∧
        βr 0 = MetricFunSpace.pt ρ hρ.metric w ∧
        βr 1 = MetricFunSpace.pt ρ hρ.metric (γ q) ∧
        (∀ r ∈ Icc (0 : ℝ) 1,
          LQGMetric.metricFunSpaceVal ρ hρ.metric (βr r) ∈ Ωr) ∧
        (∀ r ∈ Icc (0 : ℝ) 1,
          βr r ∉ βl '' Icc 0 1) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, r < 1 →
          βr r ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) := by
  obtain ⟨hs₀, hst, ht₁⟩ := hreg.cuts
  obtain ⟨u, hu₀, hus, βl, hβlc, hβli, hβlO, hβl0, hβl1, hβllen, hβlavoid⟩ :=
    lemma41_left_connector hd ρ hρ hreal hreg.left_open hreg.left_connected
      γ hγc hγi hs₀ (hst.trans ht₁) hreg.vertex_left
      hreg.left_vertex_off_witness hreg.witness_left
  have hwβ : w ∉ (LQGMetric.metricFunSpaceVal ρ hρ.metric ∘ βl) '' Icc 0 1 := by
    rintro ⟨r, hr, heq⟩
    exact hreg.opposite_excluded (heq ▸ (hβlO r hr).1)
  have hut : u < t := hus.trans hst
  obtain ⟨q, htq, hq₁, βr, hβrc, hβri, hβrO, hβr0, hβr1, hβrlen, hβravoid⟩ :=
    lemma41_right_connector hd ρ hρ hreal hreg.right_open hreg.right_connected
      γ hγc hγi (hs₀.trans hst) ht₁
      ⟨hu₀, (hut.trans ht₁).le⟩ hut
      βl hβlc hβli hβl1 hβlavoid hreg.vertex_right hwβ
      hreg.right_vertex_off_witness hreg.witness_right
  refine ⟨u, q, hu₀, hus, htq, hq₁, βl, βr, hβlc, hβli, hβllen,
    hβl0, hβl1, ?_, hβlavoid, hβrc, hβri, hβrlen, hβr0, hβr1, ?_, ?_, hβravoid⟩
  · intro r hr
    exact (hβlO r hr).1
  · intro r hr
    exact (hβrO r hr).1
  · intro r hr hmem
    have h := (hβrO r hr).2
    apply h (Or.inl ?_)
    obtain ⟨a, ha, heq⟩ := hmem
    exact ⟨a, ha, congrArg (LQGMetric.metricFunSpaceVal ρ hρ.metric) heq⟩

end HigherDimLQGMetric
