import HigherDimLQGMetric.Routing.Lemma41OuterRight

/-! Two annular-coordinate connectors for one lattice edge. -/

set_option autoImplicit false

noncomputable section

open Set Topology HigherDimLFPP LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

theorem lemma41_outer_pair_connectors {d : ℕ} (hd : 3 ≤ d)
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (hreal : ∀ {O : Set (configOuter d)}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ρ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
            (MetricFunSpace.pt ρ hρ.metric y),
          (∀ r, LQGMetric.metricFunSpaceVal ρ hρ.metric (P r) ∈ O) ∧
          pathLength P ≠ ∞)
    (γ : ℝ → configOuter d) (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1))
    (s t : ℝ) (v w : configOuter d) (Ωl Ωr : Set (Rd d))
    (hreg : Lemma41EdgeRegions (fun p : Rd d × Rd d => dist p.1 p.2)
      (Subtype.val ∘ γ) s t v.1 w.1 Ωl Ωr)
    (hΩlU : Ωl ⊆ configOuter d) (hΩrU : Ωr ⊆ configOuter d) :
    ∃ u q : ℝ, 0 ≤ u ∧ u < s ∧ t < q ∧ q ≤ 1 ∧
      ∃ βl βr : ℝ → MetricFunSpace ρ hρ.metric,
        ContinuousOn βl (Icc 0 1) ∧ InjOn βl (Icc 0 1) ∧
        curveLength βl 0 1 ≠ ∞ ∧
        βl 0 = MetricFunSpace.pt ρ hρ.metric v ∧
        βl 1 = MetricFunSpace.pt ρ hρ.metric (γ u) ∧
        (∀ r ∈ Icc (0 : ℝ) 1,
          (LQGMetric.metricFunSpaceVal ρ hρ.metric (βl r)).1 ∈ Ωl) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, r < 1 →
          βl r ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) ∧
        ContinuousOn βr (Icc 0 1) ∧ InjOn βr (Icc 0 1) ∧
        curveLength βr 0 1 ≠ ∞ ∧
        βr 0 = MetricFunSpace.pt ρ hρ.metric w ∧
        βr 1 = MetricFunSpace.pt ρ hρ.metric (γ q) ∧
        (∀ r ∈ Icc (0 : ℝ) 1,
          (LQGMetric.metricFunSpaceVal ρ hρ.metric (βr r)).1 ∈ Ωr) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, βr r ∉ βl '' Icc 0 1) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, r < 1 →
          βr r ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) := by
  obtain ⟨hs₀, hst, ht₁⟩ := hreg.cuts
  have hvγ : v ∉ γ '' Icc (0 : ℝ) 1 := by
    rintro ⟨r, hr, heq⟩
    exact hreg.left_vertex_off_witness ⟨r, hr, congrArg Subtype.val heq⟩
  obtain ⟨u, hu₀, hus, βl, hβlc, hβli, hβlO, hβl0, hβl1, hβllen, hβlavoid⟩ :=
    lemma41_outer_left_connector hd ρ hρ hreal hreg.left_open hreg.left_connected
      hΩlU γ hγc hγi hs₀ (hst.trans ht₁) hreg.vertex_left hvγ
      hreg.witness_left
  have hwβ : w ∉ (LQGMetric.metricFunSpaceVal ρ hρ.metric ∘ βl) '' Icc 0 1 := by
    rintro ⟨r, hr, heq⟩
    exact hreg.opposite_excluded (congrArg Subtype.val heq ▸ (hβlO r hr).1)
  have hwγ : w ∉ γ '' Icc (0 : ℝ) 1 := by
    rintro ⟨r, hr, heq⟩
    exact hreg.right_vertex_off_witness ⟨r, hr, congrArg Subtype.val heq⟩
  have hut : u < t := hus.trans hst
  obtain ⟨q, htq, hq₁, βr, hβrc, hβri, hβrO, hβr0, hβr1, hβrlen, hβravoid⟩ :=
    lemma41_outer_right_connector hd ρ hρ hreal hreg.right_open hreg.right_connected
      hΩrU γ hγc hγi (hs₀.trans hst) ht₁
      ⟨hu₀, (hut.trans ht₁).le⟩ hut
      βl hβlc hβli hβl1 hβlavoid hreg.vertex_right hwβ hwγ hreg.witness_right
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
    exact ⟨a, ha, congrArg (fun z : MetricFunSpace ρ hρ.metric =>
      (LQGMetric.metricFunSpaceVal ρ hρ.metric z).1) heq⟩

end HigherDimLQGMetric
