import HigherDimLQGMetric.Routing.Lemma41Outer

/-! A left connector for a coordinate carried by the outer annulus. -/

set_option autoImplicit false

noncomputable section

open Set Topology HigherDimLFPP LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

theorem lemma41_outer_left_connector {d : ℕ} (hd : 3 ≤ d)
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (hreal : ∀ {O : Set (configOuter d)}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ρ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
            (MetricFunSpace.pt ρ hρ.metric y),
          (∀ t, LQGMetric.metricFunSpaceVal ρ hρ.metric (P t) ∈ O) ∧
          pathLength P ≠ ∞)
    {Ω : Set (Rd d)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩU : Ω ⊆ configOuter d)
    (γ : ℝ → configOuter d) (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1))
    {s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1)
    {x : configOuter d} (hxΩ : x.1 ∈ Ω) (hxγ : x ∉ γ '' Icc 0 1)
    (hγ0Ω : (γ 0).1 ∈ Ω) :
    ∃ u : ℝ, 0 ≤ u ∧ u < s ∧
      ∃ β : ℝ → MetricFunSpace ρ hρ.metric,
        ContinuousOn β (Icc 0 1) ∧ InjOn β (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          (LQGMetric.metricFunSpaceVal ρ hρ.metric (β t)).1 ∈
            Ω \ ((Subtype.val ∘ γ) '' Icc s 1)) ∧
        β 0 = MetricFunSpace.pt ρ hρ.metric x ∧
        β 1 = MetricFunSpace.pt ρ hρ.metric (γ u) ∧
        curveLength β 0 1 ≠ ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, t < 1 →
          β t ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) := by
  have hγvalc : ContinuousOn (Subtype.val ∘ γ) (Icc 0 1) :=
    continuous_subtype_val.continuousOn.comp hγc (fun _ _ => mem_univ _)
  have hγvali : InjOn (Subtype.val ∘ γ) (Icc (0 : ℝ) 1) := by
    intro a ha b hb heq
    exact hγi ha hb (Subtype.ext heq)
  let W : Set (Rd d) := Ω \ (Subtype.val ∘ γ) '' Icc s 1
  let O : Set (configOuter d) := lemma41_outerSet Ω \ γ '' Icc s 1
  have htailc : ContinuousOn (Subtype.val ∘ γ) (Icc s 1) :=
    hγvalc.mono (Icc_subset_Icc hs₀.le le_rfl)
  have htaili : InjOn (Subtype.val ∘ γ) (Icc s 1) :=
    hγvali.mono (Icc_subset_Icc hs₀.le le_rfl)
  have hWp : IsPathConnected W :=
    Topology.ns_arc_Icc hd hΩo hΩc hs₁ htailc htaili
  have hWU : W ⊆ configOuter d := fun _ hx => hΩU hx.1
  have hOeq : O = (Subtype.val : configOuter d → Rd d) ⁻¹' W := by
    ext z
    constructor
    · rintro ⟨hzΩ, hzγ⟩
      refine ⟨hzΩ, ?_⟩
      rintro ⟨t, ht, heq⟩
      exact hzγ ⟨t, ht, Subtype.ext heq⟩
    · rintro ⟨hzΩ, hzγ⟩
      refine ⟨hzΩ, ?_⟩
      rintro ⟨t, ht, heq⟩
      exact hzγ ⟨t, ht, congrArg Subtype.val heq⟩
  have hOp : IsPathConnected O := by
    rw [hOeq]
    exact hWp.preimage_coe hWU
  have hOo : IsOpen O :=
    (hΩo.preimage continuous_subtype_val).sdiff
      (isCompact_Icc.image_of_continuousOn
        (hγc.mono (Icc_subset_Icc hs₀.le le_rfl))).isClosed
  have hxO : x ∈ O := by
    refine ⟨hxΩ, ?_⟩
    intro h
    exact hxγ ((image_mono (Icc_subset_Icc hs₀.le le_rfl)) h)
  have hγ0O : γ 0 ∈ O := by
    refine ⟨hγ0Ω, ?_⟩
    rintro ⟨t, ht, heq⟩
    have hzero : (0 : ℝ) = t := hγi (by norm_num)
      (Icc_subset_Icc hs₀.le le_rfl ht) heq.symm
    linarith [ht.1]
  obtain ⟨u, hu, β, hβc, hβi, hβO, hβ0, hβ1, hβlen, hβavoid⟩ :=
    lemma41_route_first_contact ρ hρ hreal hOo hOp.isConnected γ hγc hxO
      (by norm_num : (0 : ℝ) ∈ Icc 0 1) hγ0O hxγ
  have hu_lt : u < s := by
    by_contra hnot
    have huTail : γ u ∈ γ '' Icc s 1 :=
      ⟨u, ⟨le_of_not_gt hnot, hu.2⟩, rfl⟩
    have huO := hβO 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    rw [hβ1] at huO
    exact huO.2 huTail
  refine ⟨u, hu.1, hu_lt, β, hβc, hβi, ?_, hβ0, hβ1, hβlen, hβavoid⟩
  intro t ht
  have h := hβO t ht
  exact ⟨h.1, fun hmem => h.2 (by
    obtain ⟨r, hr, heq⟩ := hmem
    exact ⟨r, hr, Subtype.ext heq⟩)⟩

end HigherDimLQGMetric
