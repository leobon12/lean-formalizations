import HigherDimLQGMetric.Routing.Lemma41Left

/-!
# Right connector around the first connector and marked prefix

The first connector meets the witness arc only at its terminal point. Its Euclidean image and
the protected prefix therefore meet in at most one point, so D-NS applies to their union.
-/

set_option autoImplicit false

noncomputable section

open Set Topology LQGMetric.MetricGeometry HigherDimLFPP
open scoped ENNReal

namespace HigherDimLQGMetric

theorem lemma41_right_connector {d : ℕ} (hd : 3 ≤ d)
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
    {cut u : ℝ} (hcut₀ : 0 < cut) (hcut₁ : cut < 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hucut : u < cut)
    (β : ℝ → MetricFunSpace ρ hρ.metric)
    (hβc : ContinuousOn β (Icc 0 1)) (hβi : InjOn β (Icc 0 1))
    (hβ1 : β 1 = MetricFunSpace.pt ρ hρ.metric (γ u))
    (hβavoid : ∀ t ∈ Icc (0 : ℝ) 1, t < 1 →
      β t ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1))
    {y : Rd d} (hyΩ : y ∈ Ω)
    (hyβ : y ∉ (LQGMetric.metricFunSpaceVal ρ hρ.metric ∘ β) '' Icc 0 1)
    (hyγ : y ∉ γ '' Icc 0 1)
    (hγ1Ω : γ 1 ∈ Ω) :
    ∃ v : ℝ, cut < v ∧ v ≤ 1 ∧
      ∃ η : ℝ → MetricFunSpace ρ hρ.metric,
        ContinuousOn η (Icc 0 1) ∧ InjOn η (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          LQGMetric.metricFunSpaceVal ρ hρ.metric (η t) ∈
            Ω \ ((LQGMetric.metricFunSpaceVal ρ hρ.metric ∘ β) '' Icc 0 1 ∪
              γ '' Icc 0 cut)) ∧
        η 0 = MetricFunSpace.pt ρ hρ.metric y ∧
        η 1 = MetricFunSpace.pt ρ hρ.metric (γ v) ∧
        curveLength η 0 1 ≠ ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, t < 1 →
          η t ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) := by
  let B : ℝ → Rd d := LQGMetric.metricFunSpaceVal ρ hρ.metric ∘ β
  have hBc : ContinuousOn B (Icc 0 1) :=
    hρ.val_continuous.continuousOn.comp hβc (fun _ _ => mem_univ _)
  have hBi : InjOn B (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    apply hβi hs ht
    exact hst
  have hBavoid : ∀ t ∈ Icc (0 : ℝ) 1, t < 1 → B t ∉ γ '' Icc 0 1 := by
    intro t ht ht1 htg
    apply hβavoid t ht ht1
    obtain ⟨r, hr, hgr⟩ := htg
    refine ⟨γ r, ⟨r, hr, rfl⟩, ?_⟩
    exact hgr
  have hB1 : B 1 = γ u := by
    change LQGMetric.metricFunSpaceVal ρ hρ.metric (β 1) = γ u
    rw [hβ1]
    rfl
  have hBinter : (B '' Icc (0 : ℝ) 1 ∩ γ '' Icc 0 1).Subsingleton := by
    intro p hp q hq
    obtain ⟨s, hs, rfl⟩ := hp.1
    obtain ⟨t, ht, rfl⟩ := hq.1
    have hs1 : s = 1 := by
      by_contra hne
      exact hBavoid s hs (lt_of_le_of_ne hs.2 hne) hp.2
    have ht1 : t = 1 := by
      by_contra hne
      exact hBavoid t ht (lt_of_le_of_ne ht.2 hne) hq.2
    rw [hs1, ht1]
  have hprefixc : ContinuousOn γ (Icc 0 cut) :=
    hγc.mono (Icc_subset_Icc le_rfl hcut₁.le)
  have hprefixi : InjOn γ (Icc 0 cut) :=
    hγi.mono (Icc_subset_Icc le_rfl hcut₁.le)
  have hinter : (B '' Icc (0 : ℝ) 1 ∩ γ '' Icc 0 cut).Subsingleton := by
    intro p hp q hq
    apply hBinter
    · exact ⟨hp.1, (image_mono (Icc_subset_Icc le_rfl hcut₁.le)) hp.2⟩
    · exact ⟨hq.1, (image_mono (Icc_subset_Icc le_rfl hcut₁.le)) hq.2⟩
  let O : Set (Rd d) := Ω \ (B '' Icc 0 1 ∪ γ '' Icc 0 cut)
  have hOp : IsPathConnected O :=
    Topology.ns_tree_Icc hd hΩo hΩc (by norm_num : (0 : ℝ) < 1)
      hcut₀ hBc hprefixc hBi hprefixi hinter
  have hOo : IsOpen O := by
    apply hΩo.sdiff
    exact ((isCompact_Icc.image_of_continuousOn hBc).union
      (isCompact_Icc.image_of_continuousOn hprefixc)).isClosed
  have hyO : y ∈ O := by
    refine ⟨hyΩ, ?_⟩
    intro h
    rcases h with h | h
    · exact hyβ h
    · exact hyγ ((image_mono (Icc_subset_Icc le_rfl hcut₁.le)) h)
  have hγ1B : γ 1 ∉ B '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, heq⟩
    have ht1 : t = 1 := by
      by_contra hne
      apply hBavoid t ht (lt_of_le_of_ne ht.2 hne)
      exact ⟨1, by norm_num, heq.symm⟩
    rw [ht1, hB1] at heq
    have h1u : (1 : ℝ) = u := hγi (by norm_num) hu heq.symm
    linarith
  have hγ1prefix : γ 1 ∉ γ '' Icc (0 : ℝ) cut := by
    rintro ⟨t, ht, heq⟩
    have h1t : (1 : ℝ) = t := hγi (by norm_num) (Icc_subset_Icc le_rfl hcut₁.le ht) heq.symm
    linarith [ht.2]
  have hγ1O : γ 1 ∈ O := ⟨hγ1Ω, by simp only [mem_union, not_or]; exact ⟨hγ1B, hγ1prefix⟩⟩
  obtain ⟨v, hv, η, hηc, hηi, hηO, hη0, hη1, hηlen, hηavoid⟩ :=
    lemma41_route_first_contact ρ hρ hreal hOo hOp.isConnected γ hγc hyO
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) hγ1O hyγ
  have hcutv : cut < v := by
    by_contra hnot
    have hvprefix : γ v ∈ γ '' Icc 0 cut := ⟨v, ⟨hv.1, le_of_not_gt hnot⟩, rfl⟩
    have hvO := hηO 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    rw [hη1] at hvO
    exact hvO.2 (Or.inr hvprefix)
  exact ⟨v, hcutv, hv.2, η, hηc, hηi, hηO, hη0, hη1, hηlen, hηavoid⟩

end HigherDimLQGMetric
