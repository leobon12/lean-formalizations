import HigherDimLQGMetric.Routing.Lemma41OuterLeft

/-! A right connector avoiding the first connector and the protected witness prefix. -/

set_option autoImplicit false

noncomputable section

open Set Topology HigherDimLFPP LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

theorem lemma41_outer_right_connector {d : ℕ} (hd : 3 ≤ d)
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
    {cut u : ℝ} (hcut₀ : 0 < cut) (hcut₁ : cut < 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hucut : u < cut)
    (β : ℝ → MetricFunSpace ρ hρ.metric)
    (hβc : ContinuousOn β (Icc 0 1)) (hβi : InjOn β (Icc 0 1))
    (hβ1 : β 1 = MetricFunSpace.pt ρ hρ.metric (γ u))
    (hβavoid : ∀ t ∈ Icc (0 : ℝ) 1, t < 1 →
      β t ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1))
    {y : configOuter d} (hyΩ : y.1 ∈ Ω)
    (hyβ : y ∉ (LQGMetric.metricFunSpaceVal ρ hρ.metric ∘ β) '' Icc 0 1)
    (hyγ : y ∉ γ '' Icc 0 1)
    (hγ1Ω : (γ 1).1 ∈ Ω) :
    ∃ v : ℝ, cut < v ∧ v ≤ 1 ∧
      ∃ η : ℝ → MetricFunSpace ρ hρ.metric,
        ContinuousOn η (Icc 0 1) ∧ InjOn η (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          (LQGMetric.metricFunSpaceVal ρ hρ.metric (η t)).1 ∈
            Ω \ (((Subtype.val ∘ LQGMetric.metricFunSpaceVal ρ hρ.metric ∘ β) '' Icc 0 1) ∪
              (Subtype.val ∘ γ) '' Icc 0 cut)) ∧
        η 0 = MetricFunSpace.pt ρ hρ.metric y ∧
        η 1 = MetricFunSpace.pt ρ hρ.metric (γ v) ∧
        curveLength η 0 1 ≠ ∞ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, t < 1 →
          η t ∉ MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc 0 1)) := by
  let B : ℝ → configOuter d := LQGMetric.metricFunSpaceVal ρ hρ.metric ∘ β
  let Bv : ℝ → Rd d := Subtype.val ∘ B
  let γv : ℝ → Rd d := Subtype.val ∘ γ
  have hBc : ContinuousOn B (Icc 0 1) :=
    hρ.val_continuous.continuousOn.comp hβc (fun _ _ => mem_univ _)
  have hBvc : ContinuousOn Bv (Icc 0 1) :=
    continuous_subtype_val.continuousOn.comp hBc (fun _ _ => mem_univ _)
  have hγvc : ContinuousOn γv (Icc 0 1) :=
    continuous_subtype_val.continuousOn.comp hγc (fun _ _ => mem_univ _)
  have hBvi : InjOn Bv (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    apply hβi hs ht
    exact Subtype.ext hst
  have hγvi : InjOn γv (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact hγi hs ht (Subtype.ext hst)
  have hBavoid : ∀ t ∈ Icc (0 : ℝ) 1, t < 1 → B t ∉ γ '' Icc 0 1 := by
    intro t ht ht1 htg
    apply hβavoid t ht ht1
    obtain ⟨r, hr, hgr⟩ := htg
    exact ⟨γ r, ⟨r, hr, rfl⟩, hgr⟩
  have hB1 : B 1 = γ u := by
    change LQGMetric.metricFunSpaceVal ρ hρ.metric (β 1) = γ u
    rw [hβ1]
    rfl
  have hBinter : (Bv '' Icc (0 : ℝ) 1 ∩ γv '' Icc 0 1).Subsingleton := by
    intro p hp q hq
    obtain ⟨s, hs, rfl⟩ := hp.1
    obtain ⟨t, ht, rfl⟩ := hq.1
    have hs1 : s = 1 := by
      by_contra hne
      apply hBavoid s hs (lt_of_le_of_ne hs.2 hne)
      obtain ⟨r, hr, heq⟩ := hp.2
      exact ⟨r, hr, Subtype.ext heq⟩
    have ht1 : t = 1 := by
      by_contra hne
      apply hBavoid t ht (lt_of_le_of_ne ht.2 hne)
      obtain ⟨r, hr, heq⟩ := hq.2
      exact ⟨r, hr, Subtype.ext heq⟩
    rw [hs1, ht1]
  have hprefixc : ContinuousOn γv (Icc 0 cut) :=
    hγvc.mono (Icc_subset_Icc le_rfl hcut₁.le)
  have hprefixi : InjOn γv (Icc 0 cut) :=
    hγvi.mono (Icc_subset_Icc le_rfl hcut₁.le)
  have hinter : (Bv '' Icc (0 : ℝ) 1 ∩ γv '' Icc 0 cut).Subsingleton := by
    intro p hp q hq
    apply hBinter
    · exact ⟨hp.1, (image_mono (Icc_subset_Icc le_rfl hcut₁.le)) hp.2⟩
    · exact ⟨hq.1, (image_mono (Icc_subset_Icc le_rfl hcut₁.le)) hq.2⟩
  let W : Set (Rd d) := Ω \ (Bv '' Icc 0 1 ∪ γv '' Icc 0 cut)
  let O : Set (configOuter d) :=
    lemma41_outerSet Ω \ (B '' Icc 0 1 ∪ γ '' Icc 0 cut)
  have hWp : IsPathConnected W :=
    Topology.ns_tree_Icc hd hΩo hΩc (by norm_num : (0 : ℝ) < 1)
      hcut₀ hBvc hprefixc hBvi hprefixi hinter
  have hWU : W ⊆ configOuter d := fun _ hx => hΩU hx.1
  have hOeq : O = (Subtype.val : configOuter d → Rd d) ⁻¹' W := by
    ext z
    constructor
    · rintro ⟨hzΩ, hzavoid⟩
      refine ⟨hzΩ, ?_⟩
      rintro (hzB | hzγ)
      · apply hzavoid (Or.inl ?_)
        obtain ⟨r, hr, heq⟩ := hzB
        exact ⟨r, hr, Subtype.ext heq⟩
      · apply hzavoid (Or.inr ?_)
        obtain ⟨r, hr, heq⟩ := hzγ
        exact ⟨r, hr, Subtype.ext heq⟩
    · rintro ⟨hzΩ, hzavoid⟩
      refine ⟨hzΩ, ?_⟩
      rintro (hzB | hzγ)
      · exact hzavoid (Or.inl (by
          obtain ⟨r, hr, heq⟩ := hzB
          exact ⟨r, hr, congrArg Subtype.val heq⟩))
      · exact hzavoid (Or.inr (by
          obtain ⟨r, hr, heq⟩ := hzγ
          exact ⟨r, hr, congrArg Subtype.val heq⟩))
  have hOp : IsPathConnected O := by
    rw [hOeq]
    exact hWp.preimage_coe hWU
  have hOo : IsOpen O := by
    apply (hΩo.preimage continuous_subtype_val).sdiff
    exact ((isCompact_Icc.image_of_continuousOn hBc).union
      (isCompact_Icc.image_of_continuousOn
        (hγc.mono (Icc_subset_Icc le_rfl hcut₁.le)))).isClosed
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
    have h1t : (1 : ℝ) = t := hγi (by norm_num)
      (Icc_subset_Icc le_rfl hcut₁.le ht) heq.symm
    linarith [ht.2]
  have hγ1O : γ 1 ∈ O :=
    ⟨hγ1Ω, by simp only [mem_union, not_or]; exact ⟨hγ1B, hγ1prefix⟩⟩
  obtain ⟨v, hv, η, hηc, hηi, hηO, hη0, hη1, hηlen, hηavoid⟩ :=
    lemma41_route_first_contact ρ hρ hreal hOo hOp.isConnected γ hγc hyO
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) hγ1O hyγ
  have hcutv : cut < v := by
    by_contra hnot
    have hvprefix : γ v ∈ γ '' Icc 0 cut :=
      ⟨v, ⟨hv.1, le_of_not_gt hnot⟩, rfl⟩
    have hvO := hηO 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    rw [hη1] at hvO
    exact hvO.2 (Or.inr hvprefix)
  refine ⟨v, hcutv, hv.2, η, hηc, hηi, ?_, hη0, hη1, hηlen, hηavoid⟩
  intro t ht
  have h := hηO t ht
  exact ⟨h.1, fun hmem => h.2 (by
    rcases hmem with hB | hγ
    · obtain ⟨r, hr, heq⟩ := hB
      exact Or.inl ⟨r, hr, Subtype.ext heq⟩
    · obtain ⟨r, hr, heq⟩ := hγ
      exact Or.inr ⟨r, hr, Subtype.ext heq⟩)⟩

end HigherDimLQGMetric
