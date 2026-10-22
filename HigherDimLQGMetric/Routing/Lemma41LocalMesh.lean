import HigherDimLQGMetric.Routing.Lemma41Local

/-! The one-edge routing theorem packaged for finite lattice assembly. -/

set_option autoImplicit false

noncomputable section

open Set Topology HigherDimLFPP LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

theorem lemma41_local_mesh_piece_mark {d : ℕ} (hd : 3 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    {m n : Fin d → ℤ} (hmn : (Topology.latticeGraph d).Adj m n)
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (hreal : ∀ {O : Set (Rd d)}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ρ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
            (MetricFunSpace.pt ρ hρ.metric y),
          (∀ r, LQGMetric.metricFunSpaceVal ρ hρ.metric (P r) ∈ O) ∧
          pathLength P ≠ ∞)
    (E : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (γ : ℝ → Rd d) (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1))
    (hγbox : MapsTo γ (Icc (0 : ℝ) 1)
      (centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)))
    (hγlen : curveLength (MetricFunSpace.pt ρ hρ.metric ∘ γ) 0 1 ≠ ∞)
    {a₁ c₂ c₃ : ℝ} (ha₁ : 0 < a₁) (hc₂ : 0 ≤ c₂) (hc₂₃ : c₂ < c₃)
    (hsep : a₁ ≤ ρ (γ 0, γ 1))
    (hE : curveLengthWith E (MetricFunSpace.pt ρ hρ.metric ∘ γ) 0 1 ≤
      ENNReal.ofReal (c₂ * ρ (γ 0, γ 1))) :
    ∃ P : Lemma41LocalPiece
      (MetricFunSpace.pt ρ hρ.metric (Topology.latticePoint δ m))
      (MetricFunSpace.pt ρ hρ.metric (Topology.latticePoint δ n))
      (MetricFunSpace.pt ρ hρ.metric ''
        routingRegion δ (Topology.latticePoint δ m) (Topology.latticePoint δ n))
      (MetricFunSpace.pt ρ hρ.metric ''
        routingRegion δ (Topology.latticePoint δ n) (Topology.latticePoint δ m))
      (MetricFunSpace.pt ρ hρ.metric ''
        centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n))
      E a₁ c₃, P.σ '' Icc (0 : ℝ) 1 ⊆
        MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc (0 : ℝ) 1) := by
  obtain ⟨s, t, u, q, βl, βr, σ, hs, hst, ht, hu, hus, htq, hq,
    hσc, hσi, hσ0, hσ1, hσeq, hσsep, hσshort, hσbox,
    hβlc, hβli, hβllen, hβl0, hβl1, hβlreg, hβlavoid,
    hβrc, hβri, hβrlen, hβr0, hβr1, hβrreg, hβravoidl, hβravoid⟩ :=
    lemma41_edge_routing_full hd hδ hmn ρ hρ hreal E γ hγc hγi hγbox
      ha₁ hc₂ hc₂₃ hsep hE
  let pγ : ℝ → MetricFunSpace ρ hρ.metric := MetricFunSpace.pt ρ hρ.metric ∘ γ
  let K : Set (MetricFunSpace ρ hρ.metric) :=
    βl '' Icc (0 : ℝ) 1 ∪ pγ '' Icc 0 1 ∪ βr '' Icc 0 1
  let L : Set (MetricFunSpace ρ hρ.metric) :=
    βl '' Icc (0 : ℝ) 1 ∪ pγ '' Icc 0 s
  let R : Set (MetricFunSpace ρ hρ.metric) :=
    βr '' Icc (0 : ℝ) 1 ∪ pγ '' Icc t 1
  have hpγc : ContinuousOn pγ (Icc 0 1) :=
    hρ.pt_continuous.continuousOn.comp hγc (fun _ _ => mem_univ _)
  have hpγi : InjOn pγ (Icc (0 : ℝ) 1) := by
    intro a ha b hb heq
    exact hγi ha hb heq
  have huI : u ∈ Icc (0 : ℝ) 1 := ⟨hu, (hus.trans (hst.trans ht)).le⟩
  have hqI : q ∈ Icc (0 : ℝ) 1 := ⟨(hs.trans (hst.trans htq)).le, hq⟩
  have hβlavoids : ∀ r ∈ Icc (0 : ℝ) 1, r < 1 → βl r ∉ pγ '' Icc 0 1 := by
    simpa only [pγ, image_comp] using hβlavoid
  have hβravoids : ∀ r ∈ Icc (0 : ℝ) 1, r < 1 → βr r ∉ pγ '' Icc 0 1 := by
    simpa only [pγ, image_comp] using hβravoid
  have hβlr : Disjoint (βl '' Icc (0 : ℝ) 1) (βr '' Icc 0 1) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨r, hr, rfl⟩
    exact hβravoidl r hr hx
  have hcomp := lemma41_one_edge_components βl pγ βr hβlc hpγc hβrc hpγi
    hs hst ht hu hus htq hq hβl1 hβr1 hβlavoids hβravoids hβlr
  change IsCompact L ∧ IsConnected L ∧ IsCompact R ∧ IsConnected R ∧
    K \ (pγ '' Ioo s t) = L ∪ R ∧ Disjoint L R at hcomp
  have hgraph : IsFiniteRectGraph K :=
    lemma41_three_arc_graph βl pγ βr hβlc hpγc hβrc hβli hpγi hβri
      hβllen hγlen hβrlen huI hqI hβl1 hβr1
  have hσM : σ '' Ioo (0 : ℝ) 1 = pγ '' Ioo s t := by
    rw [hσeq]
    exact lemma41_affine_marked_interior pγ hst
  have hσfull : σ '' Icc (0 : ℝ) 1 = pγ '' Icc s t := by
    rw [hσeq]
    exact lemma41_affine_marked_image pγ hst
  have hσbox' : σ '' Icc (0 : ℝ) 1 ⊆
      MetricFunSpace.pt ρ hρ.metric ''
        centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n) :=
    hσbox.image_subset
  refine ⟨⟨K, L, R, σ, hgraph, ?_, ?_, ?_, ?_,
    hcomp.1, hcomp.2.1, hcomp.2.2.1, hcomp.2.2.2.1, hcomp.2.2.2.2.2,
    ?_, ?_, ?_, ?_, hσbox', hσc, hσi, hσsep, hσshort⟩, ?_⟩
  · simpa only [hσM] using hcomp.2.2.2.2.1
  · rw [hσfull]
    intro x hx
    exact Or.inl (Or.inr ((image_mono (Icc_subset_Icc hs.le ht.le)) hx))
  · rw [hσ0]
    exact Or.inr ⟨s, ⟨hs.le, le_rfl⟩, rfl⟩
  · rw [hσ1]
    exact Or.inr ⟨t, ⟨le_rfl, ht.le⟩, rfl⟩
  · exact Or.inl ⟨0, by norm_num, hβl0⟩
  · exact Or.inl ⟨0, by norm_num, hβr0⟩
  · rintro x (hxβ | hxγ)
    · obtain ⟨r, hr, rfl⟩ := hxβ
      exact ⟨LQGMetric.metricFunSpaceVal ρ hρ.metric (βl r), hβlreg r hr, rfl⟩
    · obtain ⟨r, hr, rfl⟩ := hxγ
      have hbox : γ r ∈ centralBox δ (Topology.latticePoint δ m)
          (Topology.latticePoint δ n) := hγbox (Icc_subset_Icc le_rfl (hst.trans ht).le hr)
      exact ⟨γ r, centralBox_subset_routingRegion hδ (dist_latticePoint_of_adj hδ hmn)
        hbox, rfl⟩
  · rintro x (hxβ | hxγ)
    · obtain ⟨r, hr, rfl⟩ := hxβ
      exact ⟨LQGMetric.metricFunSpaceVal ρ hρ.metric (βr r), hβrreg r hr, rfl⟩
    · obtain ⟨r, hr, rfl⟩ := hxγ
      have hbox : γ r ∈ centralBox δ (Topology.latticePoint δ m)
          (Topology.latticePoint δ n) := hγbox (Icc_subset_Icc (hs.trans hst).le le_rfl hr)
      exact ⟨γ r, centralBox_subset_routingRegion_swap hδ (dist_latticePoint_of_adj hδ hmn)
        hbox, rfl⟩
  · rw [hσfull]
    rintro x ⟨r, hr, rfl⟩
    exact ⟨γ r, ⟨r, (Icc_subset_Icc hs.le ht.le) hr, rfl⟩, rfl⟩

theorem lemma41_local_mesh_piece {d : ℕ} (hd : 3 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    {m n : Fin d → ℤ} (hmn : (Topology.latticeGraph d).Adj m n)
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (hreal : ∀ {O : Set (Rd d)}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ρ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
            (MetricFunSpace.pt ρ hρ.metric y),
          (∀ r, LQGMetric.metricFunSpaceVal ρ hρ.metric (P r) ∈ O) ∧
          pathLength P ≠ ∞)
    (E : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (γ : ℝ → Rd d) (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1))
    (hγbox : MapsTo γ (Icc (0 : ℝ) 1)
      (centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)))
    (hγlen : curveLength (MetricFunSpace.pt ρ hρ.metric ∘ γ) 0 1 ≠ ∞)
    {a₁ c₂ c₃ : ℝ} (ha₁ : 0 < a₁) (hc₂ : 0 ≤ c₂) (hc₂₃ : c₂ < c₃)
    (hsep : a₁ ≤ ρ (γ 0, γ 1))
    (hE : curveLengthWith E (MetricFunSpace.pt ρ hρ.metric ∘ γ) 0 1 ≤
      ENNReal.ofReal (c₂ * ρ (γ 0, γ 1))) :
    Nonempty (Lemma41LocalPiece
      (MetricFunSpace.pt ρ hρ.metric (Topology.latticePoint δ m))
      (MetricFunSpace.pt ρ hρ.metric (Topology.latticePoint δ n))
      (MetricFunSpace.pt ρ hρ.metric ''
        routingRegion δ (Topology.latticePoint δ m) (Topology.latticePoint δ n))
      (MetricFunSpace.pt ρ hρ.metric ''
        routingRegion δ (Topology.latticePoint δ n) (Topology.latticePoint δ m))
      (MetricFunSpace.pt ρ hρ.metric ''
        centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n))
      E a₁ c₃) := by
  obtain ⟨P, _⟩ := lemma41_local_mesh_piece_mark hd hδ hmn ρ hρ hreal E γ
    hγc hγi hγbox hγlen ha₁ hc₂ hc₂₃ hsep hE
  exact ⟨P⟩

end HigherDimLQGMetric
