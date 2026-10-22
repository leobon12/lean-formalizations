import HigherDimLQGMetric.Routing.Lemma41OuterPair

/-! One routed lattice edge for a coordinate on the open annulus. -/

set_option autoImplicit false

noncomputable section

open Set Topology HigherDimLFPP LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

theorem lemma41_outer_local_piece {d : ℕ} (hd : 3 ≤ d)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    {m n : Fin d → ℤ}
    (hm : m ∈ Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))
    (hn : n ∈ Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))
    (hmn : (Topology.latticeGraph d).Adj m n)
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (hreal : ∀ {O : Set (configOuter d)}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, ρ (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt ρ hρ.metric x)
            (MetricFunSpace.pt ρ hρ.metric y),
          (∀ r, LQGMetric.metricFunSpaceVal ρ hρ.metric (P r) ∈ O) ∧
          pathLength P ≠ ∞)
    (E : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (γ : ℝ → configOuter d) (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1))
    (hγbox : ∀ r ∈ Icc (0 : ℝ) 1,
      (γ r).1 ∈ centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n))
    (hγlen : curveLength (MetricFunSpace.pt ρ hρ.metric ∘ γ) 0 1 ≠ ∞)
    {a₁ c₂ c₃ : ℝ} (ha₁ : 0 < a₁) (hc₂ : 0 ≤ c₂) (hc₂₃ : c₂ < c₃)
    (hsep : a₁ ≤ ρ (γ 0, γ 1))
    (hE : curveLengthWith E (MetricFunSpace.pt ρ hρ.metric ∘ γ) 0 1 ≤
      ENNReal.ofReal (c₂ * ρ (γ 0, γ 1))) :
    ∃ P : Lemma41LocalPiece
      (MetricFunSpace.pt ρ hρ.metric
        (lemma41_outerPoint (by omega : 1 ≤ d) hδ hsmall ⟨m, hm⟩))
      (MetricFunSpace.pt ρ hρ.metric
        (lemma41_outerPoint (by omega : 1 ≤ d) hδ hsmall ⟨n, hn⟩))
      (MetricFunSpace.pt ρ hρ.metric ''
        lemma41_outerSet (routingRegion δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)))
      (MetricFunSpace.pt ρ hρ.metric ''
        lemma41_outerSet (routingRegion δ (Topology.latticePoint δ n) (Topology.latticePoint δ m)))
      (MetricFunSpace.pt ρ hρ.metric ''
        lemma41_outerSet (centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)))
      E a₁ c₃,
      P.σ '' Icc (0 : ℝ) 1 ⊆
        MetricFunSpace.pt ρ hρ.metric '' (γ '' Icc (0 : ℝ) 1) ∧
      ∃ s t : ℝ, 0 < s ∧ s < t ∧ t < 1 ∧
        P.σ = (fun r => MetricFunSpace.pt ρ hρ.metric (γ (s + (t - s) * r))) := by
  let pγ : ℝ → MetricFunSpace ρ hρ.metric := MetricFunSpace.pt ρ hρ.metric ∘ γ
  have hpγc : ContinuousOn pγ (Icc 0 1) :=
    hρ.pt_continuous.continuousOn.comp hγc (fun _ _ => mem_univ _)
  have hsep' : a₁ ≤ dist (pγ 0) (pγ 1) := by
    simpa only [pγ, Function.comp_apply, MetricFunSpace.dist_pt] using hsep
  obtain ⟨s, t, hs, hst, ht, hmarksep, hmarkE⟩ :=
    lemma41_trim E pγ hpγc ha₁ hc₂ hc₂₃ hsep' hE
  let v : configOuter d := lemma41_outerPoint (by omega : 1 ≤ d) hδ hsmall ⟨m, hm⟩
  let w : configOuter d := lemma41_outerPoint (by omega : 1 ≤ d) hδ hsmall ⟨n, hn⟩
  let Ωl := routingRegion δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)
  let Ωr := routingRegion δ (Topology.latticePoint δ n) (Topology.latticePoint δ m)
  have hγboxv : MapsTo (Subtype.val ∘ γ) (Icc (0 : ℝ) 1)
      (centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)) := hγbox
  have hreg : Lemma41EdgeRegions (fun p : Rd d × Rd d => dist p.1 p.2)
      (Subtype.val ∘ γ) s t v.1 w.1 Ωl Ωr := by
    exact lemma41_mesh_edgeRegions hδ hmn (fun p : Rd d × Rd d => dist p.1 p.2)
      (Subtype.val ∘ γ) hγboxv ⟨hs, hst, ht⟩
  have hΩlU : Ωl ⊆ configOuter d :=
    lemma41_outer_region_subset (by omega : 1 ≤ d) hδ hsmall hm hmn
  have hΩrU : Ωr ⊆ configOuter d :=
    lemma41_outer_region_subset (by omega : 1 ≤ d) hδ hsmall hn hmn.symm
  obtain ⟨u, q, hu, hus, htq, hq, βl, βr, hβlc, hβli, hβllen,
    hβl0, hβl1, hβlreg, hβlavoid, hβrc, hβri, hβrlen, hβr0,
    hβr1, hβrreg, hβravoidl, hβravoid⟩ :=
    lemma41_outer_pair_connectors hd ρ hρ hreal γ hγc hγi s t v w Ωl Ωr
      hreg hΩlU hΩrU
  let φ : ℝ → ℝ := fun r => s + (t - s) * r
  let σ : ℝ → MetricFunSpace ρ hρ.metric := pγ ∘ φ
  have hφc : Continuous φ := continuous_const.add (continuous_const.mul continuous_id)
  have hφmem : MapsTo φ (Icc (0 : ℝ) 1) (Icc s t) := by
    intro r hr
    constructor <;> dsimp [φ] <;> nlinarith [mul_nonneg (sub_pos.mpr hst).le hr.1,
      mul_le_of_le_one_right (sub_pos.mpr hst).le hr.2]
  have hφmono : MonotoneOn φ (Icc (0 : ℝ) 1) := by
    intro a _ b _ hab
    dsimp [φ]
    simpa only [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_left hab (sub_pos.mpr hst).le) s)
  have hσc : ContinuousOn σ (Icc 0 1) :=
    (hpγc.mono (Icc_subset_Icc hs.le ht.le)).comp hφc.continuousOn hφmem
  have hpγi : InjOn pγ (Icc (0 : ℝ) 1) := by
    intro a ha b hb heq
    exact hγi ha hb heq
  have hσi : InjOn σ (Icc (0 : ℝ) 1) := by
    intro a ha b hb heq
    have hφeq := hpγi (Icc_subset_Icc hs.le ht.le (hφmem ha))
      (Icc_subset_Icc hs.le ht.le (hφmem hb)) heq
    dsimp [φ] at hφeq
    have hdiff : t - s ≠ 0 := ne_of_gt (sub_pos.mpr hst)
    nlinarith
  have hσ0 : σ 0 = pγ s := by simp [σ, φ]
  have hσ1 : σ 1 = pγ t := by simp [σ, φ]
  have hσE : curveLengthWith E σ 0 1 = curveLengthWith E pγ s t := by
    calc
      curveLengthWith E σ 0 1 = curveLengthWith E pγ (φ 0) (φ 1) :=
        curveLengthWith_comp_monotoneOn E pγ (by norm_num : (0 : ℝ) ≤ 1)
          hφc.continuousOn hφmono
      _ = curveLengthWith E pγ s t := by
        simp only [φ, mul_zero, mul_one, add_zero]
        congr 1
        ring
  have hσsep : a₁ / 2 < dist (σ 0) (σ 1) := by
    simpa only [hσ0, hσ1] using hmarksep
  have hσshort : curveLengthWith E σ 0 1 <
      ENNReal.ofReal (c₃ * dist (σ 0) (σ 1)) := by
    simpa only [hσ0, hσ1, hσE] using hmarkE
  have hσeq : σ = (fun r => pγ (s + (t - s) * r)) := rfl
  let K : Set (MetricFunSpace ρ hρ.metric) :=
    βl '' Icc (0 : ℝ) 1 ∪ pγ '' Icc 0 1 ∪ βr '' Icc 0 1
  let L : Set (MetricFunSpace ρ hρ.metric) :=
    βl '' Icc (0 : ℝ) 1 ∪ pγ '' Icc 0 s
  let R : Set (MetricFunSpace ρ hρ.metric) :=
    βr '' Icc (0 : ℝ) 1 ∪ pγ '' Icc t 1
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
  have hσbox : σ '' Icc (0 : ℝ) 1 ⊆
      MetricFunSpace.pt ρ hρ.metric ''
        lemma41_outerSet (centralBox δ (Topology.latticePoint δ m)
          (Topology.latticePoint δ n)) := by
    rw [hσfull]
    rintro x ⟨r, hr, rfl⟩
    exact ⟨γ r, hγbox r ((Icc_subset_Icc hs.le ht.le) hr), rfl⟩
  refine ⟨⟨K, L, R, σ, hgraph, ?_, ?_, ?_, ?_,
    hcomp.1, hcomp.2.1, hcomp.2.2.1, hcomp.2.2.2.1, hcomp.2.2.2.2.2,
    ?_, ?_, ?_, ?_, hσbox, hσc, hσi, hσsep, hσshort⟩, ?_, ?_⟩
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
      have hbox : (γ r).1 ∈ centralBox δ (Topology.latticePoint δ m)
          (Topology.latticePoint δ n) :=
        hγbox r (Icc_subset_Icc le_rfl (hst.trans ht).le hr)
      exact ⟨γ r, centralBox_subset_routingRegion hδ (dist_latticePoint_of_adj hδ hmn)
        hbox, rfl⟩
  · rintro x (hxβ | hxγ)
    · obtain ⟨r, hr, rfl⟩ := hxβ
      exact ⟨LQGMetric.metricFunSpaceVal ρ hρ.metric (βr r), hβrreg r hr, rfl⟩
    · obtain ⟨r, hr, rfl⟩ := hxγ
      have hbox : (γ r).1 ∈ centralBox δ (Topology.latticePoint δ m)
          (Topology.latticePoint δ n) :=
        hγbox r (Icc_subset_Icc (hs.trans hst).le le_rfl hr)
      exact ⟨γ r, centralBox_subset_routingRegion_swap hδ
        (dist_latticePoint_of_adj hδ hmn) hbox, rfl⟩
  · rw [hσfull]
    rintro x ⟨r, hr, rfl⟩
    exact ⟨γ r, ⟨r, (Icc_subset_Icc hs.le ht.le) hr, rfl⟩, rfl⟩
  · exact ⟨s, t, hs, hst, ht, hσeq⟩

end HigherDimLQGMetric
