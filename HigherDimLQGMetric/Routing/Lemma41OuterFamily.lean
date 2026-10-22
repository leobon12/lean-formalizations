import HigherDimLQGMetric.Routing.Lemma41OuterLocal

/-! Images of mesh regions in the annular coordinate metric. -/

set_option autoImplicit false

noncomputable section

open Set Topology HigherDimLFPP LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

def lemma41_outerImage {d : ℕ}
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (A : Set (Rd d)) : Set (MetricFunSpace ρ hρ.metric) :=
  MetricFunSpace.pt ρ hρ.metric '' lemma41_outerSet A

theorem lemma41_outerImage_disjoint {d : ℕ}
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    {A B : Set (Rd d)} (hAB : Disjoint A B) :
    Disjoint (lemma41_outerImage ρ hρ A) (lemma41_outerImage ρ hρ B) := by
  apply Set.disjoint_image_of_injective (by intro x y h; exact h)
  exact disjoint_left.mpr (fun x hx hy => disjoint_left.mp hAB hx hy)

theorem lemma41_outerImage_mono {d : ℕ}
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    {A B : Set (Rd d)} (hAB : A ⊆ B) :
    lemma41_outerImage ρ hρ A ⊆ lemma41_outerImage ρ hρ B :=
  image_mono (preimage_mono hAB)

def lemma41_outerMeshPoint {d : ℕ} {δ : ℝ}
    (hd : 1 ≤ d) (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :
    MetricFunSpace ρ hρ.metric :=
  MetricFunSpace.pt ρ hρ.metric (lemma41_outerPoint hd hδ hsmall v)

def lemma41_outerMeshStar {d : ℕ} {δ : ℝ}
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :
    Set (MetricFunSpace ρ hρ.metric) :=
  lemma41_outerImage ρ hρ (meshStar δ v.1)

def lemma41_outerMeshRegL {d : ℕ} {δ : ℝ}
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (e : T.edgeSet) : Set (MetricFunSpace ρ hρ.metric) :=
  lemma41_outerImage ρ hρ
    (routingRegion δ (Topology.latticePoint δ (lemma41_meshLeft e).1)
      (Topology.latticePoint δ (lemma41_meshRight e).1))

def lemma41_outerMeshRegR {d : ℕ} {δ : ℝ}
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (e : T.edgeSet) : Set (MetricFunSpace ρ hρ.metric) :=
  lemma41_outerImage ρ hρ
    (routingRegion δ (Topology.latticePoint δ (lemma41_meshRight e).1)
      (Topology.latticePoint δ (lemma41_meshLeft e).1))

def lemma41_outerMeshBox {d : ℕ} {δ : ℝ}
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (e : T.edgeSet) : Set (MetricFunSpace ρ hρ.metric) :=
  lemma41_outerImage ρ hρ
    (centralBox δ (Topology.latticePoint δ (lemma41_meshLeft e).1)
      (Topology.latticePoint δ (lemma41_meshRight e).1))

def lemma41_outerMeshRegion {d : ℕ} {δ : ℝ}
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (e : T.edgeSet) (flip : Bool) : Set (MetricFunSpace ρ hρ.metric) :=
  lemma41_outerImage ρ hρ
    (routingRegion δ (Topology.latticePoint δ (lemma41_meshSource e flip).1)
      (Topology.latticePoint δ (lemma41_meshTarget e flip).1))

theorem lemma41_outerMeshRegion_false {d : ℕ} {δ : ℝ}
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (e : T.edgeSet) :
    lemma41_outerMeshRegion ρ hρ e false = lemma41_outerMeshRegL ρ hρ e := rfl

theorem lemma41_outerMeshRegion_true {d : ℕ} {δ : ℝ}
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (e : T.edgeSet) :
    lemma41_outerMeshRegion ρ hρ e true = lemma41_outerMeshRegR ρ hρ e := rfl

theorem lemma41_outer_boxes_disjoint {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (e f : T.edgeSet) (hef : e ≠ f) :
    Disjoint (lemma41_outerMeshBox ρ hρ e) (lemma41_outerMeshBox ρ hρ f) :=
  lemma41_outerImage_disjoint ρ hρ
    (disjoint_centralBox_centralBox hδ
      (lemma41_tree_edge_adj hT e) (lemma41_tree_edge_adj hT f)
      (lemma41_tree_edges_ne e f hef))

theorem lemma41_outer_box_regL_disjoint {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (e f : T.edgeSet) (hef : e ≠ f) :
    Disjoint (lemma41_outerMeshBox ρ hρ e) (lemma41_outerMeshRegL ρ hρ f) :=
  lemma41_outerImage_disjoint ρ hρ
    (disjoint_routingRegion_centralBox hδ
      (lemma41_tree_edge_adj hT f) (lemma41_tree_edge_adj hT e)
      (lemma41_tree_edges_ne f e hef.symm)).symm

theorem lemma41_outer_box_regR_disjoint {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (e f : T.edgeSet) (hef : e ≠ f) :
    Disjoint (lemma41_outerMeshBox ρ hρ e) (lemma41_outerMeshRegR ρ hρ f) :=
  lemma41_outerImage_disjoint ρ hρ
    (disjoint_routingRegion_centralBox hδ
      (lemma41_tree_edge_adj hT f).symm (lemma41_tree_edge_adj hT e)
      (by simpa only [Sym2.eq_swap] using lemma41_tree_edges_ne f e hef.symm)).symm

theorem lemma41_outer_regions_disjoint {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (e f : T.edgeSet) (hef : e ≠ f) (be bf : Bool)
    (hsource : lemma41_meshSource e be ≠ lemma41_meshSource f bf) :
    Disjoint (lemma41_outerMeshRegion ρ hρ e be)
      (lemma41_outerMeshRegion ρ hρ f bf) := by
  have heAdj : (Topology.latticeGraph d).Adj
      (lemma41_meshSource e be).1 (lemma41_meshTarget e be).1 := by
    cases be with
    | false => exact lemma41_tree_edge_adj hT e
    | true => exact (lemma41_tree_edge_adj hT e).symm
  have hfAdj : (Topology.latticeGraph d).Adj
      (lemma41_meshSource f bf).1 (lemma41_meshTarget f bf).1 := by
    cases bf with
    | false => exact lemma41_tree_edge_adj hT f
    | true => exact (lemma41_tree_edge_adj hT f).symm
  have heEq : s((lemma41_meshSource e be).1, (lemma41_meshTarget e be).1) =
      s((lemma41_meshLeft e).1, (lemma41_meshRight e).1) := by
    cases be <;> simp [lemma41_meshSource, lemma41_meshTarget, Sym2.eq_swap]
  have hfEq : s((lemma41_meshSource f bf).1, (lemma41_meshTarget f bf).1) =
      s((lemma41_meshLeft f).1, (lemma41_meshRight f).1) := by
    cases bf <;> simp [lemma41_meshSource, lemma41_meshTarget, Sym2.eq_swap]
  have hne : s((lemma41_meshSource e be).1, (lemma41_meshTarget e be).1) ≠
      s((lemma41_meshSource f bf).1, (lemma41_meshTarget f bf).1) := by
    rw [heEq, hfEq]
    exact lemma41_tree_edges_ne e f hef
  have hsource' : (lemma41_meshSource e be).1 ≠ (lemma41_meshSource f bf).1 := by
    intro h
    exact hsource (Subtype.ext h)
  exact lemma41_outerImage_disjoint ρ hρ
    (lemma41_disjoint_routing_regions hδ heAdj hfAdj hne hsource')

theorem lemma41_outer_region_subset_star {d : ℕ} {δ : ℝ}
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (e : T.edgeSet) (b : Bool) :
    lemma41_outerMeshRegion ρ hρ e b ⊆
      lemma41_outerMeshStar ρ hρ (lemma41_meshSource e b) := by
  have hAdj : (Topology.latticeGraph d).Adj
      (lemma41_meshSource e b).1 (lemma41_meshTarget e b).1 := by
    cases b with
    | false => exact lemma41_tree_edge_adj hT e
    | true => exact (lemma41_tree_edge_adj hT e).symm
  exact lemma41_outerImage_mono ρ hρ (routingRegion_subset_meshStar δ hAdj)

theorem lemma41_outer_box_subset_stars {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (e : T.edgeSet) :
    lemma41_outerMeshBox ρ hρ e ⊆
      lemma41_outerMeshStar ρ hρ (lemma41_meshLeft e) ∩
      lemma41_outerMeshStar ρ hρ (lemma41_meshRight e) := by
  intro x hx
  exact ⟨(lemma41_outerImage_mono ρ hρ
    (centralBox_subset_meshStar hδ (lemma41_tree_edge_adj hT e))) hx,
    (lemma41_outerImage_mono ρ hρ
      (centralBox_subset_meshStar' hδ (lemma41_tree_edge_adj hT e))) hx⟩

theorem lemma41_outer_side_region {d : ℕ} {δ : ℝ}
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hd : 1 ≤ d) (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (Cost : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (a₁ c₃ : ℝ)
    (P : ∀ e : T.edgeSet, Lemma41LocalPiece
      (lemma41_outerMeshPoint hd hδ hsmall ρ hρ (lemma41_meshLeft e))
      (lemma41_outerMeshPoint hd hδ hsmall ρ hρ (lemma41_meshRight e))
      (lemma41_outerMeshRegL ρ hρ e) (lemma41_outerMeshRegR ρ hρ e)
      (lemma41_outerMeshBox ρ hρ e) Cost a₁ c₃)
    (e : T.edgeSet)
    (v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :
    ∃ b : Bool,
      lemma41_side lemma41_meshLeft lemma41_meshRight
        (fun e => (P e).L) (fun e => (P e).R) e v ⊆
          lemma41_outerMeshRegion ρ hρ e b ∧
      ((lemma41_side lemma41_meshLeft lemma41_meshRight
        (fun e => (P e).L) (fun e => (P e).R) e v).Nonempty →
          v = lemma41_meshSource e b) := by
  by_cases hl : lemma41_meshLeft e = v
  · refine ⟨false, ?_, ?_⟩
    · simpa [lemma41_side, hl, lemma41_outerMeshRegion_false] using (P e).Lregion
    · intro _
      exact hl.symm
  · by_cases hr : lemma41_meshRight e = v
    · refine ⟨true, ?_, ?_⟩
      · simpa [lemma41_side, hl, hr, lemma41_outerMeshRegion_true] using (P e).Rregion
      · intro _
        exact hr.symm
    · refine ⟨false, ?_, ?_⟩
      · simp [lemma41_side, hl, hr]
      · intro h
        simp [lemma41_side, hl, hr] at h

theorem lemma41_outer_family_cross {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (hd : 1 ≤ d) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (Cost : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (a₁ c₃ : ℝ)
    (P : ∀ e : T.edgeSet, Lemma41LocalPiece
      (lemma41_outerMeshPoint hd hδ hsmall ρ hρ (lemma41_meshLeft e))
      (lemma41_outerMeshPoint hd hδ hsmall ρ hρ (lemma41_meshRight e))
      (lemma41_outerMeshRegL ρ hρ e) (lemma41_outerMeshRegR ρ hρ e)
      (lemma41_outerMeshBox ρ hρ e) Cost a₁ c₃)
    (e f : T.edgeSet)
    (v w : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))
    (hef : e ≠ f) (hvw : v ≠ w) :
    Disjoint
      (lemma41_side lemma41_meshLeft lemma41_meshRight
        (fun e => (P e).L) (fun e => (P e).R) e v)
      (lemma41_side lemma41_meshLeft lemma41_meshRight
        (fun e => (P e).L) (fun e => (P e).R) f w) := by
  let A := lemma41_side lemma41_meshLeft lemma41_meshRight
    (fun e => (P e).L) (fun e => (P e).R)
  change Disjoint (A e v) (A f w)
  by_cases he : (A e v).Nonempty
  · by_cases hf : (A f w).Nonempty
    · obtain ⟨be, hAe, hve⟩ := lemma41_outer_side_region hd hδ hsmall ρ hρ Cost a₁ c₃ P e v
      obtain ⟨bf, hAf, hwf⟩ := lemma41_outer_side_region hd hδ hsmall ρ hρ Cost a₁ c₃ P f w
      apply Disjoint.mono hAe hAf
      apply lemma41_outer_regions_disjoint hδ hT ρ hρ e f hef be bf
      intro h
      exact hvw ((hve he).trans (h.trans (hwf hf).symm))
    · have hzero : A f w = ∅ := by simpa only [Set.not_nonempty_iff_eq_empty] using hf
      simp [hzero]
  · have hzero : A e v = ∅ := by simpa only [Set.not_nonempty_iff_eq_empty] using he
    simp [hzero]

theorem lemma41_outer_family_box_side {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (hd : 1 ≤ d) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (Cost : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (a₁ c₃ : ℝ)
    (P : ∀ e : T.edgeSet, Lemma41LocalPiece
      (lemma41_outerMeshPoint hd hδ hsmall ρ hρ (lemma41_meshLeft e))
      (lemma41_outerMeshPoint hd hδ hsmall ρ hρ (lemma41_meshRight e))
      (lemma41_outerMeshRegL ρ hρ e) (lemma41_outerMeshRegR ρ hρ e)
      (lemma41_outerMeshBox ρ hρ e) Cost a₁ c₃)
    (e f : T.edgeSet)
    (v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) (hef : e ≠ f) :
    Disjoint (lemma41_outerMeshBox ρ hρ e)
      (lemma41_side lemma41_meshLeft lemma41_meshRight
        (fun e => (P e).L) (fun e => (P e).R) f v) := by
  obtain ⟨b, hsub, _⟩ := lemma41_outer_side_region hd hδ hsmall ρ hρ Cost a₁ c₃ P f v
  apply Disjoint.mono_right hsub
  cases b with
  | false => exact lemma41_outer_box_regL_disjoint hδ hT ρ hρ e f hef
  | true => exact lemma41_outer_box_regR_disjoint hδ hT ρ hρ e f hef

theorem lemma41_outer_family_side_star {d : ℕ} {δ : ℝ}
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (hd : 1 ≤ d) (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (Cost : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (a₁ c₃ : ℝ)
    (P : ∀ e : T.edgeSet, Lemma41LocalPiece
      (lemma41_outerMeshPoint hd hδ hsmall ρ hρ (lemma41_meshLeft e))
      (lemma41_outerMeshPoint hd hδ hsmall ρ hρ (lemma41_meshRight e))
      (lemma41_outerMeshRegL ρ hρ e) (lemma41_outerMeshRegR ρ hρ e)
      (lemma41_outerMeshBox ρ hρ e) Cost a₁ c₃)
    (e : T.edgeSet) (v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :
    lemma41_side lemma41_meshLeft lemma41_meshRight
      (fun e => (P e).L) (fun e => (P e).R) e v ⊆
        lemma41_outerMeshStar ρ hρ v := by
  obtain ⟨b, hsub, hsource⟩ :=
    lemma41_outer_side_region hd hδ hsmall ρ hρ Cost a₁ c₃ P e v
  by_cases hnon : (lemma41_side lemma41_meshLeft lemma41_meshRight
      (fun e => (P e).L) (fun e => (P e).R) e v).Nonempty
  · have h := hsub.trans (lemma41_outer_region_subset_star hT ρ hρ e b)
    simpa only [← hsource hnon] using h
  · have hempty : lemma41_side lemma41_meshLeft lemma41_meshRight
        (fun e => (P e).L) (fun e => (P e).R) e v = ∅ := by
      simpa only [Set.not_nonempty_iff_eq_empty] using hnon
    simp [hempty]

end HigherDimLQGMetric
