import SupercriticalLQGUniqueness.Exponent.InwardMap.TracePartition




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

theorem mapped_segment_trace (a : ℚ) (ha0 : 0 ≤ a) (p q : ℚ × ℚ)
    {n : ℕ} {t : Fin (n+1) → ℚ} (hm : StrictMono t)
    (hzero : t 0 = 0) (hone : t (Fin.last n) = 1)
    (hr : Finset.univ.image t = ratSegmentCuts p q) :
    (mappedSegmentPolygon a p q n t).path '' Icc (0:ℝ) 1 =
      inwardMap (a:ℝ) '' (segPath (ratComplex p) (ratComplex q) '' Icc (0:ℝ) 1) := by
  let v : ℕ → ℂ := fun j => segPath (ratComplex p) (ratComplex q) (cutTime n t j:ℝ)
  have hvertex : (mappedSegmentPolygon a p q n t).vertex =
      fun j => inwardMap (a:ℝ) (v j) := by
    funext j
    rw [mappedSegmentPolygon_vertex, mappedRatPoint_complex a ha0,
      ratComplex_line]
  change Exponent.PolygonCofinality.polygonPath (mappedSegmentPolygon a p q n t).vertex n '' Icc (0:ℝ) 1 = _
  rw [hvertex]
  have hmap : ∀ j < n, ∀ u ∈ Icc (0:ℝ) 1,
      inwardMap (a:ℝ) (segPath (v j) (v (j+1)) u) =
        segPath (inwardMap (a:ℝ) (v j)) (inwardMap (a:ℝ) (v (j+1))) u := by
    intro j hj u hu
    let i : Fin n := ⟨j, hj⟩
    have ht0 : cutTime n t j = t i.castSucc := cutTime_castSucc t i
    have ht1 : cutTime n t (j+1) = t i.succ := cutTime_succ t i
    dsimp only [v]
    rw [ht0, ht1, ← ratComplex_line, ← ratComplex_line]
    exact inwardMap_affine_between_cuts (a:ℝ) p q hm hr i hu
  rw [polygon_trace_map (inwardMap (a:ℝ)) v n hmap]
  have hmono : ∀ j, (cutTime n t j:ℝ) ≤ (cutTime n t (j+1):ℝ) := by
    intro j
    exact_mod_cast cutTime_mono n t hm j
  rw [polygon_trace_of_segment_partition (ratComplex p) (ratComplex q)
    (fun j => (cutTime n t j:ℝ)) hmono n]
  simp [cutTime_zero, cutTime_last, hzero, hone]

 

theorem exists_mapped_segment_polygon (a : ℚ) (ha0 : 0 < a)
    (ha : (a:ℝ) ≤ 1/256) (ξ G : ℝ) (hξ : 0 ≤ ξ) (hG0 : 0 ≤ G)
    (f : ℂ → ℝ)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hG : ∀ z ∈ gradientBox, ‖fderiv ℝ f z‖ ≤ G)
    (p q : ℚ × ℚ) (hpath : ∀ u ∈ Icc (0:ℝ) 1,
      segPath (ratComplex p) (ratComplex q) u ∈ Exponent.PolygonalCost.closedSquareAnnulus) :
    ∃ P : Exponent.PolygonalCost.RatPolygon,
      P.path '' Icc (0:ℝ) 1 =
        inwardMap (a:ℝ) ''
          (segPath (ratComplex p) (ratComplex q) '' Icc (0:ℝ) 1) ∧
      P.path '' Icc (0:ℝ) 1 ⊆ Exponent.PolygonalCost.openSquareAnnulus ∧
      lfppLen ξ f P.path ≤
        ENNReal.ofReal ((5/4:ℝ)*Real.exp
          (32*Real.sqrt 2*ξ*((a:ℝ)*G))) *
        segCost ξ f (ratComplex p) (ratComplex q) := by
  obtain ⟨n, t, hm, hzero, hone, hr⟩ := ratSegmentCuts_partition p q
  refine ⟨mappedSegmentPolygon a p q n t,
    mapped_segment_trace a ha0.le p q hm hzero hone hr, ?_, ?_⟩
  · rw [mapped_segment_trace a ha0.le p q hm hzero hone hr]
    rintro z ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    exact inwardMap_closed_to_open (a:ℝ) (by exact_mod_cast ha0)
      ha (hpath u hu)
  · exact mapped_segment_cost_le a ha0.le ha ξ G hξ hG0 f hfd hG p q
      hpath hm hzero hone hr


end SupercriticalLQGUniqueness.Exponent.InwardMap
