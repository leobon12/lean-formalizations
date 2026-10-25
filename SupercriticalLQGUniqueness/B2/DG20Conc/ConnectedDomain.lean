import LQGMetric.Papers.DG.S3T15
import LQGMetric.Papers.DDDF.P10Tail

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

 



theorem exists_admPath_of_open_connected {U A B : Set ℂ}
    (hU : IsOpen U) (hUc : IsConnected U)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAU : A ⊆ U) (hBU : B ⊆ U) :
    ∃ q : ℝ → ℂ, AdmPath U A B q := by
  obtain ⟨z, hz⟩ := hA
  obtain ⟨w, hw⟩ := hB
  obtain ⟨q, hq⟩ := LQGMetric.DG.t15_exists_isDGPath hU hUc (hAU hz) (hBU hw)
  refine ⟨q, z, hz, w, hw, ?_, ?_⟩
  · exact ⟨hq.source, hq.target, hq.continuousOn, hq.piecewise_contDiff⟩
  · exact fun t ht => hq.mapsTo ht

 



theorem crossLenIn_ne_top_of_open_connected {U A B : Set ℂ}
    (hU : IsOpen U) (hUc : IsConnected U)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAU : A ⊆ U) (hBU : B ⊆ U)
    {ξ : ℝ} {f : ℂ → ℝ} (hf : Continuous f) :
    crossLenIn ξ f U A B ≠ ⊤ := by
  obtain ⟨q, hq⟩ := exists_admPath_of_open_connected hU hUc hA hB hAU hBU
  rcases hq with ⟨z, hz, w, hw, hqp, hqU⟩
  have hqAdm : AdmPath U A B q := ⟨z, hz, w, hw, hqp, hqU⟩
  have hK : IsCompact (q '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hqp.continuousOn
  have hqK : AdmPath (q '' Icc (0 : ℝ) 1) A B q :=
    ⟨z, hz, w, hw, hqp, fun t ht => ⟨t, ht, rfl⟩⟩
  exact ne_top_of_le_ne_top
    (lfppLen_ne_top_of_adm hf hK hqK)
    (crossLenIn_le_lfppLen hqAdm)

 



theorem exists_uniform_tube_of_admPath {U A B : Set ℂ}
    (hU : IsOpen U) {q : ℝ → ℂ} (hq : AdmPath U A B q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      Metric.closedBall (q t) δ ⊆ U := by
  rcases hq with ⟨z, hz, w, hw, hqp, hqU⟩
  have hK : IsCompact (q '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hqp.continuousOn
  have hKU : q '' Icc (0 : ℝ) 1 ⊆ U := by
    rintro x ⟨t, ht, rfl⟩
    exact hqU t ht
  obtain ⟨δ, hδ, htube⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hmem : q t ∈ q '' Icc (0 : ℝ) 1 := ⟨t, ht, rfl⟩
  exact (Metric.closedBall_subset_cthickening hmem δ).trans htube

 

theorem exists_polyJoin_of_open_connected {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsConnected U)
    {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    LQGMetric.DG.T15PolyJoin U z w := by
  let A : Set ℂ := {y | LQGMetric.DG.T15PolyJoin U z y}
  let B : Set ℂ := {y | y ∈ U ∧ ¬ LQGMetric.DG.T15PolyJoin U z y}
  have hA : IsOpen A := by
    refine isOpen_iff.2 fun y hy => ?_
    obtain ⟨r, hr, hrU⟩ := isOpen_iff.1 hU y
      (LQGMetric.DG.t15_polyJoin_mem hy)
    exact ⟨r, hr, fun y' hy' => LQGMetric.DG.t15_polyJoin_snoc hy
      (((convex_ball y r).segment_subset (mem_ball_self hr) hy').trans hrU)⟩
  have hB : IsOpen B := by
    refine isOpen_iff.2 fun y hy => ?_
    obtain ⟨r, hr, hrU⟩ := isOpen_iff.1 hU y hy.1
    refine ⟨r, hr, fun y' hy' => ⟨hrU hy', fun h => hy.2
      (LQGMetric.DG.t15_polyJoin_snoc h
        (((convex_ball y r).segment_subset hy' (mem_ball_self hr)).trans hrU))⟩⟩
  have hsub : U ⊆ A :=
    hUc.isPreconnected.subset_left_of_subset_union hA hB
      (Set.disjoint_left.2 fun y h1 h2 => h2.2 h1)
      (fun y hy => by
        by_cases h : LQGMetric.DG.T15PolyJoin U z y
        · exact Or.inl h
        · exact Or.inr ⟨hy, h⟩)
      ⟨z, hz, LQGMetric.DG.t15_polyJoin_refl hz⟩
  exact hsub hw

end SupercriticalLQGUniqueness.B2.DG20Conc
