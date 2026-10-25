import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerCrossing
import LQGMetric.Topo.SectorRect

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

def laneCLeftProjection (c : ℂ) : ℂ := ⟨0, c.im⟩

theorem laneC_leftProjection_square {c : ℂ}
    (him0 : 0 ≤ c.im) (him1 : c.im ≤ 1) :
    laneCLeftProjection c ∈ (rectAB 1 1).toSet := by
  apply mem_rectAB_toSet.mpr
  simp [laneCLeftProjection, him0, him1]

theorem laneC_leftProjection_dist {c : ℂ}
    (hcre0 : 0 ≤ c.re) :
    dist (laneCLeftProjection c) c = c.re := by
  have heq : laneCLeftProjection c = c - (c.re : ℂ) := by
    apply Complex.ext <;> simp [laneCLeftProjection]
  rw [heq, dist_eq_norm]
  simp [Complex.norm_real, abs_of_nonneg hcre0]

 


def laneCInnerConnector (c : ℂ) (γ : ℝ → ℂ) (m : ℝ) : ℝ → ℂ :=
  SupercriticalLQGUniqueness.B2.Strong.seg
    (SupercriticalLQGUniqueness.B2.Strong.glue4
      (AffineMap.lineMap (laneCLeftProjection c) (γ m))
      (SupercriticalLQGUniqueness.B2.Strong.seg γ m 1)
      (fun _ => γ 1) (fun _ => γ 1)) 0 4

theorem laneC_innerConnector_continuous
    {c : ℂ} {γ : ℝ → ℂ} {m : ℝ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hm : m ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (laneCInnerConnector c γ m) (Icc (0 : ℝ) 1) := by
  have hline : ContinuousOn
      (AffineMap.lineMap (laneCLeftProjection c) (γ m)) (Icc (0 : ℝ) 1) :=
    AffineMap.lineMap_continuous.continuousOn
  have hseg := SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hγ hm
    (show (1 : ℝ) ∈ Icc 0 1 by simp)
  have hG := SupercriticalLQGUniqueness.B2.Strong.continuousOn_glue4
    (AffineMap.lineMap (laneCLeftProjection c) (γ m))
    (SupercriticalLQGUniqueness.B2.Strong.seg γ m 1)
    (fun _ => γ 1) (fun _ => γ 1)
    hline hseg continuousOn_const continuousOn_const
    (by simp [SupercriticalLQGUniqueness.B2.Strong.seg])
    (by simp [SupercriticalLQGUniqueness.B2.Strong.seg])
    (by rfl)
  exact SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hG
    (show (0 : ℝ) ∈ Icc 0 4 by simp)
    (show (4 : ℝ) ∈ Icc 0 4 by simp)

theorem laneC_innerConnector_ends (c : ℂ) (γ : ℝ → ℂ) (m : ℝ) :
    laneCInnerConnector c γ m 0 = laneCLeftProjection c ∧
      laneCInnerConnector c γ m 1 = γ 1 := by
  constructor
  · simp [laneCInnerConnector, SupercriticalLQGUniqueness.B2.Strong.seg,
      SupercriticalLQGUniqueness.B2.Strong.glue4]
  · norm_num [laneCInnerConnector, SupercriticalLQGUniqueness.B2.Strong.seg,
      SupercriticalLQGUniqueness.B2.Strong.glue4]

theorem laneC_innerConnector_square
    {c : ℂ} {γ : ℝ → ℂ} {m : ℝ}
    (hγsq : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (rectAB 1 1).toSet)
    (hm : m ∈ Icc (0 : ℝ) 1)
    (hcim0 : 0 ≤ c.im) (hcim1 : c.im ≤ 1) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      laneCInnerConnector c γ m t ∈ (rectAB 1 1).toSet := by
  let S := LQGMetric.RectCross.rect 0 1 0 1
  have hγS : Set.MapsTo γ (Icc (0 : ℝ) 1) S := by
    intro t ht
    change (γ t).re ∈ Icc 0 1 ∧ (γ t).im ∈ Icc 0 1
    exact mem_rectAB_toSet.mp (hγsq t ht)
  have hp : laneCLeftProjection c ∈ S := by
    change (laneCLeftProjection c).re ∈ Icc 0 1 ∧
      (laneCLeftProjection c).im ∈ Icc 0 1
    exact mem_rectAB_toSet.mp (laneC_leftProjection_square hcim0 hcim1)
  have hline : Set.MapsTo
      (AffineMap.lineMap (laneCLeftProjection c) (γ m))
      (Icc (0 : ℝ) 1) S :=
    LQGMetric.Sector.convex_rect.mapsTo_lineMap hp (hγS hm)
  have hG : Set.MapsTo
      (SupercriticalLQGUniqueness.B2.Strong.glue4
        (AffineMap.lineMap (laneCLeftProjection c) (γ m))
        (SupercriticalLQGUniqueness.B2.Strong.seg γ m 1)
        (fun _ => γ 1) (fun _ => γ 1)) (Icc (0 : ℝ) 4) S := by
    apply SupercriticalLQGUniqueness.B2.Strong.mapsTo_glue4
    · exact hline
    · exact SupercriticalLQGUniqueness.B2.Strong.mapsTo_seg hγS hm
        (by simp)
    · intro _ _; exact hγS (by simp)
    · intro _ _; exact hγS (by simp)
  intro t ht
  have h := SupercriticalLQGUniqueness.B2.Strong.mapsTo_seg hG
    (show (0 : ℝ) ∈ Icc 0 4 by simp)
    (show (4 : ℝ) ∈ Icc 0 4 by simp) ht
  apply mem_rectAB_toSet.mpr
  exact h

 

theorem laneC_innerConnector_trace
    {c : ℂ} {γ : ℝ → ℂ} {m r : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1)
    (hcre0 : 0 ≤ c.re) (hcreNear : c.re ≤ r)
    (hvisit : dist (γ m) c ≤ r)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (laneCInnerConnector c γ m t) c ≤ r ∨
      ∃ v ∈ Icc m 1, laneCInnerConnector c γ m t = γ v := by
  have hpball : laneCLeftProjection c ∈ closedBall c r := by
    rw [mem_closedBall, laneC_leftProjection_dist hcre0]
    exact hcreNear
  have hmball : γ m ∈ closedBall c r := by
    exact hvisit
  have hline : Set.MapsTo
      (AffineMap.lineMap (laneCLeftProjection c) (γ m))
      (Icc (0 : ℝ) 1) (closedBall c r) :=
    (convex_closedBall c r).mapsTo_lineMap hpball hmball
  have htlo : 0 ≤ t * 4 := by nlinarith [ht.1]
  have hthi : t * 4 ≤ 4 := by nlinarith [ht.2]
  simp only [laneCInnerConnector,
    SupercriticalLQGUniqueness.B2.Strong.seg, sub_zero, zero_add]
  unfold SupercriticalLQGUniqueness.B2.Strong.glue4
  split_ifs with h1 h2 h3
  · left
    exact hline ⟨htlo, h1⟩
  · right
    let v := m + (t * 4 - 1) * (1 - m)
    have hv : v ∈ Icc m 1 := by
      have hu : t * 4 - 1 ∈ Icc (0 : ℝ) 1 :=
        ⟨by linarith, by linarith⟩
      exact SupercriticalLQGUniqueness.B2.Strong.seg_param_mem
        (show m ∈ Icc m 1 by exact ⟨le_rfl, hm.2⟩)
        (show (1 : ℝ) ∈ Icc m 1 by exact ⟨hm.2, le_rfl⟩) hu
    exact ⟨v, hv, rfl⟩
  · exact Or.inr ⟨1, ⟨hm.2, le_rfl⟩, rfl⟩
  · exact Or.inr ⟨1, ⟨hm.2, le_rfl⟩, rfl⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
