import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockFirstHit.T51FirstHitCost
import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Block




 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay

private theorem innerSphere_mem_annulus {c y : ℂ} {r₁ r₂ : ℝ}
    (hr : r₁ ≤ r₂) (hy : y ∈ sphere c r₁) :
    y ∈ closedBall c r₂ \ ball c r₁ := by
  rw [mem_sphere] at hy
  exact ⟨mem_closedBall.mpr (hy.le.trans hr), fun hb =>
    (not_lt_of_ge hy.ge) (mem_ball.mp hb)⟩

 

theorem annulus_boundary_inf_le_ball_internal
    (D : LSCMetric) {c x : ℂ} {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr : r₁ < r₂) (hx : x ∈ sphere c r₂) :
    (⨅ (y : ℂ) (hy : y ∈ sphere c r₁),
      D.internal (closedBall c r₂ \ ball c r₁)
        (⟨x, by
          exact ⟨sphere_subset_closedBall hx, by
            intro hb
            have hdist := mem_sphere.mp hx
            have hlt := mem_ball.mp hb
            rw [hdist] at hlt
            exact (not_lt_of_ge hr.le) hlt⟩⟩,
         ⟨y, innerSphere_mem_annulus hr.le hy⟩)) ≤
      D.internal (closedBall c r₂)
        (⟨x, sphere_subset_closedBall hx⟩, ⟨c, mem_closedBall_self (hr₁.trans hr.le)⟩) := by
  conv_rhs => unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hP => le_iInf fun hball => le_iInf fun hstart =>
      le_iInf fun hend => ?_
  have hcont : ContinuousOn P (Icc a b) :=
    hP.continuousOn_of_mapsTo (isCompact_closedBall c r₂) hball
  have ha : dist (P a) c = r₂ := by rwa [hstart]
  have hb : dist (P b) c ≤ r₁ := by rw [hend, dist_self]; exact hr₁
  obtain ⟨t, hat, htt, hatle, htle, hts, hcost⟩ :=
    Objects.BlockFirstHit.annulus_internal_le_ball_path_len D hP hcont hr ha hb hball
  exact (iInf_le_of_le (P t) (iInf_le_of_le hts (by
    simpa only [hstart] using hcost)))


private theorem outerSphere_mem_annulus {c x : ℂ} {r₁ r₂ : ℝ}
    (hr : r₁ < r₂) (hx : x ∈ sphere c r₂) :
    x ∈ closedBall c r₂ \ ball c r₁ := by
  exact ⟨sphere_subset_closedBall hx, fun hb => by
    have hdist := mem_sphere.mp hx
    have hlt := mem_ball.mp hb
    rw [hdist] at hlt
    exact (not_lt_of_ge hr.le) hlt⟩

def annulusBoundaryCost (D : LSCMetric) {c : ℂ} {r₁ r₂ : ℝ}
    (hr : r₁ < r₂) (x : sphere c r₂) : ENNReal :=
  ⨅ (y : ℂ) (hy : y ∈ sphere c r₁),
    D.internal (closedBall c r₂ \ ball c r₁)
      (⟨x, outerSphere_mem_annulus hr x.property⟩,
       ⟨y, innerSphere_mem_annulus hr.le hy⟩)

def ballBoundaryCost (D : LSCMetric) {c : ℂ} {r₂ : ℝ}
    (hr₂ : 0 ≤ r₂) (x : sphere c r₂) : ENNReal :=
  D.internal (closedBall c r₂)
    (⟨x, sphere_subset_closedBall x.property⟩,
     ⟨c, mem_closedBall_self hr₂⟩)

theorem annulusBoundaryCost_le_ballBoundaryCost (D : LSCMetric)
    {c : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr : r₁ < r₂)
    (x : sphere c r₂) :
    annulusBoundaryCost D hr x ≤ ballBoundaryCost D (hr₁.trans hr.le) x := by
  exact annulus_boundary_inf_le_ball_internal D hr₁ hr x.property

theorem annulus_bad_subset_ball_bad (D : LSCMetric)
    {c : ℂ} {r₁ r₂ : ℝ} {B : ENNReal} (hr₁ : 0 ≤ r₁) (hr : r₁ < r₂) :
    {x : ℂ | ∃ hx : x ∈ sphere c r₂,
      B < annulusBoundaryCost D hr ⟨x, hx⟩} ⊆
    {x : ℂ | ∃ hx : x ∈ sphere c r₂,
      B < ballBoundaryCost D (hr₁.trans hr.le) ⟨x, hx⟩} := by
  rintro x ⟨hx, hbad⟩
  exact ⟨hx, hbad.trans_le (annulusBoundaryCost_le_ballBoundaryCost D hr₁ hr ⟨x, hx⟩)⟩

theorem circleOuter_annulus_bad_le_ball_bad (D : LSCMetric)
    {c : ℂ} {r₁ r₂ : ℝ} {B : ENNReal} (hr₁ : 0 ≤ r₁) (hr : r₁ < r₂) :
    Objects.Shadow.circleOuter c r₂.toNNReal 0
      {x : ℂ | ∃ hx : x ∈ sphere c r₂,
        B < annulusBoundaryCost D hr ⟨x, hx⟩} ≤
    Objects.Shadow.circleOuter c r₂.toNNReal 0
      {x : ℂ | ∃ hx : x ∈ sphere c r₂,
        B < ballBoundaryCost D (hr₁.trans hr.le) ⟨x, hx⟩} :=
  Objects.Shadow.circleOuter_mono (annulus_bad_subset_ball_bad D hr₁ hr)


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay
