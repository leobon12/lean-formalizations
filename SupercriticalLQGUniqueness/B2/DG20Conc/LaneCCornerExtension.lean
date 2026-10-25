import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerStrictEndpoints
import LQGMetric.Topo.RectMeet

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

def laneCLeftBottomExtension (α : ℝ → ℂ) : ℝ → ℂ :=
  SupercriticalLQGUniqueness.B2.Strong.seg
    (SupercriticalLQGUniqueness.B2.Strong.glue4
      (fun _ => α 1)
      (SupercriticalLQGUniqueness.B2.Strong.seg α 1 0)
      (fun t => ((1 - t : ℝ) : ℂ) * α 0)
      (fun _ => 0)) 0 4

theorem laneC_left_bottom_extension_continuous
    {α : ℝ → ℂ} (hα : ContinuousOn α (Icc (0 : ℝ) 1)) :
    ContinuousOn (laneCLeftBottomExtension α) (Icc (0 : ℝ) 1) := by
  have hrev := SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hα
    (show (1 : ℝ) ∈ Icc 0 1 by simp)
    (show (0 : ℝ) ∈ Icc 0 1 by simp)
  have hscale : ContinuousOn (fun t : ℝ => ((1 - t : ℝ) : ℂ) * α 0)
      (Icc (0 : ℝ) 1) := by fun_prop
  have hG := SupercriticalLQGUniqueness.B2.Strong.continuousOn_glue4
    (fun _ => α 1) (SupercriticalLQGUniqueness.B2.Strong.seg α 1 0)
    (fun t => ((1 - t : ℝ) : ℂ) * α 0) (fun _ => 0)
    continuousOn_const hrev hscale continuousOn_const
    (by simp [SupercriticalLQGUniqueness.B2.Strong.seg])
    (by simp [SupercriticalLQGUniqueness.B2.Strong.seg])
    (by simp)
  exact SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hG
    (show (0 : ℝ) ∈ Icc 0 4 by simp)
    (show (4 : ℝ) ∈ Icc 0 4 by simp)

theorem laneC_left_bottom_extension_ends (α : ℝ → ℂ) :
    laneCLeftBottomExtension α 0 = α 1 ∧
      laneCLeftBottomExtension α 1 = 0 := by
  constructor
  · simp [laneCLeftBottomExtension, SupercriticalLQGUniqueness.B2.Strong.seg,
      SupercriticalLQGUniqueness.B2.Strong.glue4]
  · norm_num [laneCLeftBottomExtension, SupercriticalLQGUniqueness.B2.Strong.seg,
      SupercriticalLQGUniqueness.B2.Strong.glue4]

theorem laneC_left_bottom_extension_square
    {α : ℝ → ℂ}
    (hαsq : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ (rectAB 1 1).toSet)
    (hleft : (α 0).re = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      laneCLeftBottomExtension α t ∈ (rectAB 1 1).toSet := by
  let S := (rectAB 1 1).toSet
  have hα0 : α 0 ∈ S := hαsq 0 (by simp)
  have hα1 : α 1 ∈ S := hαsq 1 (by simp)
  have hvertical : ∀ t ∈ Icc (0 : ℝ) 1,
      ((1 - t : ℝ) : ℂ) * α 0 ∈ S := by
    intro t ht
    have h0 := mem_rectAB_toSet.mp hα0
    apply mem_rectAB_toSet.mpr
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hleft, mul_zero]
    constructor
    · constructor <;> norm_num
    · constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) h0.2.1]
      · nlinarith [h0.2.2, mul_nonneg ht.1 h0.2.1]
  have hG : ∀ t ∈ Icc (0 : ℝ) 4,
      SupercriticalLQGUniqueness.B2.Strong.glue4
        (fun _ => α 1)
        (SupercriticalLQGUniqueness.B2.Strong.seg α 1 0)
        (fun u => ((1 - u : ℝ) : ℂ) * α 0)
        (fun _ => 0) t ∈ S := by
    apply SupercriticalLQGUniqueness.B2.Strong.mapsTo_glue4
    · intro _ _; exact hα1
    · exact SupercriticalLQGUniqueness.B2.Strong.mapsTo_seg hαsq
        (by simp) (by simp)
    · exact hvertical
    · intro _ _
      apply mem_rectAB_toSet.mpr
      norm_num
  intro t ht
  exact SupercriticalLQGUniqueness.B2.Strong.mapsTo_seg hG
    (show (0 : ℝ) ∈ Icc 0 4 by simp)
    (show (4 : ℝ) ∈ Icc 0 4 by simp) ht

 

theorem laneC_left_bottom_extension_trace
    {α : ℝ → ℂ}
    (hα0sq : α 0 ∈ (rectAB 1 1).toSet)
    (hleft : (α 0).re = 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∃ u ∈ Icc (0 : ℝ) 1,
      laneCLeftBottomExtension α t = α u) ∨
      ((laneCLeftBottomExtension α t).re = 0 ∧
       (laneCLeftBottomExtension α t).im ≤ (α 0).im) := by
  have h0im : 0 ≤ (α 0).im := (mem_rectAB_toSet.mp hα0sq).2.1
  have ht4lo : 0 ≤ t * 4 := by nlinarith [ht.1]
  have ht4hi : t * 4 ≤ 4 := by nlinarith [ht.2]
  simp only [laneCLeftBottomExtension,
    SupercriticalLQGUniqueness.B2.Strong.seg, sub_zero, zero_add]
  unfold SupercriticalLQGUniqueness.B2.Strong.glue4
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨1, by simp, rfl⟩
  · refine Or.inl ⟨2 - t * 4, ?_, ?_⟩
    · constructor <;> linarith
    · simp [SupercriticalLQGUniqueness.B2.Strong.seg]
      congr 1
      ring
  · right
    have hscale : 0 ≤ 3 - t * 4 ∧ 3 - t * 4 ≤ 1 := by
      constructor <;> linarith
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hleft, mul_zero]
    constructor
    · trivial
    · nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - (3 - t * 4)) h0im]
  · right
    simp [h0im]

 


theorem laneC_corner_arc_meets_positive_crosser
    {α β : ℝ → ℂ}
    (hα : ContinuousOn α (Icc (0 : ℝ) 1))
    (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hαsq : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ (rectAB 1 1).toSet)
    (hβsq : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ (rectAB 1 1).toSet)
    (hαleft : (α 0).re = 0) (hαtop : (α 1).im = 1)
    (hβleft : (β 0).re = 0) (hβright : (β 1).re = 1)
    (horder : (α 0).im < (β 0).im)
    (hβpos : ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → 0 < (β t).re) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ u ∈ Icc (0 : ℝ) 1, β s = α u := by
  let δ := laneCLeftBottomExtension α
  have hδ := laneC_left_bottom_extension_continuous hα
  have hδsq := laneC_left_bottom_extension_square hαsq hαleft
  have hβrect : Set.MapsTo β (Icc (0 : ℝ) 1)
      (LQGMetric.RectCross.rect 0 1 0 1) := by
    intro t ht
    change (β t).re ∈ Icc 0 1 ∧ (β t).im ∈ Icc 0 1
    exact mem_rectAB_toSet.mp (hβsq t ht)
  have hδrect : Set.MapsTo δ (Icc (0 : ℝ) 1)
      (LQGMetric.RectCross.rect 0 1 0 1) := by
    intro t ht
    change (δ t).re ∈ Icc 0 1 ∧ (δ t).im ∈ Icc 0 1
    exact mem_rectAB_toSet.mp (hδsq t ht)
  obtain ⟨s, hs, t, ht, hmeet⟩ :=
    LQGMetric.RectMeet.rect_crossings_meet 0 1 0 1 β δ
      hβ hδ hβrect hδrect hβleft hβright
      (by dsimp [δ]; rw [(laneC_left_bottom_extension_ends α).1]; exact hαtop)
      (by dsimp [δ]; rw [(laneC_left_bottom_extension_ends α).2]; simp)
  rcases laneC_left_bottom_extension_trace
      (hαsq 0 (by simp)) hαleft t ht with ⟨u, hu, heq⟩ | ⟨hre, him⟩
  · exact ⟨s, hs, u, hu, hmeet.trans heq⟩
  · have hs0 : s = 0 := by
      by_contra hn
      have hp := hβpos s hs hn
      rw [hmeet] at hp
      linarith
    subst s
    have him' := congrArg Complex.im hmeet
    linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
