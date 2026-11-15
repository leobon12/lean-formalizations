/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoFaceNoWrap
import InteractingSLE.Spec.Sec7.Aux37GermFinishFill

/-!
# A free positive-real gate for the contacted outer face

The inverse counterflow chart has a positive original-real boundary value at
some positive chart point. Proper-arc closedness gives a whole ball there
avoiding the closed excursion image. The Aux. 37 filling lemma makes its upper
half-ball either entirely filled or entirely part of the outer face. In the
latter case the desired physical positive-boundary access follows directly.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- A genuine untouched positive-real gate, with both its physical boundary
value and a ball avoiding the entire closed excursion image. -/
structure PositiveBoundaryGate (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ) where
  source : ℝ
  target : ℝ
  radius : ℝ
  source_pos : 0 < source
  target_pos : 0 < target
  radius_pos : 0 < radius
  boundary_limit : Tendsto (revChartInv w s) (𝓝[H] (source : ℂ))
    (𝓝[H] (target : ℂ))
  avoids : ball (source : ℂ) radius ∩ closure (chartFlowSet η w s) = ∅

variable {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}

/-- A positive physical gate exists before making any assumption about the
orientation, number of contacts, or boundedness of the chart excursion set. -/
theorem exists_positiveBoundaryGate (hη : IsProperArc η)
    (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) :
    Nonempty (PositiveBoundaryGate η w s) := by
  obtain ⟨q, y, hq, hy, hlim⟩ := Prop411Q.exists_neg_tendsto_fwdMapInv hβ hw hw0 hs
  let r : ℝ := -q⁻¹
  let x : ℝ := -y⁻¹
  have hr : 0 < r := neg_pos.2 (inv_lt_zero.2 hq)
  have hx : 0 < x := neg_pos.2 (inv_lt_zero.2 hy)
  have hrq : negInv (r : ℂ) = (q : ℂ) := by simp [negInv, r]
  have hinv : Tendsto negInv (𝓝[H] (r : ℂ)) (𝓝[H] (q : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc := (continuousAt_negInv (ofReal_ne_zero.2 hr.ne')).tendsto
      rw [hrq] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz using negInv_mem_H hz
  have hF : Tendsto (revChartInv w s) (𝓝[H] (r : ℂ)) (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · change Tendsto (fun z => negInv (fwdMapInv w s (negInv z)))
        (𝓝[H] (r : ℂ)) (𝓝 (x : ℂ))
      have hc := (continuousAt_negInv (ofReal_ne_zero.2 hy.ne)).tendsto.comp
        (hlim.comp hinv)
      simpa only [revChartInv, negInv, x, ofReal_neg, ofReal_inv,
        Function.comp_def] using hc
    · filter_upwards [self_mem_nhdsWithin] with z hz using (revChartInv_mem hw hw0 hs hz).1
  have hxA : (x : ℂ) ∉ arcRange η := hη.ofReal_notMem_arcRange hx.ne'
  have hfree : ∀ᶠ z in 𝓝[H] (r : ℂ), revChartInv w s z ∉ arcRange η :=
    (hF.mono_right nhdsWithin_le_nhds).eventually
      (hη.isClosed_arcRange.isOpen_compl.mem_nhds hxA)
  obtain ⟨δ, hδ, havoid⟩ := Metric.mem_nhdsWithin_iff.1 hfree
  have hdis : Disjoint (ball (r : ℂ) δ) (chartFlowSet η w s) := by
    refine disjoint_left.2 ?_
    rintro z hzb ⟨p, hp, rfl⟩
    have hzH := revChart_mem_H hw hs hp.2
    have hn := havoid ⟨hzb, hzH⟩
    change revChartInv w s (revChart w s p) ∉ arcRange η at hn
    rw [revChartInv_revChart hw hw0 hs hp.2] at hn
    exact hn hp.1
  exact ⟨⟨r, x, δ, hr, hx, hδ, hF,
    disjoint_iff_inter_eq_empty.1 (hdis.closure_right isOpen_ball)⟩⟩

/-- The free gate half-ball is either entirely outer or entirely filled. The
all-or-nothing assertion is the existing Aux. 37 collar filling lemma. -/
theorem PositiveBoundaryGate.halfBall_dichotomy (g : PositiveBoundaryGate η w s) :
    (ball (g.source : ℂ) g.radius ∩ H ⊆ outerChartFace η w s) ∨
      ball (g.source : ℂ) g.radius ∩ H ⊆ fillH (chartFlowSet η w s) := by
  by_cases h : ∃ z ∈ ball (g.source : ℂ) g.radius ∩ H,
      z ∉ fillH (chartFlowSet η w s)
  · obtain ⟨z, hz, hzf⟩ := h
    have hempty := Sec7.Aux37Germ.inter_fillH_eq_empty_of_avoid g.avoids hz.1 hz.2 hzf
    refine Or.inl (fun v hv => ⟨hv.2, fun hvf => ?_⟩)
    have hm : v ∈ ball (g.source : ℂ) g.radius ∩ fillH (chartFlowSet η w s) :=
      ⟨hv.1, hvf⟩
    rwa [hempty] at hm
  · exact Or.inr (fun z hz => by_contra fun hzf => h ⟨z, hz, hzf⟩)

/-- An outer gate half-ball supplies the original positive-real boundary
access, without any excursion selection or collar-orientation premise. -/
theorem PositiveBoundaryGate.physical_access (g : PositiveBoundaryGate η w s)
    (houter : ball (g.source : ℂ) g.radius ∩ H ⊆ outerChartFace η w s) :
    (g.target : ℂ) ∈ closure (physicalOuterFace η w s) := by
  have : (𝓝[H] (g.source : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1
      (closure_H ▸ mem_Hbar_of_im_eq_zero (by simp))
  have he : ∀ᶠ z in 𝓝[H] (g.source : ℂ),
      revChartInv w s z ∈ physicalOuterFace η w s := by
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds _ g.radius_pos)] with z hz
    exact ⟨z, houter ⟨hz.2, hz.1⟩, rfl⟩
  exact mem_closure_of_tendsto (g.boundary_limit.mono_right nhdsWithin_le_nhds) he

end InteractingSLE.Sec5.Prop51HTopo
