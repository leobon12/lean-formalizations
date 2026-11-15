/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoFaceOrientation
import InteractingSLE.Foundations.OrientationCrosscut

/-!
# Orientation of an excursion collar incident to the outer face

The collar data are an actual clockwise loop sharing an arc, in the opposite
direction, with the Cayley picture of the proper flow line. The winding-number
crossing lemma and conformal invariance of the index prove that the outer face
has a physical right-side point. No side label is assumed in the collar data.
Constructing these data at a contacted excursion is a separate obligation.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)
open _root_.InteractingSLE.Orientation

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt

/-- Compactified physical coordinates for the inverse counterflow chart. -/
def discRevChart (w : ℝ → ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  cayley (revChartInv w s z)

/-- The positively oriented reference loop of the proper flow arc. -/
def flowReferenceLoop (η : ℝ → ℂ) : ℝ → ℂ := crossLoop (toDisc η)

theorem windNum_discRevChart {w : ℝ → ℝ} {s : ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    {γ : ℝ → ℂ} (hc : ContinuousOn γ (Icc 0 1)) (hl : γ 0 = γ 1)
    (hγH : MapsTo γ (Icc 0 1) H) {z : ℂ} (hz : z ∈ H)
    (hγz : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z) :
    windNum (discRevChart w s ∘ γ) (discRevChart w s z) = windNum γ z := by
  have hF := isConformalBijection_revChartInv hw hw0 hs
  have hFd : DifferentiableOn ℂ (discRevChart w s) H :=
    QuantumZipper.CA.differentiableOn_cayley_Hbar.comp hF.1
      (fun z hz => H_subset_Hbar (hF.2.mapsTo hz).1)
  have hFi : InjOn (discRevChart w s) H := by
    intro x hx y hy he
    exact hF.2.injOn hx hy (cayley_injOn_Hbar
      (H_subset_Hbar (hF.2.mapsTo hx).1) (H_subset_Hbar (hF.2.mapsTo hy).1) he)
  exact windNum_comp_of_univalent_H hFd hFi hc hl hγH hz hγz

/-- The global reference index is one on the left of the physical flow line. -/
theorem windNum_flowReferenceLoop_of_mem_left {η : ℝ → ℂ} (hη : IsProperArc η)
    {z : ℂ} (hz : z ∈ leftSideOf (arcRange η)) :
    windNum (flowReferenceLoop η) (cayley z) = 1 :=
  windNum_crossLoop_of_mem_crossSide_one hη.isDiscCrosscut_toDisc
    ((hη.mem_leftSideOf_iff hz.1.1).1 hz)

/-- Off the flow line the global reference index is at most one. -/
theorem windNum_flowReferenceLoop_le_one {η : ℝ → ℂ} (hη : IsProperArc η)
    {z : ℂ} (hzH : z ∈ H) (hzA : z ∉ arcRange η) :
    windNum (flowReferenceLoop η) (cayley z) ≤ 1 := by
  rcases hη.mem_leftSideOf_or_mem_rightSideOf hzH hzA with hzL | hzR
  · exact (windNum_flowReferenceLoop_of_mem_left hη hzL).le
  · have hα := hη.isDiscCrosscut_toDisc
    have hcl : flowReferenceLoop η '' Icc 0 1 ⊆ closure (crossSide (toDisc η) 1) := by
      intro v hv
      rcases image_crossLoop_subset hα.one hv with h | h
      · exact hα.crossRange_subset_closure_crossSide (Or.inl rfl) h
      · exact hα.semiArc_subset_closure_crossSide (Or.inl rfl) h
    have hz0 := windNum_eq_zero_of_mem_crossSide_neg hα
      (continuousOn_crossLoop hα.cont hα.one) (crossLoop_loop hα.zero hα.one)
      hcl ((hη.mem_rightSideOf_iff hzH).1 hzR)
    change windNum (flowReferenceLoop η) (cayley z) = 0 at hz0
    rw [hz0]
    norm_num

/-- Finite collar data at an excursion incident to the outer face. The inner
and outer labels are winding indices in chart space, not physical side labels.
All common-arc and remainder-avoidance data are those of the existing crossing
lemma, making their construction an explicit geometric obligation. -/
structure OuterFaceCollar (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ) where
  loop : ℝ → ℂ
  loop_cont : ContinuousOn loop (Icc 0 1)
  loop_closed : loop 0 = loop 1
  loop_H : MapsTo loop (Icc 0 1) H
  common : ℝ → ℂ
  common_cont : ContinuousOn common (Icc 0 1)
  common_inj : InjOn common (Icc 0 1)
  common_flow : common '' Icc 0 1 ⊆ crossRange (toDisc η)
  s₀ : ℝ
  s₁ : ℝ
  t₀ : ℝ
  t₁ : ℝ
  s₀_nonneg : 0 ≤ s₀
  s_le : s₀ ≤ s₁
  s₁_le : s₁ ≤ 1
  t₀_nonneg : 0 ≤ t₀
  t_le : t₀ ≤ t₁
  t₁_le : t₁ ≤ 1
  flow_common : MapsTo (flowReferenceLoop η) (Icc s₀ s₁) (common '' Icc 0 1)
  loop_common : MapsTo (discRevChart w s ∘ loop) (Icc t₀ t₁) (common '' Icc 0 1)
  common_start : flowReferenceLoop η s₀ = discRevChart w s (loop t₁)
  common_end : flowReferenceLoop η s₁ = discRevChart w s (loop t₀)
  point : ℂ
  point_off_rest : point ∉
    flowReferenceLoop η '' Icc 0 s₀ ∪ flowReferenceLoop η '' Icc s₁ 1 ∪
      (discRevChart w s ∘ loop) '' Icc 0 t₀ ∪
      (discRevChart w s ∘ loop) '' Icc t₁ 1
  outer_closure : point ∈ closure (discRevChart w s '' outerChartFace η w s)
  outer_index : ∀ z ∈ outerChartFace η w s, windNum loop z = 0
  outer_avoid : ∀ z ∈ outerChartFace η w s, ∀ t ∈ Icc (0 : ℝ) 1, loop t ≠ z
  inner : Set ℂ
  inner_H : inner ⊆ H
  inner_avoid_flow : ∀ z ∈ inner, revChartInv w s z ∉ arcRange η
  inner_closure : point ∈ closure (discRevChart w s '' inner)
  inner_index : ∀ z ∈ inner, windNum loop z = -1
  inner_avoid : ∀ z ∈ inner, ∀ t ∈ Icc (0 : ℝ) 1, loop t ≠ z

/-- A clockwise collar proves the required physical orientation. If the outer
point were on the left, cancellation along the common arc would force reference
index two at an inner point. A proper arc has reference index at most one. -/
theorem exists_rightSide_of_outerFaceCollar {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}
    (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (c : OuterFaceCollar η w s) :
    ∃ z ∈ outerChartFace η w s, revChartInv w s z ∈ rightSideOf (arcRange η) := by
  have hα := hη.isDiscCrosscut_toDisc
  have hδc : ContinuousOn (discRevChart w s ∘ c.loop) (Icc 0 1) :=
    QuantumZipper.CA.differentiableOn_cayley_Hbar.continuousOn.comp
      ((continuousOn_revChartInv hw hw0 hs).comp c.loop_cont c.loop_H)
      (fun t ht => H_subset_Hbar (revChartInv_mem hw hw0 hs (c.loop_H ht)).1)
  obtain ⟨ε, hε, hcross⟩ := windNum_add_windNum_eq
    (continuousOn_crossLoop hα.cont hα.one) hδc
    (crossLoop_loop hα.zero hα.one) (congrArg (discRevChart w s) c.loop_closed)
    (fun z hz => hasLogOn_sub_image_Icc zero_lt_one c.common_cont c.common_inj hz)
    c.s₀_nonneg c.s_le c.s₁_le c.t₀_nonneg c.t_le c.t₁_le
    c.flow_common c.loop_common c.common_start c.common_end c.point_off_rest
  obtain ⟨_, ⟨u, hu, rfl⟩, hdu⟩ := Metric.mem_closure_iff.1 c.outer_closure ε hε
  obtain ⟨_, ⟨v, hv, rfl⟩, hdv⟩ := Metric.mem_closure_iff.1 c.inner_closure ε hε
  have huP := physicalOuterFace_subset hw hw0 hs ⟨u, hu, rfl⟩
  have hvH := (revChartInv_mem hw hw0 hs (c.inner_H hv)).1
  have huA : discRevChart w s u ∉ c.common '' Icc 0 1 := by
    intro h
    exact huP.2 ((hη.cayley_mem_crossRange_iff (H_subset_Hbar huP.1)).1 (c.common_flow h))
  have hvA : discRevChart w s v ∉ c.common '' Icc 0 1 := by
    intro h
    exact c.inner_avoid_flow v hv
      ((hη.cayley_mem_crossRange_iff (H_subset_Hbar hvH)).1 (c.common_flow h))
  have heq := hcross (discRevChart w s u)
    (by simpa only [mem_ball, dist_comm] using hdu) (discRevChart w s v)
    (by simpa only [mem_ball, dist_comm] using hdv) huA hvA
  have hδu : windNum (discRevChart w s ∘ c.loop) (discRevChart w s u) = 0 :=
    (windNum_discRevChart hw hw0 hs c.loop_cont c.loop_closed c.loop_H hu.1
      (c.outer_avoid u hu)).trans (c.outer_index u hu)
  have hδv : windNum (discRevChart w s ∘ c.loop) (discRevChart w s v) = -1 :=
    (windNum_discRevChart hw hw0 hs c.loop_cont c.loop_closed c.loop_H (c.inner_H hv)
      (c.inner_avoid v hv)).trans (c.inner_index v hv)
  refine ⟨u, hu, (hη.mem_leftSideOf_or_mem_rightSideOf huP.1 huP.2).resolve_left ?_⟩
  intro huL
  have hu1 := windNum_flowReferenceLoop_of_mem_left hη huL
  have hvle := windNum_flowReferenceLoop_le_one hη hvH (c.inner_avoid_flow v hv)
  change windNum (flowReferenceLoop η) (discRevChart w s u) = 1 at hu1
  change windNum (flowReferenceLoop η) (discRevChart w s v) ≤ 1 at hvle
  change windNum (flowReferenceLoop η) (discRevChart w s u) + _ =
    windNum (flowReferenceLoop η) (discRevChart w s v) + _ at heq
  rw [hδu, hδv, hu1] at heq
  omega

end InteractingSLE.Sec5.Prop51HTopo
