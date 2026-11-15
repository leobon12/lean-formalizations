/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2TermFresh
import InteractingSLE.Spec.Restart.FCK2TermClock

/-! # Physical terminal access on the actual first-contact source coupling -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Complex
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData MartChar.RealFlow
universe u

/-- At a positive real endpoint of a simple trace, the corresponding zero
side image collides. Both implications include a finite lifetime endpoint. -/
theorem zero_side_collisions_of_simple_real_endpoint {W : ℝ≥0 → ℝ}
    {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ} (hg : IsGeneratingTrace W U γ)
    (hc : Continuous W) (h0 : W 0 = 0) (hi : InjOn γ {s | (s : ℝ≥0∞) ≤ U})
    {T : ℝ≥0} (hT : 0 < T) (hTU : (T : ℝ≥0∞) ≤ U) (him : (γ T).im = 0) :
    ((γ T).re ≤ 0 → rightImg (fun s : ℝ => -W s.toNNReal) 0 T = -W T) ∧
      (0 ≤ (γ T).re → rightImg (fun s : ℝ => W s.toNNReal) 0 T = W T) := by
  have hne : (γ T).re ≠ 0 := by
    intro he
    have hz : γ T = γ 0 := by
      rw [← Sec7.SideHeightBox.ofReal_re_of_im him, he, ofReal_zero, hg.1]
    exact hT.ne' (hi hTU (by simp) hz)
  constructor
  · intro hre
    have hpos : 0 < -(γ T).re := neg_pos.2 (lt_of_le_of_ne hre hne)
    have hir : InjOn (fun s => LP.reflectC (γ s)) {s | (s : ℝ≥0∞) ≤ U} := by
      intro a ha b hb he
      apply hi ha hb
      simpa only [LP.reflectC_reflectC] using congrArg LP.reflectC he
    have hv : LP.reflectC (γ T) = ((-(γ T).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp only [LP.reflectC, neg_re, conj_re, neg_im, conj_im,
        neg_neg, ofReal_re, ofReal_im, him]
    have hz := zero_right_collision_of_simple_real_endpoint
      (W := fun s => -W s) (γ := fun s => LP.reflectC (γ s))
      (LP.isGeneratingTrace_reflect hg) hc.neg (by simp only [h0, neg_zero]) hir hT hTU hpos hv
    exact hz
  · intro hre
    exact zero_right_collision_of_simple_real_endpoint hg hc h0 hi hT hTU
      (lt_of_le_of_ne hre hne.symm) (Sec7.SideHeightBox.ofReal_re_of_im him).symm

/-- The physical terminal-access input is proved from the original source
flow lines, closed clocks, and the actual continuous generating drivers.
Only Lemma 7.7 is needed for the previously landed canonical clock geometry. -/
theorem firstContactK2PhysicalTerminalAccessStatement
    (h77 : Supp10.Lemma77Statement.{u}) : FirstContactK2PhysicalTerminalAccessStatement.{u} := by
  intro κ hκ hκ4 b J hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  have hbAE := ae_canon_terminal_bad_incident_on_chart_side h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd
    hζ₁ hζ₂ hae hcanon hc₁ hc₂ hz₁ hz₂ hg
  have hiAE := ae_canon_injOn_closed_life h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hcanon
  constructor
  · filter_upwards [hbAE, hiAE, hg] with ω hbω hiω hgω hM T hT
    obtain ⟨hT0, him, hside⟩ := (hbω hM).1 T hT
    have hz := zero_side_collisions_of_simple_real_endpoint (hgω hM).1 (hc₁ ω) (hz₁ ω)
      (hiω hM).1 hT0 hT.le him
    have hE := (mem_meetSet_iff.1 hM).1
    exact ⟨him, hside.imp
      (fun hL => ⟨hz.1 (hL.1.trans_le (hd.wordL_nonpos hE)).le, hL.2⟩)
      (fun hR => ⟨hz.2 ((hd.wordR_nonneg hE).trans hR.1.le), hR.2⟩)⟩
  · filter_upwards [hbAE, hiAE, hg] with ω hbω hiω hgω hM T hT
    obtain ⟨hT0, him, hside⟩ := (hbω hM).2 T hT
    have hz := zero_side_collisions_of_simple_real_endpoint (hgω hM).2 (hc₂ ω) (hz₂ ω)
      (hiω hM).2 hT0 hT.le him
    have hE := (mem_meetSet_iff.1 hM).1
    exact ⟨him, hside.imp
      (fun hL => ⟨hz.1 (hL.1.trans_le (hd.wordL_nonpos hE)).le, hL.2⟩)
      (fun hR => ⟨hz.2 ((hd.wordR_nonneg hE).trans hR.1.le), hR.2⟩)⟩

end InteractingSLE.Restart.FCPlumb
