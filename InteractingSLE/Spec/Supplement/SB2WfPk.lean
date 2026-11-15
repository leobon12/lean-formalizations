/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfPf
import InteractingSLE.Spec.Supplement.GB7aCmp
import InteractingSLE.Spec.Supplement.G12Low
import InteractingSLE.Spec.Supplement.SB2VrBad

/-!
# A flow line avoids the forbidden set before its lifetime

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). Let `η` be the angle-`θ` flow line from `0` of a GFF with
data `b'`, and `β` a word with `β.fn = b'` off a finite set. Almost surely `η` does not visit `forb κ θ β` before its
lifetime (`ae_avoid_forb`):

* right points of right weight `≤ −2` and left points of left weight `≤ −2` are bad points of the flow-line word
  (`Vr.cumWeightRight_rightLim_flowLine`), never visited before the lifetime (`Vr.trace_ne_of_bad`);
* the finitely many jumps of `β`, of `b'` and the exceptional points: G12 (`g12FlowStatement`) when the beyond weight
  is `> κ/2 − 4`, and otherwise they are bad;
* the remaining left points of left weight `≥ κ/2 − 2`: GB7a (`GB7aFlowStatement.ae_forall`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

universe u

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim)

/-- One-sided limits ignore finite sets (right). -/
theorem rightLim_eq_of_eq_off {f f' : ℝ → ℝ} {J F : Finset ℝ} (hf' : IsPiecewiseConstantBoundaryData f' J)
    (hff : ∀ y ∉ F, f y = f' y) (z : ℝ) : rightLim f z = rightLim f' z := by
  obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem J z
  refine Sec4.rightLim_eq_of_forall_notMem F (a := z + δ) (by linarith) fun t ht htF => ?_
  rw [hff t htF]
  exact (rightLim_eq_of_gap hf' (fun w hw => (hδJ w hw).1) ht).symm

/-- One-sided limits ignore finite sets (left). -/
theorem leftLim_eq_of_eq_off {f f' : ℝ → ℝ} {J F : Finset ℝ} (hf' : IsPiecewiseConstantBoundaryData f' J)
    (hff : ∀ y ∉ F, f y = f' y) (z : ℝ) : leftLim f z = leftLim f' z := by
  obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem J z
  refine Sec4.leftLim_eq_of_forall_notMem F (a := z - δ) (by linarith) fun t ht htF => ?_
  rw [hff t htF]
  exact (leftLim_eq_of_gap hf' (fun w hw => (hδJ w hw).2) ht).symm

/-- **A flow line avoids the forbidden set of a word equal to its data off a finite set.** -/
theorem ae_avoid_forb {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q h' b' J')
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b' J' 0 θ Q h' η ζ) {β : BoundaryWord} {F : Finset ℝ}
    (hβ : ∀ y ∉ F, β.fn y = b' y) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η ω t ∉ forb κ θ β := by
  classical
  have hβpc := β.isPiecewiseConstantBoundaryData
  have hd : κ / 2 - 4 < -2 := by linarith
  set N : Finset ℝ := β.jumps ∪ J' ∪ F with hN
  have hη' := hη
  obtain ⟨_, _, W, VL, VR, B, -, hcoup, hgen⟩ := hη'
  have hpath := hcoup.1.2.2.2.2
  have hGB := Supp8.GB7aFlowStatement.ae_forall Supp8.gb7aFlowStatement hκ hκ4 hb' hh hη
  have hG12 : ∀ᵐ ω ∂Q, ∀ y ∈ N, y < 0 →
      κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b' y + θ * chiC κ) → ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y := by
    have h1 : ∀ y ∈ N, ∀ᵐ ω ∂Q, y < 0 →
        κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b' y + θ * chiC κ) → ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω →
          η ω t ≠ y := by
      intro y _
      by_cases hc : y < 0 ∧ κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b' y + θ * chiC κ)
      · filter_upwards [(Supp7.g12FlowStatement κ hκ hκ4 b' J' hb' 0 θ y Q h' hh η ζ hη).2 hc.1 hc.2]
          with ω hω _ _ using hω
      · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hc
    exact (Finset.eventually_all N).2 h1
  filter_upwards [hpath, hgen, hGB, hG12] with ω hp hg hgb hg12 t ht hmem
  obtain ⟨him, hR | ⟨hneg, hL⟩⟩ := hmem
  · -- a bad right point
    obtain ⟨hpos, hbad⟩ := hR
    set z := (η ω t).re with hz
    have hze : η ω t = (z : ℂ) := Complex.ext (by simp [hz]) (by simp [him])
    have hrl := rightLim_eq_of_eq_off hb' hβ z
    have hw := Vr.cumWeightRight_rightLim_flowLine hκ hb' 0 θ hpos
    rw [add_zero, ← hrl] at hw
    have hB : Vq.IsBadPoint (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL κ b' J' 0 θ)
        (flowLineRhoR κ b' J' 0 θ) (z : ℂ) :=
      ⟨by simp, Or.inl ⟨by simp; exact hpos.le, by simp; rw [← hw]; exact hbad⟩⟩
    have := Vr.trace_ne_of_bad hp hg ht hB (by exact_mod_cast hpos.ne')
    apply this
    simp [hze]
  · -- a left point
    set z := (η ω t).re with hz
    have hze : η ω t = (z : ℂ) := Complex.ext (by simp [hz]) (by simp [him])
    have hbadcase : Sec4.cumWeightLeft κ (leftLim b' z + θ * chiC κ) ≤ κ / 2 - 4 → False := by
      intro hS
      have hw := Vr.cumWeightLeft_leftLim_flowLine hκ hb' 0 θ hneg
      rw [add_zero] at hw
      have hB : Vq.IsBadPoint (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL κ b' J' 0 θ)
          (flowLineRhoR κ b' J' 0 θ) (z : ℂ) :=
        ⟨by simp, Or.inr ⟨by simp; exact hneg.le, by simp; rw [← hw]; linarith⟩⟩
      have := Vr.trace_ne_of_bad hp hg ht hB (by exact_mod_cast hneg.ne)
      apply this
      simp [hze]
    by_cases hzN : z ∈ N
    · by_cases hS : κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b' z + θ * chiC κ)
      · exact hg12 z hzN hneg hS t ht.le hze
      · exact hbadcase (not_lt.1 hS)
    · have hzβ : z ∉ β.jumps := fun h => hzN (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have hzJ' : z ∉ J' := fun h => hzN (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      have hzF : z ∉ F := fun h => hzN (Finset.mem_union_right _ h)
      rcases hL with hJ | hgood
      · exact hzβ hJ
      · rw [hβ z hzF] at hgood
        exact (hgb t ht.le z hzJ').2 hneg hgood hze

end InteractingSLE.Theorem14.SB.Wf
