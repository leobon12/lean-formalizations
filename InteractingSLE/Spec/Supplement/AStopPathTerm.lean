/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPathMono
import InteractingSLE.Spec.Supplement.AStopPathCore
import InteractingSLE.Spec.Restart.FCK2TermAccess
import InteractingSLE.Spec.Restart.FCK2TermSource
import InteractingSLE.Spec.Restart.FCK2CapAccess

/-!
# The terminal case of the A-stop: the original end is a relative threshold

Packet PROVE-T15-ASTOP-PATH (Lemma G7, p. 498: "a relative threshold there is also an original threshold", read at the
end of the continuation). **`threshold_terminal`** (deterministic): for a retained continuation with the chart facts
(`IsAChart`, `IsAMono`), an untouched word of a fixed force type, and a continuous driver generating the canonical
A-stopped clock, if the continuation runs to the path's own lifetime `ζ` at a point off `K` with a bad original incident
height on its side of the seed (FCK2's `ae_original_terminal_bad_incident` gives this almost surely for flow lines),
and the capacity lifetime `V` is finite, then the continuation threshold condition holds at `V`. Proof: the terminal
chart point `γ V` is real and over `η(ζ)` (`ψ` maps `ℍ` into the domain); its side is the original side (`IsAChart`);
the word's one-sided limits there are the original ones (`IsAChart.limits_of_mono`); the zero-side image collides at a
real terminal tip of the simple canonical trace (FCK2's `zero_side_collisions_of_simple_real_endpoint`); and the
accessed-side criterion (`FCPlumb.threshold_type_geom_iff_accessed_incident_height`) concludes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.RLC.AStopPath

open Supp7 Restart PiecewiseConstantBoundaryData MartChar.RealFlow

section Terminal

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {a : ℝ≥0} {O : Set ℂ} {φ ψ : ℂ → ℂ}

/-- **The original end is a relative threshold** (see the module docstring). -/
theorem threshold_terminal (hR : IsRetCont η ζ x a O φ ψ) (hA : IsAChart ψ (O ∪ η '' Icc 0 a) x)
    (hM : IsAMono ψ (O ∪ η '' Icc 0 a)) {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {c : BoundaryWord}
    (hu : IsUntouchedWord b jumps (O ∪ η '' Icc 0 a) ψ c)
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (htype : c ∈ FCDet.typeSet κ θ nL nR ρL ρR)
    {W : ℝ≥0 → ℝ} (hWc : Continuous W) (hW0 : W 0 = 0)
    (hg : IsGeneratingTrace W (canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0)
      (canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0))
    (hV : canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 ≠ ⊤)
    (hstop : contStop η ζ a (O ∪ η '' Icc 0 a) = ζ) (hoff : η ζ.toNNReal ∉ O ∪ η '' Icc 0 a)
    (hbad : (η ζ.toNNReal).im = 0 ∧
      (((η ζ.toNNReal).re ≤ x ∧ sleLambda κ ≤ leftLim b (η ζ.toNNReal).re + θ * chiC κ) ∨
        (x ≤ (η ζ.toNNReal).re ∧ rightLim b (η ζ.toNNReal).re + θ * chiC κ ≤ -sleLambda κ))) :
    ForceWord.ThresholdCondition ρL ρR
      (W (canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0).toNNReal)
      (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-FCDet.typeXL κ θ nL nR ρL ρR c i)
        (canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0).toNNReal)
      (fun j => rightImg (fun s : ℝ => W s.toNNReal) (FCDet.typeXR κ θ nL nR ρL ρR c j)
        (canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0).toNNReal) := by
  set K := O ∪ η '' Icc 0 a with hKdef
  obtain ⟨hfin, he⟩ := canonRetLife_ne_top hR hV
  obtain ⟨-, -, -, -, hinj, -⟩ := RetAux79.canonRetPath_facts hR
  set V := canonRetLife (H \ fillH K) φ η ζ a K 0 with hVdef
  set γ := canonRetPath (H \ fillH K) φ η ζ a K 0 with hγdef
  have hLle : ((contLife η ζ a K).toNNReal : ℝ≥0∞) ≤ contLife η ζ a K := by rw [ENNReal.coe_toNNReal hfin]
  obtain ⟨hHb, hψ⟩ := hR.contPath_spec hLle
  have hstop' : ((a + (contLife η ζ a K).toNNReal : ℝ≥0) : ℝ≥0∞) = contStop η ζ a K := by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hfin, contLife, add_tsub_cancel_of_le hR.lt_contStop.le]
  have hst : a + (contLife η ζ a K).toNNReal = ζ.toNNReal := by
    rw [← ENNReal.toNNReal_coe (a + (contLife η ζ a K).toNNReal), hstop', hstop]
  rw [hst] at hψ
  rw [← he] at hHb hψ
  -- the terminal chart point is real, over `η ζ`
  have him : (γ V.toNNReal).im = 0 := by
    by_contra hne
    have hH : γ V.toNNReal ∈ H := lt_of_le_of_ne hHb (Ne.symm hne)
    have hD := hR.chart.bijOn_inv.mapsTo hH
    rw [hψ] at hD
    have h0 : (0 : ℝ) < (η ζ.toNNReal).im := hD.1
    linarith [hbad.1]
  have hzr : γ V.toNNReal = (((γ V.toNNReal).re : ℝ) : ℂ) := (ofReal_re_eq him).symm
  have hψw : ψ (((γ V.toNNReal).re : ℝ) : ℂ) = η ζ.toNNReal := by rw [← hzr, hψ]
  have hw : ψ (((γ V.toNNReal).re : ℝ) : ℂ) ∉ K := by rw [hψw]; exact hoff
  obtain ⟨hlL, hlR⟩ := hA.limits_of_mono hM hb hu hw
  rw [hψw] at hlL hlR
  have hVpos : 0 < V.toNNReal := ENNReal.toNNReal_pos (canonRetLife_pos hR).ne' hV
  have hTU : (V.toNNReal : ℝ≥0∞) ≤ V := ENNReal.coe_toNNReal_le_self
  have hacc := FCPlumb.zero_side_collisions_of_simple_real_endpoint hg hWc hW0 hinj hVpos hTU him
  have h0K : ψ ((0 : ℝ) : ℂ) ∈ K := by
    rw [ofReal_zero, hR.tipInv]
    exact Or.inr ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩
  have hw0 : (γ V.toNNReal).re ≠ 0 := fun h => hw (by rw [h]; exact h0K)
  refine (FCPlumb.threshold_type_geom_iff_accessed_incident_height hκ htype hWc hW0 hg hTU).2 ?_
  rcases lt_or_gt_of_ne hw0 with hneg | hpos
  · have hlt := hA.neg _ hw hneg
    rw [hψw] at hlt
    rcases hbad.2 with hL | hR'
    · exact Or.inl ⟨hacc.1 hneg.le, by rw [hlL]; exact hL.2⟩
    · exact absurd hR'.1 (not_le.2 hlt)
  · have hlt := hA.pos _ hw hpos
    rw [hψw] at hlt
    rcases hbad.2 with hL | hR'
    · exact absurd hL.1 (not_le.2 hlt)
    · exact Or.inr ⟨hacc.2 hpos.le, by rw [hlR]; exact hR'.2⟩

end Terminal

end InteractingSLE.RLC.AStopPath
