/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronData
import InteractingSLE.Spec.Supplement.WalkIntOrientTips

/-!
# Cutting a recorded piece at a full-walk parameter

Own-time monotonicity and continuity give the cut. A finite lifetime may
be retained completely. At an infinite lifetime, trace transience and the
bounded displacement of the physical extension give a finite bracket.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntBoundCut

open WalkBdry WalkWords WalkIntOrient

/-- Every full-walk cutoff beyond a piece's seed is realized by a finite
own-time cutoff, allowing equality with a finite recorded lifetime. -/
theorem exists_piece_clock_cut {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α)
    {pc : Piece} {A : Set ℂ} {f : ℂ → ℂ} {W : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}
    (d : PieceData pc A f W η)
    (hrange : pc.1.tipSet pc.2.1 pc.2.2 ⊆ range α)
    (hmono : StrictMonoOn (fun t => curveTime α (f (η t)))
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ pc.2.2})
    {a : ℝ≥0} (hstart : curveTime α (f (η 0)) ≤ a) :
    ∃ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ pc.2.2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ pc.2.2 →
        (curveTime α (f (η t)) ≤ a ↔ t ≤ τ) := by
  have hmem (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ pc.2.2) : f (η t) ∈ range α := by
    apply hrange
    rw [d.tipSet_eq]
    exact ⟨t, ht, rfl⟩
  have hbracket (T : ℝ≥0) (hT : (T : ℝ≥0∞) ≤ pc.2.2)
      (haT : a ≤ curveTime α (f (η T))) :
      ∃ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ pc.2.2 ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ pc.2.2 →
          (curveTime α (f (η t)) ≤ a ↔ t ≤ τ) := by
    have hI : Icc (0 : ℝ≥0) T ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ pc.2.2} :=
      fun _ ht => (ENNReal.coe_le_coe.2 ht.2).trans hT
    have hc := continuousOn_curveTime hα (d.continuousOn.mono hI)
      (fun _ hz => by obtain ⟨t, ht, rfl⟩ := hz; exact hmem t (hI ht))
    obtain ⟨τ, hτ, heq⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ T from zero_le) hc ⟨hstart, haT⟩
    refine ⟨τ, hI hτ, fun t ht => ?_⟩
    rw [← heq]
    exact hmono.le_iff_le ht (hI hτ)
  by_cases htop : pc.2.2 = ⊤
  · obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := a)).exists_bound_of_continuousOn
      hα.1.continuousOn
    obtain ⟨C, hC⟩ := d.bdd
    obtain ⟨T, hT⟩ := ((d.trans htop).eventually_gt_atTop (M + C)).exists
    have hTS : (T : ℝ≥0∞) ≤ pc.2.2 := by rw [htop]; exact le_top
    have hlarge : a < curveTime α (f (η T)) := by
      by_contra h
      have hclock : curveTime α (f (η T)) ≤ a := le_of_not_gt h
      have hb := hM (curveTime α (f (η T))) ⟨zero_le, hclock⟩
      rw [apply_curveTime (hmem T hTS)] at hb
      have hc := hC (η T) (d.mem_Hbar hTS)
      have hn := norm_sub_norm_le (η T) (f (η T))
      rw [norm_sub_rev] at hn
      linarith only [hT, hb, hc, hn]
    exact hbracket T hTS hlarge.le
  · let T : ℝ≥0 := pc.2.2.toNNReal
    have hTS : (T : ℝ≥0∞) = pc.2.2 := ENNReal.coe_toNNReal htop
    by_cases hTa : curveTime α (f (η T)) ≤ a
    · refine ⟨T, hTS.le, fun t ht => ?_⟩
      have htT : t ≤ T := ENNReal.coe_le_coe.1 (hTS ▸ ht)
      exact iff_of_true ((hmono.monotoneOn ht hTS.le htT).trans hTa) htT
    · exact hbracket T hTS.le (le_of_not_ge hTa)

end InteractingSLE.Theorem14.WalkIntBoundCut
