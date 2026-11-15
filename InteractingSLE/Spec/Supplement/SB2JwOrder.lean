/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JtConc

/-!
# SB2(2): the start piece of a pure piece entry, ordered along the walk (D6 v3, item 1)

Packet PROVE-SB2-LIFTSET (round 17). At a pure piece entry (`R` not yet in the launch state's physical part) the start
piece runs from its seed (in the earlier physical part, so on the head of `β₀`) through `R` (its first visit at
`t_R`). Deterministically:

* **`tip_inter_old_eq`**: a launched piece meets the earlier physical part exactly in its (real) seed;
  **`pcPt_zero_launch`**: the piece starts at the launch state's point;
* `lt_of_mem_old`: when `β₀ t_L ∉` the earlier part, its points are reached before `t_L`;
* **`startPiece_order`**: the piece's points at times `t < t_R` are reached by `β₀` before `t_L`, those at times
  `t_R < t` (before the lifetime) after `t_L` (a cut-point argument: the arcs `[0, t_R]` and `[t_R, t]` of the
  injective piece meet only at `R`, while their `β₀`-time sets are intervals).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- **A launched piece meets the earlier physical part exactly in its seed.** -/
theorem tip_inter_old_eq (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) :
    (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 ∩
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) =
      {((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) : ℝ) : ℂ)} := by
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := stStatus_ne_done_of_launches _ D hl'
  have hpt := (prefix_facts hW.1 hW.2 n).2 hnd
  obtain ⟨f, α, C, -, -, -, -, -, -, -, -, hq₀, -, hcap⟩ := hW.1 n c θ' hl' hpt
  have hti := Lx.instrTime_boundaryWalk_of_launch hl'
  have hc : c = stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) :=
    (eq_launch_of_launches _ D hl').2.2
  rw [hti, hc, hq₀] at hcap
  exact hcap

/-- **A launched piece of positive lifetime starts at the launch state's point.** -/
theorem pcPt_zero_launch (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) :
    pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) 0 =
      ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) : ℝ) : ℂ) := by
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := stStatus_ne_done_of_launches _ D hl'
  have hpt := (prefix_facts hW.1 hW.2 n).2 hnd
  obtain ⟨f, α, C, hf, -, -, hW0, hWc, hα, -, -, hq₀, -, -⟩ := hW.1 n c θ' hl' hpt
  have hti := Lx.instrTime_boundaryWalk_of_launch hl'
  have hc : c = stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) :=
    (eq_launch_of_launches _ D hl').2.2
  rw [hti, min_top_left] at hWc hα
  have hPR := pieceRegular_of_launch hP hl
  have hαT := isGeneratingTrace_trOf hPR
  have hWlt : ContinuousOn (D n).1 {s | (s : ℝ≥0∞) < (D n).2} :=
    hPR.2.1.mono fun s hs => le_of_lt (show (s : ℝ≥0∞) < (D n).2 from hs)
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < (D n).2 := by rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hpos
  have h1 : trOf (D n) 0 = α 0 := by
    rw [← LP.traceAt_eq_of_isGeneratingTrace hαT hWlt hPR.1 h0, LP.traceAt_eq_of_isGeneratingTrace hα hWlt hW0 h0]
  have him := im_nonneg_of_isGeneratingTrace_le hαT hPR.2.1 hPR.1 (le_of_lt h0)
  show LuM.bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) (trOf (D n) 0) = _
  rw [bdVal_eq_of_tendsto him (by rw [← hc]; exact hf _ him), h1, hq₀]

/-- When `β₀ t_L` is not in a preconnected part of the range holding `β₀ 0`, that part is reached before `t_L`. -/
theorem lt_of_mem_old {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) {P : Set ℂ} (hP : P ⊆ range β₀)
    (hPc : IsPreconnected P) (h0 : β₀ 0 ∈ P) {tL : ℝ≥0} (hR : β₀ tL ∉ P) {x : ℝ≥0} (hx : β₀ x ∈ P) : x < tL := by
  have he := isClosedEmbedding_of_isProperCurve hβ
  have hT : IsPreconnected (β₀ ⁻¹' P) := by
    rw [← he.isInducing.isPreconnected_image, image_preimage_eq_of_subset hP]
    exact hPc
  by_contra hle
  push Not at hle
  exact hR (hT.Icc_subset h0 hx ⟨zero_le, hle⟩)

/-- The `β₀`-times of a preconnected part of the range form an interval. -/
theorem Icc_subset_preimage {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) {P : Set ℂ} (hP : P ⊆ range β₀)
    (hPc : IsPreconnected P) {x y : ℝ≥0} (hx : β₀ x ∈ P) (hy : β₀ y ∈ P) : Icc x y ⊆ β₀ ⁻¹' P := by
  have he := isClosedEmbedding_of_isProperCurve hβ
  have hT : IsPreconnected (β₀ ⁻¹' P) := by
    rw [← he.isInducing.isPreconnected_image, image_preimage_eq_of_subset hP]
    exact hPc
  exact hT.Icc_subset hx hy

/-- **The start piece of a pure piece entry, ordered along the walk.** -/
theorem startPiece_order (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0}
    (hRold : β₀ tL ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {sh : ℝ≥0} (hsh : pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) sh = β₀ tL)
    (hshmin : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 →
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = β₀ tL → sh ≤ t)
    (hshL : (sh : ℝ≥0∞) < (D n).2) :
    (∀ t : ℝ≥0, t < sh → ∀ t' : ℝ≥0,
      β₀ t' = pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t → t' < tL) ∧
    (∀ t : ℝ≥0, sh < t → (t : ℝ≥0∞) < (D n).2 → ∀ t' : ℝ≥0,
      β₀ t' = pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t → tL < t') := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  set φ := pcPt s (D n) with hφ
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) _ D hl
  have hpc := continuousOn_pcPt_launch hP hl
  have hinj := pcPt_injOn_launch hP hW hl
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have htipR : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → φ t ∈ range β₀ := fun t ht => by
    rw [hβr]
    exact tipSet_subset_physSet_launch hl (by rw [htip]; exact ⟨t, ht, rfl⟩)
  have hold : statePhysicalSet 0 s ⊆ range β₀ := by
    rw [hβr]; exact statePhysicalSet_subset_physSet hlen.le
  have holdc := (prefix_facts hW.1 hW.2 n).1
  have h0old : β₀ 0 ∈ statePhysicalSet 0 s := by rw [hβ0]; exact Or.inl (Or.inl rfl)
  -- the seed is reached before `t_L`
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hseed : φ 0 ∈ statePhysicalSet 0 s := by
    rw [hφ, pcPt_zero_launch hP hW hl hpos]
    exact (prefix_facts hW.1 hW.2 n).2 (stStatus_ne_done_of_launches _ D hl')
  obtain ⟨ts, hts⟩ := htipR 0 (by rw [ENNReal.coe_zero]; exact zero_le)
  have htsL : ts < tL := lt_of_mem_old hβ hold holdc h0old hRold (by rw [hts]; exact hseed)
  have hφc : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → ContinuousOn φ (Icc 0 t) := fun t ht =>
    hpc.mono fun x hx => le_trans (ENNReal.coe_le_coe.2 hx.2) ht
  have harc : ∀ a t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → φ '' Icc a t ⊆ range β₀ := fun a t ht => by
    rintro _ ⟨x, hx, rfl⟩
    exact htipR x (le_trans (ENNReal.coe_le_coe.2 hx.2) ht)
  have hconn : ∀ a t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → IsPreconnected (φ '' Icc a t) := fun a t ht =>
    isPreconnected_Icc.image _ (hpc.mono fun x hx => le_trans (ENNReal.coe_le_coe.2 hx.2) ht)
  have hshle : (sh : ℝ≥0∞) ≤ (D n).2 := hshL.le
  refine ⟨fun t ht t' ht' => ?_, fun t ht htL t' ht' => ?_⟩
  · -- before `t_R`: the arc `[0, t]` misses `R`
    have htle : (t : ℝ≥0∞) ≤ (D n).2 := le_trans (ENNReal.coe_le_coe.2 ht.le) hshle
    by_contra hge
    push Not at hge
    have hsub := Icc_subset_preimage hβ (harc 0 t htle) (hconn 0 t htle)
      (show β₀ ts ∈ φ '' Icc 0 t from by rw [hts]; exact ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩)
      (show β₀ t' ∈ φ '' Icc 0 t from by rw [ht']; exact ⟨t, ⟨zero_le, le_rfl⟩, rfl⟩)
    obtain ⟨x, hx, hxR⟩ := hsub ⟨htsL.le, hge⟩
    have := hshmin x (le_trans (ENNReal.coe_le_coe.2 hx.2) htle) hxR
    exact absurd (lt_of_le_of_lt (le_trans this hx.2) ht) (lt_irrefl _)
  · -- after `t_R`: the arcs `[0, t_R]` and `[t_R, t]` meet only at `R`
    have htle : (t : ℝ≥0∞) ≤ (D n).2 := htL.le
    by_contra hle
    push Not at hle
    have hne : t' ≠ tL := fun he => by
      have h1 : φ t = φ sh := by rw [← ht', he, hsh]
      exact (ne_of_gt ht) (hinj htL hshL h1)
    have hlt : t' < tL := lt_of_le_of_ne hle hne
    have hsub₀ := Icc_subset_preimage hβ (harc 0 sh hshle) (hconn 0 sh hshle)
      (show β₀ ts ∈ φ '' Icc 0 sh from by rw [hts]; exact ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩)
      (show β₀ tL ∈ φ '' Icc 0 sh from by rw [← hsh]; exact ⟨sh, ⟨zero_le, le_rfl⟩, rfl⟩)
    have hsub₁ := Icc_subset_preimage hβ (harc sh t htle) (hconn sh t htle)
      (show β₀ t' ∈ φ '' Icc sh t from by rw [ht']; exact ⟨t, ⟨ht.le, le_rfl⟩, rfl⟩)
      (show β₀ tL ∈ φ '' Icc sh t from by rw [← hsh]; exact ⟨sh, ⟨le_rfl, ht.le⟩, rfl⟩)
    obtain ⟨x, hx1, hx2⟩ := exists_between (max_lt htsL hlt)
    obtain ⟨a, ha, hax⟩ := hsub₀ ⟨(le_max_left _ _).trans hx1.le, hx2.le⟩
    obtain ⟨b', hb, hbx⟩ := hsub₁ ⟨(le_max_right _ _).trans hx1.le, hx2.le⟩
    have hab : a = b' := hinj (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ha.2) hshL)
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hb.2) htL) (hax.trans hbx.symm)
    have ha' : a = sh := le_antisymm ha.2 (hab ▸ hb.1)
    have hxL : β₀ x = β₀ tL := by rw [← hax, ha', hsh]
    exact absurd (hβ.2.1 hxL) (ne_of_lt hx2)

end InteractingSLE.Theorem14.SB.Lk
