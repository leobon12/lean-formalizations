/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwZero

/-!
# SB2(2): the corner case — the start piece first visits `R` at its end (round 17 finding)

Packet PROVE-SB2-LIFTSET (round 17). At a pure piece entry the start piece may first visit `R` exactly at its end
(`t_R = L₀ < ∞`). Then the shifted lifetime `L₀ − t_R` is `0`, so `Stage0Facts`' field `L ≠ 0` fails and the v3 rule's
stage-`0` clause (`StagesGeom3`) is false at that sample. The tip's points before `t_R` are head points, so the start
piece lifts to the single point `γ 0 = 0`: the relative stage `0` is a zero-lifetime piece, as at a zero root.

* `startPiece_before`: the points of the piece before its first visit of `R` are reached by `β₀` before `t_L`
  (`startPiece_order`'s first half, which needs only `t_R ≤ L₀`);
* **`liftRel_corner`**: in the corner case, the lift relation with any regular zero-lifetime relative piece from the
  root holds.
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

/-- **The points of the piece before its first visit of `R` are reached by `β₀` before `t_L`.** -/
theorem startPiece_before (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0}
    (hRold : β₀ tL ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {sh : ℝ≥0}
    (hshmin : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 →
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = β₀ tL → sh ≤ t)
    (hshle : (sh : ℝ≥0∞) ≤ (D n).2) :
    ∀ t : ℝ≥0, t < sh → ∀ t' : ℝ≥0,
      β₀ t' = pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t → t' < tL := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  set φ := pcPt s (D n) with hφ
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) _ D hl
  have hpc := continuousOn_pcPt_launch hP hl
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have htipR : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → φ t ∈ range β₀ := fun t ht => by
    rw [hβr]
    exact tipSet_subset_physSet_launch hl (by rw [htip]; exact ⟨t, ht, rfl⟩)
  have hold : statePhysicalSet 0 s ⊆ range β₀ := by
    rw [hβr]; exact statePhysicalSet_subset_physSet hlen.le
  have holdc := (prefix_facts hW.1 hW.2 n).1
  have h0old : β₀ 0 ∈ statePhysicalSet 0 s := by rw [hβ0]; exact Or.inl (Or.inl rfl)
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hseed : φ 0 ∈ statePhysicalSet 0 s := by
    rw [hφ, pcPt_zero_launch hP hW hl hpos]
    exact (prefix_facts hW.1 hW.2 n).2 (stStatus_ne_done_of_launches _ D hl')
  obtain ⟨ts, hts⟩ := htipR 0 (by rw [ENNReal.coe_zero]; exact zero_le)
  have htsL : ts < tL := lt_of_mem_old hβ hold holdc h0old hRold (by rw [hts]; exact hseed)
  have harc : ∀ a t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → φ '' Icc a t ⊆ range β₀ := fun a t ht => by
    rintro _ ⟨x, hx, rfl⟩
    exact htipR x (le_trans (ENNReal.coe_le_coe.2 hx.2) ht)
  have hconn : ∀ a t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → IsPreconnected (φ '' Icc a t) := fun a t ht =>
    isPreconnected_Icc.image _ (hpc.mono fun x hx => le_trans (ENNReal.coe_le_coe.2 hx.2) ht)
  intro t ht t' ht'
  have htle : (t : ℝ≥0∞) ≤ (D n).2 := le_trans (ENNReal.coe_le_coe.2 ht.le) hshle
  by_contra hge
  push Not at hge
  have hsub := Icc_subset_preimage hβ (harc 0 t htle) (hconn 0 t htle)
    (show β₀ ts ∈ φ '' Icc 0 t from by rw [hts]; exact ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩)
    (show β₀ t' ∈ φ '' Icc 0 t from by rw [ht']; exact ⟨t, ⟨zero_le, le_rfl⟩, rfl⟩)
  obtain ⟨x, hx, hxR⟩ := hsub ⟨htsL.le, hge⟩
  have := hshmin x (le_trans (ENNReal.coe_le_coe.2 hx.2) htle) hxR
  exact absurd (lt_of_le_of_lt (le_trans this hx.2) ht) (lt_irrefl _)

/-- **The corner case lifts to the root**: when the start piece first visits `R` at its end (`L₀ − t_R = 0`), its lift
image is `{γ 0} = {0}`, the tip of any regular zero-lifetime relative piece from the root. -/
theorem liftRel_corner (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) {β₀ γ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0} {R : ℝ}
    (hβL : β₀ tL = R)
    (hRmem : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hL : (D n).2 - visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R = 0)
    (hγ0 : γ 0 = 0) {e₂ : Drv} (hreg : IsRegularDriver e₂) (he₂ : e₂.2 = 0) :
    LiftRel β₀ tL γ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
      (newPc (ExplState.init 0) e₂) := by
  set s₁ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs₁
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  -- `R` is not in the old part (else the shift is `0` and the shifted lifetime is `L₀ ≠ 0`)
  have hRo : (R : ℂ) ∉ statePhysicalSet 0 s₁ := fun hRo => by
    rw [visitTime_eq_zero_of_old hP hW hl hpos hRo, ENNReal.coe_zero, tsub_zero] at hL
    exact hpos hL
  have hsplit : statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) =
      statePhysicalSet 0 s₁ ∪ (newPc s₁ (D n)).1.tipSet (newPc s₁ (D n)).2.1 (newPc s₁ (D n)).2.2 := by
    rw [GW1W.launch_walk hl]
    exact GW1WalkChain.statePhysicalSet_launch 0 _ n (D n) θ ⊤
  rw [hsplit] at hRmem
  have hRt := hRmem.resolve_left hRo
  rw [htip] at hRt
  obtain ⟨t₀, ht₀, ht₀R⟩ := hRt
  obtain ⟨hshK, hsh, hmin⟩ := visitTime_spec hP hl ⟨t₀, ht₀, ht₀R⟩
  set sh := visitTime s₁ (D n) R with hsh_def
  have hLsh : (D n).2 ≤ sh := tsub_eq_zero_iff_le.1 hL
  have hbefore := startPiece_before hP hW hl hpos hβ hβ0 hβr (tL := tL) (by rw [hβL]; exact hRo) (sh := sh)
    (fun t ht h => hmin t ht (h.trans hβL)) hshK
  unfold LiftRel liftImage
  rw [tipSet_newPc_init_zero hreg he₂, htip]
  ext z
  constructor
  · intro hz
    rw [mem_singleton_iff.1 hz]
    refine ⟨0, show β₀ (tL + 0) ∈ pcPt s₁ (D n) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} from ?_, hγ0⟩
    rw [add_zero, hβL]
    exact ⟨sh, hshK, hsh⟩
  · rintro ⟨s, ⟨t, ht, heq⟩, rfl⟩
    have hts : t = sh := by
      refine le_antisymm (ENNReal.coe_le_coe.1 (ht.trans hLsh)) ?_
      by_contra hlt
      push Not at hlt
      exact absurd (hbefore t hlt (tL + s) heq.symm) (not_lt.2 le_self_add)
    have hs' : β₀ (tL + s) = β₀ tL := by rw [← heq, hts, hsh, hβL]
    have hs0 : tL + s = tL + 0 := by rw [add_zero]; exact hβ.2.1 hs'
    rw [add_left_cancel hs0, hγ0]
    exact mem_singleton _

end InteractingSLE.Theorem14.SB.Lk
