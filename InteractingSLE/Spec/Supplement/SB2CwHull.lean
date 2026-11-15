/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeCanon
import InteractingSLE.Spec.Supplement.SB2NcClock
import InteractingSLE.Spec.Supplement.SB2FinHull
import InteractingSLE.Spec.Supplement.SB2QxPhys

/-!
# The canonical relative hull read back in the physical picture (deterministic)

Packet PROVE-SB2-CANON, round 4 ((P4): the chain clause of the canonical driver). For the retained union `Y` (compact,
`fill Y` a hull), the chart `Φ = Mo.hullChart (fill Y) x₀`, B's physical piece `p` of lifetime `L` and its canonical
curve `ρ = Dv.canonCurve Y x₀ p L` (driven), NOJUMP's `Ne.H_diff_fillH_union_canon` gives
`ℍ ∖ fill (Y ∪ p[0, cTime U]) = Φ⁻¹(ℍ ∖ fill ρ[0, U])`. Read pointwise:

* **`mem_fillH_canon_iff`**: for `x ∈ ℍ ∖ fill Y`, `Φ x ∈ fill ρ[0, U] ↔ x ∈ fill (Y ∪ p[0, cTime U])`;
* **`mem_closure_of_frontier_canon`**: if `Φ x` is on the frontier of `fill ρ[0, U]`, then `x` is in the joint fill
  and in the closure of its complement in `ℍ`, hence (**`mem_piece_of_frontier_canon`**) on `p[0, cTime U]`.

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Cz

open Sec7.PocketTraversal Sec7.Lemma71C Dv

variable {Y : Set ℂ} {x₀ : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞}

/-- The chart's forward map undoes its inverse on `ℍ`. -/
theorem hullChart_fwd_inv (hA : IsHPHull (fillH Y)) (x₀ : ℝ) {w : ℂ} (hw : w ∈ H) :
    (Mo.hullChart (fillH Y) x₀).1 ((Mo.hullChart (fillH Y) x₀).2.1 w) = w :=
  (Mo.isDomainChart_hullChart hA x₀).1.2.2 w hw

/-- **The canonical relative hull read back**: for `x` off `fill Y` in `ℍ`, the chart image of `x` is in the filled
canonical prefix iff `x` is in the joint fill of `Y` and the physical piece. -/
theorem mem_fillH_canon_iff (hYc : IsCompact Y) (hA : IsHPHull (fillH Y)) (hL : L ≠ 0)
    (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L}) (hdr : IsDrivenCurve (canonCurve Y x₀ p L)) {U : ℝ} (hU : 0 ≤ U)
    {x : ℂ} (hx : x ∈ H \ fillH Y) :
    (Mo.hullChart (fillH Y) x₀).1 x ∈ fillH (canonCurve Y x₀ p L '' Icc 0 U) ↔
      x ∈ fillH (Y ∪ p '' Icc 0 (Nc.cTime L U)) := by
  have hid := Ne.H_diff_fillH_union_canon hYc hA hL hpc hdr hU (x₀ := x₀)
  obtain ⟨hyH, hyx⟩ := Ne.hullChart_fwd_spec hA x₀ hx
  constructor
  · intro hy
    by_contra hxJ
    have hxm : x ∈ H \ fillH (Y ∪ p '' Icc 0 (Nc.cTime L U)) := ⟨hx.1, hxJ⟩
    rw [hid] at hxm
    obtain ⟨y', hy', hy'x⟩ := hxm
    have : (Mo.hullChart (fillH Y) x₀).1 x = y' := by rw [← hy'x, hullChart_fwd_inv hA x₀ hy'.1]
    rw [this] at hy
    exact hy'.2 hy
  · intro hxJ
    by_contra hy
    have hym : (Mo.hullChart (fillH Y) x₀).2.1 ((Mo.hullChart (fillH Y) x₀).1 x) ∈
        H \ fillH (Y ∪ p '' Icc 0 (Nc.cTime L U)) := by
      rw [hid]; exact ⟨_, ⟨hyH, hy⟩, rfl⟩
    rw [hyx] at hym
    exact hym.2 hxJ

/-- **A frontier point of the canonical relative hull reads back to the joint fill and the closure of its complement.**
-/
theorem mem_closure_of_frontier_canon (hYc : IsCompact Y) (hA : IsHPHull (fillH Y)) (hL : L ≠ 0)
    (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L}) (hdr : IsDrivenCurve (canonCurve Y x₀ p L)) {U : ℝ} (hU : 0 ≤ U)
    {x : ℂ} (hx : x ∈ H \ fillH Y)
    (hfr : (Mo.hullChart (fillH Y) x₀).1 x ∈ frontier (fillH (canonCurve Y x₀ p L '' Icc 0 U))) :
    x ∈ fillH (Y ∪ p '' Icc 0 (Nc.cTime L U)) ∧
      x ∈ closure (H \ fillH (Y ∪ p '' Icc 0 (Nc.cTime L U))) := by
  set Φ := Mo.hullChart (fillH Y) x₀ with hΦ
  set F := fillH (canonCurve Y x₀ p L '' Icc 0 U) with hF
  have hid := Ne.H_diff_fillH_union_canon hYc hA hL hpc hdr hU (x₀ := x₀)
  obtain ⟨hyH, hyx⟩ := Ne.hullChart_fwd_spec hA x₀ hx
  have hFc : IsCompact (canonCurve Y x₀ p L '' Icc 0 U) :=
    isCompact_Icc.image_of_continuousOn (hdr.continuousOn.mono fun v hv => hv.1)
  have hFo : IsOpen (H \ F) := isOpen_H_diff_fillH hFc.isBounded
  -- the image point is in the filled prefix (relatively closed in `ℍ`)
  have hyF : Φ.1 x ∈ F := by
    by_contra hn
    have hmem : Φ.1 x ∈ H \ F := ⟨hyH, hn⟩
    have hint : Φ.1 x ∈ interior Fᶜ := interior_maximal (fun w hw => hw.2) hFo hmem
    rw [interior_compl] at hint
    exact hint (frontier_subset_closure hfr)
  refine ⟨(mem_fillH_canon_iff hYc hA hL hpc hdr hU hx).1 hyF, ?_⟩
  -- points of `ℍ ∖ F` accumulate at the image point; their inverse images accumulate at `x`
  have hacc : Φ.1 x ∈ closure (H \ F) := by
    rw [_root_.mem_closure_iff]
    intro O hO hyO
    have hfr' : Φ.1 x ∈ closure F ∧ Φ.1 x ∉ interior F := hfr
    obtain ⟨w, hwO, hwF⟩ : (O ∩ H ∩ Fᶜ).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      have hsub : O ∩ H ⊆ F := fun w hw => by
        by_contra hwF
        have : w ∈ O ∩ H ∩ Fᶜ := ⟨hw, hwF⟩
        rw [hne] at this
        exact this
      exact hfr'.2 (mem_interior.2 ⟨O ∩ H, hsub, hO.inter QuantumZipper.isOpen_H, hyO, hyH⟩)
    exact ⟨w, hwO.1, hwO.2, hwF⟩
  have hcont : ContinuousWithinAt Φ.2.1 (H \ F) (Φ.1 x) :=
    ((Ne.continuousOn_hullChart_inv hA x₀).continuousAt (QuantumZipper.isOpen_H.mem_nhds hyH)).continuousWithinAt
  have himg : Φ.2.1 '' (H \ F) ⊆ H \ fillH (Y ∪ p '' Icc 0 (Nc.cTime L U)) := by
    rw [hid]
  have hcl := hcont.mem_closure_image hacc
  rw [hyx] at hcl
  exact closure_mono himg hcl

/-- **A frontier point of the canonical relative hull reads back to a point of the physical piece.** -/
theorem mem_piece_of_frontier_canon (hYc : IsCompact Y) (hA : IsHPHull (fillH Y)) (hL : L ≠ 0)
    (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L}) (hdr : IsDrivenCurve (canonCurve Y x₀ p L)) {U : ℝ} (hU : 0 ≤ U)
    {x : ℂ} (hx : x ∈ H \ fillH Y)
    (hfr : (Mo.hullChart (fillH Y) x₀).1 x ∈ frontier (fillH (canonCurve Y x₀ p L '' Icc 0 U))) :
    x ∈ p '' Icc 0 (Nc.cTime L U) := by
  obtain ⟨hJ, hcl⟩ := mem_closure_of_frontier_canon hYc hA hL hpc hdr hU hx hfr
  have hpI : IsCompact (p '' Icc 0 (Nc.cTime L U)) :=
    isCompact_Icc.image_of_continuousOn (hpc.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans
      (Nc.cTime_le hL hU))
  have hSc : IsClosed (Y ∪ p '' Icc 0 (Nc.cTime L U)) := hYc.isClosed.union hpI.isClosed
  have hfrJ : x ∈ frontier (fillH (Y ∪ p '' Icc 0 (Nc.cTime L U))) := by
    refine ⟨subset_closure hJ, fun hint => ?_⟩
    obtain ⟨O, hOs, hOo, hxO⟩ := mem_interior.1 hint
    obtain ⟨w, hwO, hw⟩ := _root_.mem_closure_iff.1 hcl O hOo hxO
    exact hw.2 (hOs hwO)
  have hmem := FinRel.frontier_fillH_inter_H_subset _ ⟨hfrJ, hx.1⟩
  rw [hSc.closure_eq] at hmem
  rcases hmem with hY | hp
  · exact absurd (Qx.self_inter_H_subset_fillH Y ⟨hY, hx.1⟩) hx.2
  · exact hp

end InteractingSLE.Theorem14.SB.Cz
