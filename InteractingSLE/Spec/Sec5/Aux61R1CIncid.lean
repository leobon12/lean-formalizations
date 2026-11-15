/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R1CChart

/-!
# Clearance and incidence of a record from the source's restart conditions

Packet PROVE-AUX61-R1CHART. The good records (`goodSet`) add to regularity two source conditions; here they are
derived from the forms in which the source states them (Astra follow-up 4, Part (1), §1.1: a restart at a rational own
time `r` with `dist(η(r), K) > 0`, the current access in the original right-target component):

* `clearRec_of_infDist_pos`: a tip in `ℍ` at positive distance from the counterflow hull has clearance from R1's
  obstacle `(ℍ ∖ K)ᶜ`;
* `incRec_of_frequent`: on a regular record with clearance, if the current access (the own inverse map at `q` near
  `0`) frequently lies in a component of the retained domain with `1` in its closure, then it eventually lies in the
  selected target component along the access points (R1's current collar
  `Aux61Restart.history_current_collar_of_frequent` and the uniqueness of the target component).

`mem_goodSet_of_frequent` assembles them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv)

namespace InteractingSLE.Sec5.Aux61R1C

open LawUnique Restart.FlowStopIdentG Aux61Restart Aux61Marks
open Aux61SlitW (rationalTime)

variable {nL nR : ℕ} {s : ℝ≥0} {q : ℚ}

/-- **Clearance from the distance to the counterflow hull**: a tip in `ℍ` at positive distance from the counterflow
hull is at positive distance from R1's obstacle `(ℍ ∖ K)ᶜ`. -/
theorem clearRec_of_infDist_pos {y : Rec nL nR} (hH : recTrace y.2 q ∈ H)
    (hK : 0 < infDist (recTrace y.2 q) (recHull s y)) : ClearRec s q y := by
  set x := recTrace y.2 q with hx
  have hδ : 0 < min x.im (infDist x (recHull s y)) := lt_min hH hK
  refine lt_of_lt_of_le hδ ((le_infDist (retObs_nonempty s y)).2 fun z hz => ?_)
  by_cases hzH : z ∈ H
  · have hzK : z ∈ recHull s y := by
      by_contra h
      exact hz ⟨hzH, h⟩
    exact (min_le_right _ _).trans (infDist_le_dist_of_mem hzK)
  · have hz0 : z.im ≤ 0 := not_lt.1 hzH
    refine (min_le_left _ _).trans ?_
    calc x.im ≤ x.im - z.im := by linarith
      _ ≤ |x.im - z.im| := le_abs_self _
      _ = |(x - z).im| := by rw [Complex.sub_im]
      _ ≤ ‖x - z‖ := Complex.abs_im_le_norm _
      _ = dist x z := (dist_eq_norm _ _).symm

/-- **Incidence from the source's frequent current access**: on a regular record with clearance, if the current access
frequently lies in a component of the retained domain with `1` in its closure, the record has incidence. -/
theorem incRec_of_frequent (hs : 0 < s) {y : Rec nL nR} (hy : RegRec s q y) (hcl : ClearRec s q y) {b : ℂ}
    (hb : (1 : ℂ) ∈ closure (restartComponent (recHull s y) (recη q y) q b))
    (hf : ∃ᶠ w in 𝓝[H] 0, fwdMapInv (Ito.rpath fun t => recU q t y) (rationalTime q) w ∈
      restartComponent (recHull s y) (recη q y) q b) :
    IncRec s q y := by
  obtain ⟨hq, hUc, hU0, hη, -, hH, hco, h0, hP⟩ := hy.facts
  have hqq : (0 : ℚ) ≤ q := by exact_mod_cast hq.le
  have hrq : ((rationalTime q : ℝ≥0) : ℝ) = q := coe_rationalTime hqq
  have htip : recη q y q ∈ H := hH ⟨hq, le_rfl⟩
  have hclear : 0 < infDist (recη q y q) (recHull s y) := by
    rw [recη_of_le hqq y le_rfl]
    exact infDist_recHull_pos hs hcl
  obtain ⟨δ, hδ, hmaps⟩ := history_current_collar_of_frequent (Ω := Unit) (s := s) (r := rationalTime q) (q := q)
    hrq (Y := fun _ => y.1) (η := fun _ => recη q y) (U := fun t _ => recU q t y) (fun _ => hUc) (fun _ => hU0)
    (fun _ => hη) hq.le (fun _ => htip) (fun _ => hclear) (b := fun _ => b) (fun _ => hf) ()
  have hyr : y ∈ regSet s q := hy
  obtain ⟨-, -, hcl1⟩ := selN_spec ⟨y, hyr⟩
  have hcl2 := hcl1 y
  rw [tgtComp_of_mem hyr] at hcl2
  have heq : restartComponent (recHull s y) (recη q y) q b = tgtComp s q y := by
    rw [tgtComp_of_mem hyr]
    exact connectedComponentIn_eq_of_original_target_collars
      (exists_original_right_target_component_collar hco h0 hH hP hb)
      (exists_original_right_target_component_collar hco h0 hH hP hcl2)
  have hev : ∀ᶠ n in atTop, accPt n ∈ ball (0 : ℂ) δ ∩ H :=
    tendsto_accPt.eventually_mem (by rw [inter_comm]; exact inter_mem_nhdsWithin H (ball_mem_nhds 0 hδ))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine ⟨n₀, fun n hn => ?_⟩
  have h := hmaps (hn₀ n hn)
  simp only [stU]
  rw [retr_of_mem hyr, ← heq]
  exact h

/-- **A regular record is good** when its tip (in `ℍ`) is at positive distance from the counterflow hull and the
current access frequently lies in a component of the retained domain with `1` in its closure. -/
theorem mem_goodSet_of_frequent (hs : 0 < s) {y : Rec nL nR} (hy : RegRec s q y)
    (hK : 0 < infDist (recTrace y.2 q) (recHull s y)) {b : ℂ}
    (hb : (1 : ℂ) ∈ closure (restartComponent (recHull s y) (recη q y) q b))
    (hf : ∃ᶠ w in 𝓝[H] 0, fwdMapInv (Ito.rpath fun t => recU q t y) (rationalTime q) w ∈
      restartComponent (recHull s y) (recη q y) q b) :
    y ∈ goodSet s q := by
  obtain ⟨hq, -, -, -, -, hH, -, -, -⟩ := hy.facts
  have hqq : (0 : ℚ) ≤ q := by exact_mod_cast hq.le
  have htip : recTrace y.2 q ∈ H := by
    rw [← recη_of_le hqq y le_rfl]
    exact hH ⟨hq, le_rfl⟩
  have hcl := clearRec_of_infDist_pos htip hK
  exact ⟨hy, hcl, incRec_of_frequent hs hy hcl hb hf⟩

end InteractingSLE.Sec5.Aux61R1C
