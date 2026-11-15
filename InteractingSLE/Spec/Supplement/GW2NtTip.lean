/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdoThr
import InteractingSLE.Spec.Supplement.GW2GmJ32Shift

/-!
# GW2's `noThreshold`: an interior tip has no continuation threshold

Packet PROVE-GW2-NOTHR (round 2, decision D38). A continuation threshold puts the tip of the chain on a bad REAL
point (`GW2Sdo.not_threshold_of_notMem_badSet`, from `GW2Sdn.threshold_real_tip`). So when the tip is an interior
point, there is no threshold, whatever the force word. For a chain mapped out at time `a` the tip is interior as soon
as the original trace at `a + u` is an interior point of `ℍ \ K_a` ([Yua22] Corollary 1.3 with the fibre identity,
through GEOM2's `Gm.notMem_diff_of_shiftTip_notMem_H`). This is the after-cap step of `noThreshold`: past the
candidate's own cap the explored driver is frozen, and the explored trace is the slit into the interior.

* **`not_threshold_of_tip_mem_H`**;
* **`not_threshold_shift_of_mem`**: no threshold of any force word along the shifted driver `W(a + ·) − W(a)` at a
  time `u > 0` whose original trace point `η(a + u)` lies in `ℍ \ K_a`.

Deterministic; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H fwdHull)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW2Nt

open MartChar.RealFlow

/-- **An interior tip has no continuation threshold** (any force word with marks on their own sides). -/
theorem not_threshold_of_tip_mem_H {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {t : ℝ} (ht : 0 < t)
    {η : ℝ → ℂ} (hη : IsLoewnerTraceLT U t η) (hc : ContinuousOn η (Icc 0 t)) (hH : η t ∈ H)
    {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) :
    ¬ ForceWord.ThresholdCondition ρL ρR (U t) (fun i => -rightImg (fun v => -U v) (-xL i) t)
      (fun j => rightImg U (xR j) t) :=
  GW2Sdo.not_threshold_of_notMem_badSet hU hU0 ht hη hc hxL hxR fun hm =>
    (ne_of_gt hH) (SB.Vr.badSet_subset_real hm)

/-- **A shifted tip over an interior point has no continuation threshold.** For a global Loewner trace `η` of `W`,
if `η(a + u)` (with `u > 0`) is an interior point of `ℍ \ K_a`, the shifted driver `W(a + ·) − W(a)` has no
continuation threshold at `u`, for any force word. -/
theorem not_threshold_shift_of_mem {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) (hmem : η (a + u) ∈ H \ fwdHull W a)
    {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) :
    ¬ ForceWord.ThresholdCondition ρL ρR (shiftDrive W a u)
      (fun i => -rightImg (fun v => -shiftDrive W a v) (-xL i) u) (fun j => rightImg (shiftDrive W a) (xR j) u) := by
  obtain ⟨hψ, -⟩ := hη.isLoewnerTrace_shift_and_extendFrom hW hW0 ha
  have hHtip : loewnerTip (shiftDrive W a) u ∈ H := by
    by_contra h
    exact GW2TipSystem.Gm.notMem_diff_of_shiftTip_notMem_H hη hW hW0 ha hu.le h hmem
  have hLT : IsLoewnerTraceLT (shiftDrive W a) u (loewnerTip (shiftDrive W a)) :=
    ⟨hψ.1, hψ.2.1.mono Ico_subset_Ici_self, fun t ht _ => hψ.2.2 t ht⟩
  exact not_threshold_of_tip_mem_H (QuantumZipper.RS.continuous_shiftDrive hW a)
    (QuantumZipper.RS.shiftDrive_zero W a) hu hLT (hψ.2.1.mono Icc_subset_Ici_self) hHtip hxL hxR

end InteractingSLE.Theorem14.GW2Nt
