/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdoThr
import InteractingSLE.Spec.Supplement.GW2SdyDil
import InteractingSLE.Spec.Supplement.GW2SfWord
import InteractingSLE.Spec.Supplement.GB6LifeBase

/-!
# Review defect N4, item 2: from the launch chart to the stage chart (deterministic)

Packet PROVE-GW2-SDE (round 14; D20). `OpenLinesS.noThreshold` reads the stage word `upW (θχ) c` (GEOM2's word map:
the base word `c` raised by the candidate's angle) at angle `0`, along the stage driver `D`. The candidate's own
statement (`GW2Sdo.ae_candidate_no_threshold`) reads its launch word at angle `θ` along its launch driver `W_L`. When
the launch chart is the stage chart dilated by `λ > 0` (STAGEMEAN's step 3, `ca = λ · cs`), the launch word is the
dilated base word `dilW λ c` and `W_L = scD λ D` (`s ↦ λ D(s/λ²)`) before the relevant time. Then:

* `thresholdCondition_cast`: the threshold condition is invariant under re-indexing by `Fin.cast`;
* `dilW_inv_dilW`, **`isFlowType_dilW_of`**: the flow-line data of the dilated word are the dilated data (the converse
  of `GW2Sdy.isFlowType_of_dilW`);
* **`not_threshold_stage_of_launch`**: no threshold of the launch word at angle `θ` along `W_L` at time `λ² u` gives
  no threshold of the stage word `upW (θχ) c` at angle `0` along `D` at time `u`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Sdo

open Restart MartChar.RealFlow Sec5.CrossCond.StagedRepLater GW2Sdy

/-- **The threshold condition is invariant under re-indexing by `Fin.cast`.** -/
theorem thresholdCondition_cast {n n' m m' : ℕ} (eL : n = n') (eR : m = m') (ρL vL : Fin n' → ℝ)
    (ρR vR : Fin m' → ℝ) (w : ℝ) :
    ForceWord.ThresholdCondition (fun i => ρL (Fin.cast eL i)) (fun j => ρR (Fin.cast eR j)) w
        (fun i => vL (Fin.cast eL i)) (fun j => vR (Fin.cast eR j)) ↔
      ForceWord.ThresholdCondition ρL ρR w vL vR := by
  subst eL
  subst eR
  rfl

theorem dilW_inv_dilW {a : ℝ} (ha : a ≠ 0) (c : BoundaryWord) : dilW a⁻¹ (dilW a c) = c := by
  refine Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl)
  simp only [dilW]
  rw [inv_mul_cancel_left₀ ha]

/-- **The flow-line data of the dilated word are the dilated data.** -/
theorem isFlowType_dilW_of {κ θ a : ℝ} (ha : 0 < a) {c : BoundaryWord} {nL nR : ℕ} {xL ρL : Fin nL → ℝ}
    {xR ρR : Fin nR → ℝ} (h : FCDet.IsFlowType κ θ c xL xR ρL ρR) :
    FCDet.IsFlowType κ θ (dilW a c) (fun i => a * xL i) (fun j => a * xR j) ρL ρR := by
  rw [← dilW_inv_dilW ha.ne' c] at h
  have h' := isFlowType_of_dilW (inv_pos.2 ha) h
  simpa only [inv_inv] using h'

/-- **No threshold in the launch chart gives no threshold in the stage chart** (deterministic). If the launch driver
`WL` is `scD λ D` on `[0, λ² u]` and the launch word is `dilW λ c`, then no continuation threshold of the launch word at
angle `θ` along `WL` at time `λ² u` gives none of the stage word `upW (θχ) c` at angle `0` along `D` at time `u`
(the form of `OpenLinesS.noThreshold`). -/
theorem not_threshold_stage_of_launch {κ θ lam : ℝ} (hlam : 0 < lam) (c : BoundaryWord) {D WL : ℝ → ℝ}
    (hD : Continuous D) {u : ℝ} (hu : 0 ≤ u) (hW : ∀ v ∈ Icc (0 : ℝ) (lam ^ 2 * u), WL v = scD lam D v)
    (hL : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ (dilW lam c).fn (dilW lam c).jumps 0 θ)
      (flowLineRhoR κ (dilW lam c).fn (dilW lam c).jumps 0 θ) (WL (lam ^ 2 * u))
      (fun i => -rightImg (fun v => -WL v) (-flowLineXL (dilW lam c).fn (dilW lam c).jumps 0 i) (lam ^ 2 * u))
      (fun j => rightImg WL (flowLineXR (dilW lam c).fn (dilW lam c).jumps 0 j) (lam ^ 2 * u))) :
    ¬ ForceWord.ThresholdCondition
      (flowLineRhoL κ (GW2Rd.upW (θ * chiC κ) c).fn (GW2Rd.upW (θ * chiC κ) c).jumps 0 0)
      (flowLineRhoR κ (GW2Rd.upW (θ * chiC κ) c).fn (GW2Rd.upW (θ * chiC κ) c).jumps 0 0) (D u)
      (fun i => -rightImg (fun v => -D v) (-flowLineXL (GW2Rd.upW (θ * chiC κ) c).fn
        (GW2Rd.upW (θ * chiC κ) c).jumps 0 i) u)
      (fun j => rightImg D (flowLineXR (GW2Rd.upW (θ * chiC κ) c).fn (GW2Rd.upW (θ * chiC κ) c).jumps 0 j) u) := by
  set cu := GW2Rd.upW (θ * chiC κ) c with hcu
  set xLu := flowLineXL cu.fn cu.jumps 0
  set xRu := flowLineXR cu.fn cu.jumps 0
  set ρLu := flowLineRhoL κ cu.fn cu.jumps 0 0
  set ρRu := flowLineRhoR κ cu.fn cu.jumps 0 0
  have htriv : FCDet.IsFlowType κ 0 cu xLu xRu ρLu ρRu := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := isFlowType_dilW_of hlam (GW2Sf.isFlowType_of_upW htriv)
  have hxL' : ∀ i, flowLineXL (dilW lam c).fn (dilW lam c).jumps 0 i = lam * xLu (Fin.cast eL i) :=
    fun i => (congrFun hxL i).symm
  have hxR' : ∀ j, flowLineXR (dilW lam c).fn (dilW lam c).jumps 0 j = lam * xRu (Fin.cast eR j) :=
    fun j => (congrFun hxR j).symm
  rw [← hρL, ← hρR] at hL
  simp only [hxL', hxR'] at hL
  have hL' := (thresholdCondition_cast eL eR ρLu (fun i => -rightImg (fun v => -WL v) (-(lam * xLu i)) (lam ^ 2 * u))
    ρRu (fun j => rightImg WL (lam * xRu j) (lam ^ 2 * u)) (WL (lam ^ 2 * u))).not.1 hL
  have hsc := continuous_scD hD lam
  have ht : 0 ≤ lam ^ 2 * u := mul_nonneg (sq_nonneg _) hu
  have eW : WL (lam ^ 2 * u) = scD lam D (lam ^ 2 * u) := hW _ ⟨ht, le_rfl⟩
  have eR' : ∀ x, rightImg WL x (lam ^ 2 * u) = rightImg (scD lam D) x (lam ^ 2 * u) := fun x =>
    Supp8.GB6.rightImg_congr hsc ht hW
  have eL' : ∀ x, rightImg (fun v => -WL v) x (lam ^ 2 * u) = rightImg (fun v => -scD lam D v) x (lam ^ 2 * u) :=
    fun x => Supp8.GB6.rightImg_congr hsc.neg ht fun r hr => by rw [hW r hr]; rfl
  simp only [eW, eR', eL'] at hL'
  exact (thresholdCondition_scD_iff hD hlam hu ρLu ρRu xLu xRu).not.1 hL'

end InteractingSLE.Theorem14.GW2Sdo
