/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedOrigin
import InteractingSLE.Spec.Supplement.SBLuChart
import InteractingSLE.Spec.Supplement.GW1WalkExitInverse
import InteractingSLE.Spec.Supplement.GW1DetPhysical

/-!
# S3: the physical boundary transport used by word provenance

The inverse Loewner boundary theorem identifies the physical readouts at
alive real coordinates. Thus the boundary transport in the provenance step
follows from the actual chart boundary limits and the single-piece inverse
boundary limits. Recentering transports the physical coordinate as well as
the word; original real data cannot supply an interior landing at stage zero.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H Hbar fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart GW1W GW1Conn

/-- The stopped word retains the tip coordinate among its finite marks. -/
theorem zero_mem_jumps_stopWord (κ : ℝ) (c : BoundaryWord) (θ : ℝ) (r : RecData) :
    (0 : ℝ) ∈ (stopWord κ (c, θ, r)).jumps := by
  refine BoundaryWord.mem_jumps.2 ⟨flowLineNL c.fn c.jumps 0, ?_, ?_⟩
  · change flowLineNL c.fn c.jumps 0 < flowLineNL c.fn c.jumps 0 + 1 + flowLineNR c.fn c.jumps 0
    omega
  · change cumMax (rawPos _ _ _) (flowLineNL c.fn c.jumps 0) = 0
    rw [cumMax_rawPos (isMarkOrder_stopWord c r) (by omega)]
    simp only [rawPos, lt_self_iff_false, ↓reduceIte]

/-- The vertical-limit readout agrees with the continuous boundary extension. -/
theorem bdVal_eq_extendFrom {c : Chart} (hc : HasBdryLimits c.2.1) {p : ℂ} (hp : p ∈ Hbar) :
    LuM.bdVal c p = extendFrom H c.2.1 p :=
  LuM.bdVal_eq_of_tendsto hp (hc.tendsto hp)

/-- The physical readout on the real coordinate line is continuous. -/
theorem continuous_bdVal_real {c : Chart} (hc : HasBdryLimits c.2.1) :
    Continuous (fun x : ℝ => LuM.bdVal c (x : ℂ)) := by
  have he : (fun x : ℝ => LuM.bdVal c (x : ℂ)) =
      fun x : ℝ => extendFrom H c.2.1 (x : ℂ) :=
    funext fun x => bdVal_eq_extendFrom hc (by simp [QuantumZipper.Hbar])
  rw [he]
  exact hc.continuousOn.comp_continuous Complex.continuous_ofReal
    (fun x => by simp [QuantumZipper.Hbar])

/-- The exact physical boundary transport through one Loewner step.
It follows from the existing inverse-map boundary limit at an alive point. -/
theorem bdVal_loewner_fwdMap {c : Chart} (hc : HasBdryLimits c.2.1)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hB : HasBdryLimits (fwdMapInv W T)) {x : ℝ}
    (hAlive : ∃ u, IsForwardSol W (x : ℂ) T u) :
    LuM.bdVal c (x : ℂ) =
      LuM.bdVal (c.loewner W T) ((fwdMap W T (x : ℂ)).re : ℂ) := by
  obtain ⟨u, hu⟩ := hAlive
  have hxH : (x : ℂ) ∈ Hbar := by simp [QuantumZipper.Hbar]
  have he := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB hW hW0 hT hxH hu
  have hmap : fwdMap W T (x : ℂ) = u T :=
    InteractingSLE.fwdMap_eq_of_isForwardSol hW hu ⟨hT, le_rfl⟩
  have hr : fwdMap W T (x : ℂ) = ((fwdMap W T (x : ℂ)).re : ℂ) :=
    Complex.ext rfl (by simp only [Complex.ofReal_im, im_fwdMap_ofReal W hT x])
  have huH : u T ∈ Hbar := by rw [← hmap, hr]; simp [QuantumZipper.Hbar]
  have hlim := hB.tendsto huH
  rw [he, ← hmap, hr] at hlim
  have ht := CounterflowRange.tendsto_loewner_inv (c := c)
    (f := extendFrom H c.2.1) hW hW0 hT hlim (hc.tendsto hxH)
  exact (bdVal_eq_extendFrom hc hxH).trans
    (LuM.bdVal_eq_of_tendsto (by simp only [Complex.ofReal_im, le_refl]) ht).symm

/-- Recentering moves the physical readout by exactly the same real shift
as `BoundaryWord.shiftW`. -/
theorem bdVal_recenter_real {c : Chart} (hc : HasBdryLimits c.2.1) (a x : ℝ) :
    LuM.bdVal (c.recenter a) (x : ℂ) = LuM.bdVal c ((x + a : ℝ) : ℂ) := by
  have ht := GW1Det.tendsto_recenter_inv
    (fun p hp => hc.tendsto hp) a (x : ℂ) (by simp [QuantumZipper.Hbar])
  have he := LuM.bdVal_eq_of_tendsto (by simp only [Complex.ofReal_im, le_refl]) ht
  rw [he, bdVal_eq_extendFrom hc (by simp [QuantumZipper.Hbar]), Complex.ofReal_add]

/-- An interior stopped-word value has the inherited old-side predicate or
a new side height. Its zero coordinate is automatically excluded by marks. -/
theorem stopWord_interior_values_bdVal {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord}
    {chart : Chart} (hc : HasBdryLimits chart.2.1) {θ : ℝ} {r : RecData}
    (hB : HasBdryLimits (fwdMapInv (rdrv r) (rtime r))) {P : ℝ → Prop}
    (hOld : ∀ x ∉ c.jumps, LuM.bdVal chart (x : ℂ) ∈ H → P (c.fn x))
    (hL : P (-sleLambda κ - θ * QuantumZipper.chiC κ))
    (hR : P (sleLambda κ - θ * QuantumZipper.chiC κ))
    {y : ℝ} (hy : y ∉ (stopWord κ (c, θ, r)).jumps)
    (hyH : LuM.bdVal (chart.loewner (rdrv r) (rtime r)) (y : ℂ) ∈ H) :
    P ((stopWord κ (c, θ, r)).fn y) := by
  have hy0 : y ≠ 0 := fun he => hy (he ▸ zero_mem_jumps_stopWord κ c θ r)
  exact stopWord_interior_values (gNew := fun t : ℝ =>
    LuM.bdVal (chart.loewner (rdrv r) (rtime r)) (t : ℂ)) hκ (continuous_bdVal_real hc) hOld
    (fun x _ hxA => bdVal_loewner_fwdMap hc (continuous_rdrv r) (rdrv_zero r)
      (rtime_nonneg r) hB hxA) hL hR hy0 hy hyH

end InteractingSLE.Theorem14.SB.S3
