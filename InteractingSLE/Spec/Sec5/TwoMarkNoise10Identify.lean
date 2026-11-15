/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkNoise10Clock

/-!
# Identifying the centered observable along a local retargeted path

The existing `bv0_eq_newB` argument uses only a local path, retargeting data,
initial Brownian value and distinct marks. It does not need maximality or `1 ≤ j`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Noise10
open Zhan.Retarget

/-- Local retargeting identifies the existing centered observable with canonical noise. -/
theorem bv0_eq_newB_of_local {Ω : Type*} {nL j m : ℕ} {κ : ℝ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin (j + 1 + m) → ℝ}
    {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {G : Set Ω} {ω : Ω} {T : ℝ≥0∞}
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (B · ω) T)
    (hd : RetargetData xL xR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) T)
    (hD : LP.IsDistinctForceWord xL xR) (hzeroB : B 0 ω = 0) (hκ : 0 < κ)
    (hω : ω ∈ G) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω) T) :
    bv0 κ xL xR ρL ρR G W VL VR B u ω =
      newB κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) u := by
  have hκs : Real.sqrt κ ≠ 0 := Real.sqrt_ne_zero'.2 hκ
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) <
      newHorizon (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω) T := lt_of_le_of_lt bot_le hu
  have e0 := sqrt_mul_newB_eq hp hd hκ h0
  have eu := sqrt_mul_newB_eq hp hd hκ hu
  have hB0 : newB κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) 0 = 0 := by
    simp only [newB, newW_zero hp hd, newVL_zero hp hd hD, newVR_zero hp hD, sub_self, mul_zero,
      Finset.sum_const_zero, add_zero, zero_div]
  -- the initial value of the observable is `X̃`
  obtain ⟨S₀, _, _, _, hm0, _⟩ := newTime_spec hd.sep hd.pos h0
  have hF := hp
  have hinit : obs κ xL xR ρL ρR (LP.retargetIdx j m) (rInit xL xR (LP.retargetPos xR)) =
      obs κ xL xR ρL ρR (LP.retargetIdx j m)
        (((fun i => VL i (invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) (0 : ℝ≥0)).toNNReal
          ω), (fun i => VR i (invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω))
            (0 : ℝ≥0)).toNNReal ω),
          alpha (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)
            (invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) (0 : ℝ≥0)),
          beta (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)
            (invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) (0 : ℝ≥0)),
          clk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω))
            (invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) (0 : ℝ≥0))),
          B (invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) (0 : ℝ≥0)).toNNReal ω) := by
    simp only [NNReal.coe_zero, invClk_zero_eq, Real.toNNReal_zero, hF.vL_zero, hF.vR_zero, alpha_zero,
      beta_zero, clk_zero, hzeroB, rInit]
  rw [hB0, mul_zero, ← hinit] at e0
  -- the value at `u`
  obtain ⟨S, _, _, _, hm, _⟩ := newTime_spec hd.sep hd.pos hu
  have hval : obs κ xL xR ρL ρR (LP.retargetIdx j m)
      (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR (invClk (rateT xR W VR ω) u).toNNReal ω,
        Sec2.TwoSeed.brownG G B (invClk (rateT xR W VR ω) u).toNNReal ω) =
      Real.sqrt κ * newB κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) u +
        obs κ xL xR ρL ρR (LP.retargetIdx j m) (rInit xL xR (LP.retargetPos xR)) := by
    rw [eu]
    simp only [rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    rw [show rateT xR W VR ω = rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω) from rfl,
      rCoordAt_toNNReal hm.1]
    linarith
  rw [bv0, hval]
  field_simp
  ring

end InteractingSLE.Sec5.TwoMark.Noise10
