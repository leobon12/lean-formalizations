/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR8Transport

/-! # GW2: the canonical extension at flowed geometric marks, at any angle -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2JDetR8

open Supp8.Q3Chain Supp8.GB6LMean Sec7.PocketTraversal MartChar.RealFlow
open Restart Restart.DomainMarkov Exist.StagedLaw

/-- The extension of an arbitrary angle word, flowed by a continuous driver,
is the canonical extension for any fixed typing of that same word. -/
theorem eqOn_bheProc_of_flowType {κ θ : ℝ} {c : BoundaryWord} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (ht : FCDet.IsFlowType κ θ c xL xR ρL ρR)
    {Ω : Type*} {R : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0) (Q : ℝ≥0) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension
      (flowedData κ (flowLineRhoL κ c.fn c.jumps 0 θ)
        (flowLineRhoR κ c.fn c.jumps 0 θ) (flowLineXL c.fn c.jumps 0)
        (flowLineXR c.fn c.jumps 0) (fun r : ℝ => R r.toNNReal ω) Q)
      (flowedJumps (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
        (fun r : ℝ => R r.toNNReal ω) Q) G) :
    EqOn G (bheProc κ ρL ρR R (geomLW R (fun _ => xL))
      (geomRW R (fun _ => xR)) ω Q) H := by
  let Rp : ℝ → ℝ := fun r => R r.toNNReal ω
  have hRpc : Continuous Rp := hRc.comp continuous_real_toNNReal
  have hRp0 : Rp 0 = 0 := by simp only [Rp, Real.toNNReal_zero, hR0]
  have hRQ : Rp Q = R Q ω := by simp only [Rp, Real.toNNReal_coe]
  have hb := isBoundedHarmonicExtension_bheProc (κ := κ) (ρL := ρL) (ρR := ρR)
    (W := R) (VL := geomLW R (fun _ => xL)) (VR := geomRW R (fun _ => xR)) ω Q
  have hfin : (forceJumpSet
      (fun i => geomLW R (fun _ => xL) i Q ω - R Q ω)
      (fun j => geomRW R (fun _ => xR) j Q ω - R Q ω)).Finite := by
    rw [← coe_initJumps]
    exact Finset.finite_toSet _
  refine eqOn_bhe_of_eqOff hfin (Finset.finite_toSet _) hb hG fun y _ _ => ?_
  change forceBoundaryData κ ρL ρR
    (fun i => -rightImg (fun r : ℝ => -R r.toNNReal ω) (-xL i) Q - R Q ω)
    (fun j => rightImg (fun r : ℝ => R r.toNNReal ω) (xR j) Q - R Q ω) y = _
  rw [RetAux79.forceBoundaryData_geom_of_isFlowType ht (R · ω) Q y]
  change forceBoundaryData κ _ _ _ _ y = forceBoundaryData κ _ _ _ _ y
  have hL : (fun i => markPosL Rp Q (flowLineXL c.fn c.jumps 0 i)) =
      fun i => -rightImg (fun r : ℝ => -R r.toNNReal ω)
        (-flowLineXL c.fn c.jumps 0 i) Q - R Q ω := by
    funext i
    rw [Sec5.CrossCond.Gen.markPosL_eq_rightImg_of_nonpos hRpc hRp0 Q.coe_nonneg
      (Theorem14.GW3Word.flowLineXL_nonpos _ _ i), hRQ]
  have hR : (fun j => markPos Rp Q (flowLineXR c.fn c.jumps 0 j)) =
      fun j => rightImg (fun r : ℝ => R r.toNNReal ω)
        (flowLineXR c.fn c.jumps 0 j) Q - R Q ω := by
    funext j
    rw [Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg hRpc hRp0 Q.coe_nonneg
      (Theorem14.GW3Word.flowLineXR_nonneg _ _ j), hRQ]
  rw [hL, hR]

end InteractingSLE.Theorem14.GW2JDetR8
