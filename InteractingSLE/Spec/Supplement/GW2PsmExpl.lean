/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmStepC
import InteractingSLE.Spec.Supplement.SB2OmWord
import InteractingSLE.Spec.Supplement.GW2SfWord
import InteractingSLE.Spec.Supplement.GW2SdsTip
import InteractingSLE.Spec.Sec5.CrossCondGenCloseMarks
import InteractingSLE.Spec.Sec7.StripSideHeightProbSide
import InteractingSLE.Spec.Restart.RetPlumbLine

/-!
# GW2's open lines: the explored identity for the flowed data of a typed raised word

Packet PROVE-GW2-STAGEMEAN, R121 round (the word side of the Claim(k) step). For a word `c`, an angle `θ` and a driver
`S` (continuous, `S 0 = 0`) run for a time `q`:

* **`eqOn_explored_flowType`**: every bounded harmonic extension of the force data of an angle-`θ` flow type of `c`
  with the marks flowed along `S` up to `q` (the `rightImg` form of `pair_root0`) is, on `ℍ`, the mean of the stop word
  `stopWord κ (c, θ, recOf q (S, ⊤))` plus `θχ` (`SB.Om.eqOn_explored_mean`);
* **`eqOn_explored_typed`**: the same for the typed data of the raised word `upW (θχ) c` at its own word type.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

namespace InteractingSLE.Theorem14.GW2Psm

open Restart Exist.StagedLaw Supp8.Q3Stop MartChar.RealFlow
open Supp8.Q3Chain (flowedData flowedJumps initJumps coe_initJumps)

/-- **The explored identity for a flow type**, with the marks flowed in the `rightImg` form. -/
theorem eqOn_explored_flowType {κ θ : ℝ} {c : BoundaryWord} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hft : FCDet.IsFlowType κ θ c xL xR ρL ρR) {S : ℝ≥0 → ℝ}
    (hS : Continuous S) (hS0 : S 0 = 0) (q : ℝ≥0) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -Ito.rpath S s) (-xL i) q - Ito.rpath S q)
        (fun j => rightImg (Ito.rpath S) (xR j) q - Ito.rpath S q))
      (forceJumpSet (fun i => -rightImg (fun s => -Ito.rpath S s) (-xL i) q - Ito.rpath S q)
        (fun j => rightImg (Ito.rpath S) (xR j) q - Ito.rpath S q)) G) :
    EqOn G (fun z => (stopWord κ (c, θ, recOf (q : ℝ≥0∞) (S, ⊤))).mean z + θ * chiC κ) H := by
  obtain ⟨hsL, hsR⟩ := RetAux79.isFlowType_signs hft
  set r := recOf (q : ℝ≥0∞) (S, ⊤) with hr
  have hrt : rtime r = (q : ℝ) := by
    rw [hr, Exist.StagedLaw.rtime_recOf_coe]
    simp only [min_top_right, ENNReal.toNNReal_coe]
  have hw : Continuous (Ito.rpath S) := hS.comp continuous_real_toNNReal
  have hw0 : Ito.rpath S 0 = 0 := by simp [Ito.rpath, hS0]
  have hrd : EqOn (Ito.rpath S) (rdrv r) (Icc 0 (q : ℝ)) := fun x hx => by
    have hx' : x.toNNReal ≤ q := Real.toNNReal_le_iff_le_coe.2 hx.2
    have h1 := GW2Sds.rdrv_recOf_top_eq hS hS0 hx'
    rw [Real.coe_toNNReal _ hx.1] at h1
    rw [h1]
    rfl
  have eL : (fun i => -rightImg (fun s => -Ito.rpath S s) (-xL i) q - Ito.rpath S q) =
      fun i => markPosL (rdrv r) (rtime r) (xL i) := by
    funext i
    rw [hrt, ← Sec7.StripSideHeightProb.markPosL_congr hrd,
      Sec5.CrossCond.Gen.markPosL_eq_rightImg_of_nonpos hw hw0 q.coe_nonneg (hsL i)]
  have eR : (fun j => rightImg (Ito.rpath S) (xR j) q - Ito.rpath S q) =
      fun j => markPos (rdrv r) (rtime r) (xR j) := by
    funext j
    rw [hrt, ← Sec7.StripSideHeightProb.markPos_congr hrd,
      Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg hw hw0 q.coe_nonneg (hsR j)]
  rw [eL, eR] at hG
  obtain ⟨hnL, hnR, hxL, hxR, hρL, hρR⟩ := hft
  subst hnL hnR
  simp only [Fin.cast_eq_self] at hxL hxR hρL hρR
  have hxL' : xL = flowLineXL c.fn c.jumps 0 := hxL
  have hxR' : xR = flowLineXR c.fn c.jumps 0 := hxR
  have hρL' : ρL = flowLineRhoL κ c.fn c.jumps 0 θ := hρL
  have hρR' : ρR = flowLineRhoR κ c.fn c.jumps 0 θ := hρR
  subst hxL' hxR' hρL' hρR'
  refine SB.Om.eqOn_explored_mean c r ?_
  have e : (flowedJumps (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) (rdrv r) (rtime r) : Set ℝ) =
      forceJumpSet (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
        (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j)) := by
    unfold flowedJumps
    rw [coe_initJumps]
  rw [e]
  exact hG

/-- **The explored identity for the typed data of a raised word.** -/
theorem eqOn_explored_typed {κ θ : ℝ} {c : BoundaryWord} {w : WordType}
    (hw : wordType κ (GW2Rd.upW (θ * chiC κ) c) = w) {S : ℝ≥0 → ℝ} (hS : Continuous S) (hS0 : S 0 = 0)
    (q : ℝ≥0) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension
      (forceBoundaryData κ (typedRhoL w) (typedRhoR w)
        (fun i => -rightImg (fun s => -Ito.rpath S s) (-typedXL κ w (GW2Rd.upW (θ * chiC κ) c) i) q - Ito.rpath S q)
        (fun j => rightImg (Ito.rpath S) (typedXR κ w (GW2Rd.upW (θ * chiC κ) c) j) q - Ito.rpath S q))
      (forceJumpSet
        (fun i => -rightImg (fun s => -Ito.rpath S s) (-typedXL κ w (GW2Rd.upW (θ * chiC κ) c) i) q - Ito.rpath S q)
        (fun j => rightImg (Ito.rpath S) (typedXR κ w (GW2Rd.upW (θ * chiC κ) c) j) q - Ito.rpath S q)) G) :
    EqOn G (fun z => (stopWord κ (c, θ, recOf (q : ℝ≥0∞) (S, ⊤))).mean z + θ * chiC κ) H :=
  eqOn_explored_flowType (GW2Sf.isFlowType_of_upW (isFlowType_typed hw)) hS hS0 q hG

end InteractingSLE.Theorem14.GW2Psm
