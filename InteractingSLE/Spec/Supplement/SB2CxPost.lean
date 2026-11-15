/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CxMark
import InteractingSLE.Spec.Supplement.SB2CxEng
import InteractingSLE.Spec.Sec5.MarkovFlow

/-!
# B's explored mean read in the post-head chart

Packet PROVE-SB2-CONDFIN, round 12 (decision D66, item (M)). At the root the S2 clause is stated in the post-head
chart `c' = c.loewner V τ` (B's stage chart followed by the Loewner map of the head, `V` the driver stopped at the
entrance `τ`) with the shifted driver `shiftDrive W τ` and the time `s − τ`. B's explored mean is known in the stage
chart: `M (f_s (c z)) − χ (Im log f_s′(c z) + lift z)` with `M` the mean of B's stop word `stopWord (β, θ, r)`,
`r` a record of `(W, s)`. Deterministic facts:

* **`fwdMap_postHead`**, **`im_logDerivFwd_postHead`**: the forward map and the argument of its derivative compose
  through the head (`QuantumZipper.fwdMap_add`, `Sec5.Markov.logDerivFwd_add`, the head drivers agreeing on
  `[0, τ]`);
* **`postHead_explored`**: the same function `M` is the explored mean in the post-head chart, and it is the bounded
  harmonic extension of the flowed data of B's force marks read at `τ` (`markPos`/`markPosL` at `τ`) under the
  shifted driver — exactly the `hind₂` clause of `Cx.ae_lineMean_pos_rootG` (`Cx.flowedData_shiftDrive` and
  `Om.eqOn_explored_mean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H chiC IsForwardSol fwdMap fwdHull logDerivFwd)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.SB.Cx

open Exist.StagedLaw (markPos markPosL)
open Exist Exist.StagedLaw Restart

variable {W V : ℝ → ℝ} {τ s : ℝ} {p : ℂ}

/-- **The forward map through the head.** -/
theorem fwdMap_postHead (hW : Continuous W) (hV : Continuous V) (hτ : 0 ≤ τ) (hτs : τ ≤ s)
    (hVW : ∀ r ∈ Icc (0 : ℝ) τ, V r = W r) (hp : p ∈ H \ fwdHull W s) :
    fwdMap W s p = fwdMap (shiftDrive W τ) (s - τ) (fwdMap V τ p) := by
  have hs : 0 ≤ s := hτ.trans hτs
  have e : s = τ + (s - τ) := by ring
  have hex := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hs hp.1 hp.2
  rw [e] at hex
  have h := QuantumZipper.fwdMap_add hW hp.1 hτ (sub_nonneg.2 hτs) hex
  rw [← e] at h
  rw [h, QuantumZipper.fwdMap_congr_drive hW hV hp.1 hτ fun r hr => (hVW r hr).symm]
  rfl

/-- The head's derivative logarithm depends only on the driver on `[0, τ]`. -/
theorem logDerivFwd_congr_drive (hW : Continuous W) (hV : Continuous V) (hτ : 0 ≤ τ)
    (hVW : ∀ r ∈ Icc (0 : ℝ) τ, V r = W r) (hp : p ∈ H) : logDerivFwd W τ p = logDerivFwd V τ p := by
  unfold QuantumZipper.logDerivFwd
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hτ] at hr
  rw [QuantumZipper.fwdMap_congr_drive hW hV hp hr.1 fun q hq => (hVW q ⟨hq.1, hq.2.trans hr.2⟩).symm]

/-- **The argument of the derivative through the head.** -/
theorem im_logDerivFwd_postHead (hW : Continuous W) (hV : Continuous V) (hτ : 0 ≤ τ) (hτs : τ ≤ s)
    (hVW : ∀ r ∈ Icc (0 : ℝ) τ, V r = W r) (hp : p ∈ H \ fwdHull W s) :
    (logDerivFwd W s p).im =
      (logDerivFwd (shiftDrive W τ) (s - τ) (fwdMap V τ p)).im + (logDerivFwd V τ p).im := by
  have e : s = τ + (s - τ) := by ring
  have hp' : p ∈ H \ fwdHull W (τ + (s - τ)) := by rw [← e]; exact hp
  have h := Sec5.Markov.logDerivFwd_add hW hτ (sub_nonneg.2 hτs) hp'
  rw [← e] at h
  rw [h, logDerivFwd_congr_drive hW hV hτ hVW hp.1,
    QuantumZipper.fwdMap_congr_drive hW hV hp.1 hτ fun r hr => (hVW r hr).symm, Complex.add_im, add_comm]
  rfl

/-- **B's explored mean in the post-head chart** (deterministic): the stop word's mean `M` read through the stage
chart equals `M` read through the post-head chart with the shifted driver, at every point off B's explored set; and
`M` (shifted by `θχ`) is the bounded harmonic extension of the flowed data of B's marks read at `τ` under the
shifted driver. -/
theorem postHead_explored {κ θ : ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (hV : Continuous V) (hτ : 0 ≤ τ)
    (hτs : τ ≤ s) (hVW : ∀ r ∈ Icc (0 : ℝ) τ, V r = W r) {β : BoundaryWord} {r : RecData} (hrw : rdrv r = W)
    (hrt : rtime r = s) {c : Chart} (hc : c.IsConformal) {A₂ : Set ℂ} (hdom₂ : H \ (c.dom : Set ℂ) ⊆ A₂)
    (hcorr : ∀ v ∈ H, c.2.1 v ∈ A₂ ↔ v ∈ fwdHull W s) :
    (∃ (nL' nR' : ℕ) (ρL' : Fin nL' → ℝ) (ρR' : Fin nR' → ℝ) (xL' : Fin nL' → ℝ) (xR' : Fin nR' → ℝ),
      (∀ i, xL' i ≤ 0) ∧ (∀ j, 0 ≤ xR' j) ∧
      ∀ G : ℂ → ℝ, IsBoundedHarmonicExtension
          (Supp8.Q3Chain.flowedData κ ρL' ρR' xL' xR' (shiftDrive W τ) (s - τ))
          (Supp8.Q3Chain.flowedJumps xL' xR' (shiftDrive W τ) (s - τ)) G →
        EqOn G (fun z => (stopWord κ (β, θ, r)).mean z + θ * chiC κ) H) ∧
    ∀ z ∈ H \ A₂,
      (stopWord κ (β, θ, r)).mean (fwdMap W s (c.1 z)) - chiC κ * ((logDerivFwd W s (c.1 z)).im + c.2.2 z) =
        (stopWord κ (β, θ, r)).mean (fwdMap (shiftDrive W τ) (s - τ) ((c.loewner V τ).1 z)) -
          chiC κ * ((logDerivFwd (shiftDrive W τ) (s - τ) ((c.loewner V τ).1 z)).im + (c.loewner V τ).2.2 z) := by
  have hFO := Theorem15.isOrderedForceWord_flowLine β.fn β.jumps 0
  have hxL : ∀ i, flowLineXL β.fn β.jumps 0 i ≤ 0 := hFO.2.1
  have hxR : ∀ j, 0 ≤ flowLineXR β.fn β.jumps 0 j := hFO.2.2.2
  have hs' : 0 ≤ s - τ := sub_nonneg.2 hτs
  refine ⟨⟨_, _, flowLineRhoL κ β.fn β.jumps 0 θ, flowLineRhoR κ β.fn β.jumps 0 θ,
    fun i => markPosL W τ (flowLineXL β.fn β.jumps 0 i), fun j => markPos W τ (flowLineXR β.fn β.jumps 0 j),
    fun i => GW1W.markPosL_nonpos hW hW0 hτ (hxL i), fun j => GW1W.markPos_nonneg hW hW0 hτ (hxR j),
    fun G hG => ?_⟩, fun z hz => ?_⟩
  · rw [flowedData_shiftDrive hW hW0 hτ hs' κ _ _ hxL hxR, flowedJumps_shiftDrive hW hW0 hτ hs' hxL hxR,
      add_sub_cancel, ← hrw, ← hrt] at hG
    exact Om.eqOn_explored_mean β r hG
  · have hzd : z ∈ (c.dom : Set ℂ) := by
      by_contra hn
      exact hz.2 (hdom₂ ⟨hz.1, hn⟩)
    have hpH : c.1 z ∈ H := hc.fwd_mem hzd
    have hpK : c.1 z ∉ fwdHull W s := fun hK => by
      have h1 := (hcorr _ hpH).2 hK
      rw [hc.inv_fwd hzd] at h1
      exact hz.2 h1
    have hp : c.1 z ∈ H \ fwdHull W s := ⟨hpH, hpK⟩
    show _ = (stopWord κ (β, θ, r)).mean (fwdMap (shiftDrive W τ) (s - τ) (fwdMap V τ (c.1 z))) -
      chiC κ * ((logDerivFwd (shiftDrive W τ) (s - τ) (fwdMap V τ (c.1 z))).im +
        ((logDerivFwd V τ (c.1 z)).im + c.2.2 z))
    rw [fwdMap_postHead hW hV hτ hτs hVW hp, im_logDerivFwd_postHead hW hV hτ hτs hVW hp]
    ring

end InteractingSLE.Theorem14.SB.Cx
