/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmHarm
import InteractingSLE.Spec.Sec5.MarkovFlow

/-!
# GW2's open lines: the explicit stage mean restarted at a later stage start

Packet PROVE-GW2-STAGEMEAN, R121 round (deterministic; the chart side of the Claim(k) step):

* **`stgMeanR_restart`**: the explicit stage mean read from the stage start `a` at clock `q` IS the explicit stage mean
  read from the later stage start `a + q` at clock `0`, when the later stage-start mean `U₀` is the earlier flowed mean
  `U'` shifted by `σa − σa'` (the Loewner semigroup `fwdMap_add`, `Sec5.Markov.logDerivFwd_add`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)

namespace InteractingSLE.Theorem14.GW2Psm

open Exist.StagedLaw GW2Rd Supp8

/-- **The explicit stage mean restarted at a later stage start.** -/
theorem stgMeanR_restart (κ : ℝ) (rec : RecData) {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0)
    (a q : ℝ≥0) {U' U₀ u₀ : ℂ → ℝ} {σa' σa : ℝ} (hU : ∀ z ∈ H, U₀ z = U' z + (σa - σa')) {y : ℂ}
    (hy : y ∈ ((stgChart (RelSafeS.relChart rec) R (a + q)).dom : Set ℂ)) :
    stgMeanR κ rec R a (q : ℝ) U' u₀ σa' y = stgMeanR κ rec R (a + q) 0 U₀ u₀ σa y := by
  set c := RelSafeS.relChart rec with hc
  set w : ℝ → ℝ := Ito.rpath R with hw
  have hwc : Continuous w := hR.comp continuous_real_toNNReal
  have hw0 : w 0 = 0 := by simp [hw, Ito.rpath, hR0]
  have hcsD := isDomainChart_stgChart_relChart rec hR hR0 (a + q)
  set z := c.1 y with hz
  -- `z` is not swallowed by `a + q`
  have hfwd := hcsD.fwd_mem hy
  have hzK : z ∈ H \ fwdHull w ((a + q : ℝ≥0) : ℝ) := by
    have hy' := hy
    rw [hcsD.coe_dom] at hy'
    have hdom := hcsD.isConformal
    rw [hdom.coe_dom] at hy'
    obtain ⟨v, hv, hvy⟩ := hy'
    have h1 : (stgChart c R (a + q)).2.1 v = c.2.1 (QuantumZipper.fwdMapInv w ((a + q : ℝ≥0) : ℝ) v) := rfl
    have hz' : z = QuantumZipper.fwdMapInv w ((a + q : ℝ≥0) : ℝ) v := by
      rw [hz, ← hvy, h1]
      exact (RelSafeS.isConformal_relChart rec).2.2 _ (QuantumZipper.RS.fwdMapInv_mem_H hwc hw0 (by positivity) hv)
    rw [hz']
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hwc hw0 (by positivity) hv
  have haq : ((a + q : ℝ≥0) : ℝ) = (a : ℝ) + q := NNReal.coe_add a q
  rw [haq] at hzK
  -- the restarted driver is the stage driver
  have hshift : ∀ r ∈ Icc (0 : ℝ) q, (fun r => w ((a : ℝ) + r) - w a) r = Ito.rpath (stgDrv R a) r :=
    fun r hr => (rpath_stgDrv_eq R a hr.1).symm
  have hF : fwdMap (fun r => w ((a : ℝ) + r) - w a) q = fwdMap (Ito.rpath (stgDrv R a)) q :=
    QuantumZipper.CharFunRhs.fwdMap_eq_of_eqOn hshift
  have hL : logDerivFwd (fun r => w ((a : ℝ) + r) - w a) q = logDerivFwd (Ito.rpath (stgDrv R a)) q :=
    QuantumZipper.CharFunRhs.logDerivFwd_eq_of_eqOn q.coe_nonneg hshift
  have hfa := QuantumZipper.fwdMap_add hwc hzK.1 a.coe_nonneg q.coe_nonneg
    (Ito.exists_isForwardSol_of_mem (by positivity) hzK)
  have hla := Sec5.Markov.logDerivFwd_add hwc a.coe_nonneg q.coe_nonneg hzK
  rw [hF] at hfa
  rw [hL] at hla
  -- both sides
  have hne : fwdMap w ((a : ℝ) + q) z ≠ 0 := by
    have h := hcsD.fwd_mem hy
    have e : (stgChart c R (a + q)).1 y = fwdMap w ((a : ℝ) + q) z := by
      show fwdMap w ((a + q : ℝ≥0) : ℝ) (c.1 y) = _
      rw [haq]
    rw [e] at h
    intro h0
    rw [h0] at h
    have h' : (0 : ℝ) < (0 : ℂ).im := h
    simp at h'
  have hS0 : Ito.rpath (stgDrv R (a + q)) 0 = 0 := by simp [Ito.rpath, stgDrv_zero]
  unfold stgMeanR
  rw [Coupling.MartMeans2.couplingMean_zero κ hS0 U₀ (by
    show fwdMap w ((a + q : ℝ≥0) : ℝ) (c.1 y) ≠ 0
    rw [haq]
    exact hne)]
  have e1 : (stgChart c R a).1 y = fwdMap w a z := rfl
  have e2 : (stgChart c R (a + q)).1 y = fwdMap w ((a : ℝ) + q) z := by
    show fwdMap w ((a + q : ℝ≥0) : ℝ) (c.1 y) = _
    rw [haq]
  have e3 : (stgChart c R a).2.2 y = (logDerivFwd w a z).im + c.2.2 y := rfl
  have e4 : (stgChart c R (a + q)).2.2 y = (logDerivFwd w ((a : ℝ) + q) z).im + c.2.2 y := by
    show (logDerivFwd w ((a + q : ℝ≥0) : ℝ) (c.1 y)).im + c.2.2 y = _
    rw [haq]
  rw [e1, e2, e3, e4, hla, Complex.add_im, hU _ (by rw [← e2]; exact hcsD.fwd_mem hy)]
  unfold couplingMean
  rw [← hfa]
  ring

end InteractingSLE.Theorem14.GW2Psm
