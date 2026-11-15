/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxB0Rd
import InteractingSLE.Spec.Supplement.GW2WxMap
import InteractingSLE.Spec.Supplement.GW2PsmTMean
import InteractingSLE.Spec.Supplement.OrdFstShift
import InteractingSLE.Spec.Coupling.MartMeans2Lemma71
import InteractingSLE.Spec.Supplement.GW2TqCond

/-!
# The root stage's start identity at a root `x`, from the retained counterflow mean

Packet PROVE-GW2-GEOM2, round 14 (D49). Read from the root's start, the root piece's stage has the counterflow's
retained hull as its union. The retained mean (`GW2Fb.ae_eqOn_retMean_gw2`, the joint word of the counterflow word
`cw` in the relative chart) read in the root-`x` stage chart at clock `0`, `relChartX = relChart.recenter b` with
`b = baseRead x s rec`, is the stage-start identity of the root word map `upW (θ χ) (rootWordX κ cw x s rec)` (round 8,
the joint word re-centred by `b`): the re-centring moves the word (`mean_shiftW`), the lift of `relChart` is
`Im relLog − 2π` (`BW1LMean.relChart_lift_eq`), and `specOffset κ = 2πχ`.

* **`inst0_rootX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)

namespace InteractingSLE.Theorem14.GW2Kx

open GW2Kb GW2Psm GW2Omx Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem
  GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Sdi GW2Rd GW2Olm GW2Rz GW2Rv Supp8 GW2JointKernel
  Supp8.Q3Stop GW2Sde Restart.DomainMarkov MartChar.RealFlow Sec7.PocketTraversal GW2Xk
open Supp8.GB6 (relMap gb6Rec)
open Supp8.Q3Rel (invHull relLog)

/-- **The root stage's start identity from the retained mean** (root `x`, one sample). -/
theorem inst0_rootX {Ω : Type*} {κ θ : ℝ} (hκ : 0 < κ) (cw : BoundaryWord) (x : ℝ) {s : ℝ≥0}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hW0 : W 0 ω = 0) (hWc : Continuous fun t => W t ω)
    (hsζ : (s : ℝ≥0∞) < ζ ω) {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {u₀ w₁ : ℂ → ℝ}
    (hret : ∀ z ∈ H \ invHull (fun q : ℝ => W q.toNNReal ω) s, w₁ z + u₀ z =
      (jointWordOfRec (specOffset κ) κ cw (cfRec s W ζ ω)).mean (relMap (fun q : ℝ => W q.toNNReal ω) s z) -
        chiC κ * (relLog (fun q : ℝ => W q.toNNReal ω) s z).im)
    {w : WordType} (hw : wordType κ (upW (θ * chiC κ) (GW2Wm.rootWordX κ cw x s (cfRec s W ζ ω))) = w)
    {U₀ : ℂ → ℝ}
    (hU₀ : IsBoundedHarmonicExtension
      (forceBoundaryData κ (typedRhoL w) (typedRhoR w)
        (typedXL κ w (upW (θ * chiC κ) (GW2Wm.rootWordX κ cw x s (cfRec s W ζ ω))))
        (typedXR κ w (upW (θ * chiC κ) (GW2Wm.rootWordX κ cw x s (cfRec s W ζ ω)))))
      (forceJumpSet (typedXL κ w (upW (θ * chiC κ) (GW2Wm.rootWordX κ cw x s (cfRec s W ζ ω))))
        (typedXR κ w (upW (θ * chiC κ) (GW2Wm.rootWordX κ cw x s (cfRec s W ζ ω))))) U₀) :
    ∀ y ∈ ((stgChart (GW2Rz.relChartX x s (cfRec s W ζ ω)) R 0).dom : Set ℂ),
      w₁ y + u₀ y + (specOffset κ + θ * chiC κ) +
          chiC κ * (stgChart (GW2Rz.relChartX x s (cfRec s W ζ ω)) R 0).2.2 y =
        U₀ ((stgChart (GW2Rz.relChartX x s (cfRec s W ζ ω)) R 0).1 y) := by
  intro y hy
  set rec := cfRec s W ζ ω with hrec
  set U : ℝ → ℝ := fun q : ℝ => W q.toNNReal ω with hUdef
  set c₀ := Supp8.RelSafeS.relChart rec with hc₀def
  set cX := GW2Rz.relChartX x s rec with hcXdef
  set b := GW2Rz.baseRead x s rec with hb
  have hrs : BW1Ver.recS rec = s := NNReal.coe_injective (by
    rw [← BW1Ver.rtime_eq_recS]
    exact Supp8.GB6.rtime_recOf_cfE s hsζ)
  have hrd : ∀ q ∈ Icc (0 : ℝ) (BW1Ver.recS rec), rdrv rec q = U q := by
    intro q hq
    rw [hrec, cfRec]
    exact Supp8.GB6.rdrv_recOf_cfE s hW0 hWc.continuousOn hsζ (by rw [hrs] at hq; exact hq.2)
  have hRp : Continuous (Ito.rpath R) := hR.comp continuous_real_toNNReal
  have hRp0 : Ito.rpath R 0 = 0 := by simp [Ito.rpath, hR0]
  have hcX : cX.IsConformal := GW2Rz.isConformal_relChartX x s rec
  have hc₀ : c₀.IsConformal := Supp8.RelSafeS.isConformal_relChart rec
  -- the stage chart at clock `0` is the re-centred relative chart
  have e1 : (stgChart cX R 0).1 y = c₀.1 y - b := by
    change fwdMap (Ito.rpath R) ((0 : ℝ≥0) : ℝ) (cX.1 y) = _
    rw [NNReal.coe_zero, Exist.StagedLaw.fwdMap_zero_time hRp0]
    rfl
  have e2 : (stgChart cX R 0).2.2 y = c₀.2.2 y := by
    change (logDerivFwd (Ito.rpath R) ((0 : ℝ≥0) : ℝ) (cX.1 y)).im + cX.2.2 y = _
    rw [NNReal.coe_zero, Coupling.MartMeans2.logDerivFwd_zero, Complex.zero_im, zero_add]
    rfl
  -- the domain
  have hy₀ : y ∈ (c₀.dom : Set ℂ) := by
    rw [GW2Rd.dom_stgChart hcX hR hR0, NNReal.coe_zero, fwdHull_zero_eq_empty hRp hRp0, sdiff_empty] at hy
    obtain ⟨w', hw', rfl⟩ := hy
    rw [hc₀.coe_dom]
    refine ⟨w' + (b : ℂ), ?_, rfl⟩
    change 0 < (w' + (b : ℂ)).im
    have : 0 < w'.im := hw'
    simpa using this
  have hyD : y ∈ H \ invHull U s := by
    have h := hy₀
    rw [BW1LMean.coe_dom_relChart, hrs] at h
    have e : invHull (rdrv rec) (s : ℝ) = invHull U s := Supp8.RelSafeS.invHull_record_eq hW0 hWc.continuousOn hsζ
    rw [e] at h
    exact h
  have hlift : c₀.2.2 y = (relLog U s y).im - 2 * Real.pi := by
    rw [BW1LMean.relChart_lift_eq rec hy₀, Supp8.Q3Chain.relLog_eq_of_eqOn (BW1Ver.recS rec).coe_nonneg hrd, hrs]
  have hc1 : c₀.1 y = relMap U s y := relChart_gb6Rec_fst hW0 hWc.continuousOn hsζ y
  have hfH : (stgChart cX R 0).1 y ∈ H := (GW2Rd.isConformal_stgChart hcX hR hR0 0).fwd_mem hy
  rw [e1] at hfH
  have hU := eqOn_typed_upW_mean hκ (GW2Wm.rootWordX κ cw x s rec) (GW2Wm.isSorted_rootWordX κ cw x s rec)
    (θ * chiC κ) hw hU₀ _ hfH
  rw [e1, e2, hU]
  unfold GW2Wm.rootWordX
  rw [RLC.OrdDet.mean_shiftW, sub_add_cancel, hret y hyD, hc1, hlift]
  unfold specOffset
  ring

end InteractingSLE.Theorem14.GW2Kx
