/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR8Marks

/-! # GW2: frozen-chain locality and the complement in the recorded joint chart -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2JDetR8

open GW2Fb Supp8 Supp8.GB6 Supp8.Q3Rel Supp8.Q3Chain Supp8.GB6LMean
open Exist.StagedLaw RelSafeS GW2JointKernel

section Chain

variable {κ : ℝ} {nL nR mL mR : ℕ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {σL : Fin mL → ℝ} {σR : Fin mR → ℝ} {yL : Fin mL → ℝ} {yR : Fin mR → ℝ}
  {U : ℝ → ℝ} {s T : ℝ≥0} {w : ℝ≥0 → ℝ}
  {p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ)}

/-- Every physical hull and clock value through the stopped time is the one
of the frozen explored driver; its relative driver generates these hulls. -/
theorem relChainStop_prefix
    (hp : IsRelChainStop κ ρL ρR xL xR σL σR yL yR U s w T p) :
    ∀ t : ℝ≥0, t ≤ T →
      fwdHull (fun r : ℝ => p.1 r.toNNReal) t = fwdHull (fun r : ℝ => w r.toNNReal) t ∧
      relClock U s (fun r : ℝ => p.1 r.toNNReal) t =
        relClock U s (fun r : ℝ => w r.toNNReal) t ∧
      relMap U s '' fwdHull (fun r : ℝ => w r.toNNReal) t =
        fwdHull p.2.2.1 (relClock U s (fun r : ℝ => w r.toNNReal) t) := by
  obtain ⟨t₂, hTt₂, hweq⟩ := hp.2.2.2.1
  intro t ht
  have hh : fwdHull (fun r : ℝ => p.1 r.toNNReal) t =
      fwdHull (fun r : ℝ => w r.toNNReal) t := by
    refine fwdHull_eq_of_eqOn t.coe_nonneg
      (NNReal.coe_lt_coe.mpr (ht.trans_lt hTt₂)) fun r hr => ?_
    exact hweq _ (Real.toNNReal_le_iff_le_coe.mpr hr.2)
  have ha : relClock U s (fun r : ℝ => p.1 r.toNNReal) t =
      relClock U s (fun r : ℝ => w r.toNNReal) t := by
    unfold relClock
    rw [hh]
  refine ⟨hh, ha, ?_⟩
  have h := hp.2.2.2.2.2.2.2.2.2.1 t ht
  rwa [hh, ha] at h

/-- Separation is already a field of FABLE's configuration, rather than a
new geometric assumption on the relative chain. -/
theorem relChainStop_disjoint
    (hp : IsRelChainStop κ ρL ρR xL xR σL σR yL yR U s w T p) :
    Disjoint (closure (fwdHull (fun r : ℝ => p.1 r.toNNReal) T))
      (closure (invHull U s)) := by
  obtain ⟨G₀, hG₀⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData
    κ σL σR yL yR
  obtain ⟨GE, hGE⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData
    κ ρL ρR (fun i => markPosL (fun r : ℝ => p.1 r.toNNReal) T (xL i))
      (fun j => markPos (fun r : ℝ => p.1 r.toNNReal) T (xR j))
  obtain ⟨G, hG⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData
    κ σL σR (fun i => markPosL p.2.2.1
      (relClock U s (fun r : ℝ => p.1 r.toNNReal) T) (yL i))
      (fun j => markPos p.2.2.1 (relClock U s (fun r : ℝ => p.1 r.toNNReal) T) (yR j))
  have hc := hp.2.2.2.2.2.2.2.2.2.2 G₀ GE G
    (fun z => G (QuantumZipper.fwdMap p.2.2.1
      (relClock U s (fun r : ℝ => p.1 r.toNNReal) T) (relMap U s z)) -
      QuantumZipper.chiC κ * ((QuantumZipper.logDerivFwd p.2.2.1
        (relClock U s (fun r : ℝ => p.1 r.toNNReal) T) (relMap U s z)).im +
          (relLog U s z).im))
    (by rwa [coe_initJumps])
    (by simpa only [flowedData, flowedJumps, coe_initJumps] using hGE)
    (by simpa only [flowedData, flowedJumps, coe_initJumps] using hG) (fun _ => rfl)
  exact hc.disj

end Chain

/-- The complement of a separated physical union is exactly the inverse
recorded joint-chart image of the relative hull complement. -/
theorem compl_union_eq_relChart {r : RecData} {s : ℝ≥0} (hr : rtime r = s)
    {U : ℝ → ℝ} (hUc : Continuous U) (hU : EqOn (rdrv r) U (Icc 0 (s : ℝ)))
    {K : Set ℂ} (hK : K ⊆ H) (hdis : Disjoint (closure K) (closure (invHull U s)))
    {R : ℝ → ℝ} {Q : ℝ} (hh : relMap U s '' K = fwdHull R Q) :
    H \ (invHull U s ∪ K) = (relChart r).2.1 '' (H \ fwdHull R Q) := by
  have hm := relMap_eq_of_eqOn s.coe_nonneg hU
  have hA : invHull (rdrv r) s = invHull U s := by
    unfold invHull
    rw [QuantumZipper.CharFunRhs.fwdHull_eq_of_eqOn
      (continuous_rdrv r) hUc s.coe_nonneg hU]
  have hdc := isDomainChart_rel (continuous_rdrv r) (rdrv_zero r) s.coe_nonneg
  have hKD : K ⊆ H \ invHull (rdrv r) s := by
    intro z hz
    refine ⟨hK hz, ?_⟩
    rw [hA]
    exact fun hzA => Set.disjoint_left.mp hdis (subset_closure hz) (subset_closure hzA)
  rw [← hh, ← hm, relChart_eq_jointChart hr]
  change H \ (invHull U s ∪ K) =
    (jointChart (rdrv r) s).2.1 '' (H \ (jointChart (rdrv r) s).1 '' K)
  rw [image_inv_compl_image_fwd hdc.1 hdc.2.1 hKD, hA, Set.sdiff_sdiff]

end InteractingSLE.Theorem14.GW2JDetR8
