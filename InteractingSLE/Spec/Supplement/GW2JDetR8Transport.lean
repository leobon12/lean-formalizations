/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2FbLocal
import InteractingSLE.Spec.Supplement.GB6LMeanFinal

/-! # GW2: transport a represented union mean to the joint chart -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW2JDetR8

open Supp8 Supp8.GB6 Supp8.GB6LMean Exist.StagedLaw GW2JointKernel RelSafeS

/-- The landed GB6 transport identity at the dual parameter. The represented
mean may come from any angle; all angle dependence is carried by `G`. -/
theorem chartTransport_eq_couplingMean {κ : ℝ} (hκ : 0 < κ)
    {r : RecData} {s : ℝ≥0} (hr : rtime r = s) {U : ℝ → ℝ}
    (hU : ∀ x ∈ Icc (0 : ℝ) s, rdrv r x = U x)
    {S : Set ℂ} {Rp Wr : ℝ → ℝ} {u : ℝ≥0}
    (hO : H \ S = (relChart r).2.1 '' (H \ fwdHull Rp u))
    {g : DistOn upperHalfPlaneOpens} {wU u₀ : ℂ → ℝ}
    (hwU : InnerProductSpace.HarmonicOnNhd wU (H \ S))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hrep : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ S →
      g φ = ∫ z, wU z * φ z) {G Gb : ℂ → ℝ}
    (hv : EqOn (fun z => wU z + u₀ z)
      (fun z => G (fwdMap Wr u (relMap U s z)) - chiC κ *
        ((logDerivFwd Wr u (relMap U s z)).im + (Q3Rel.relLog U s z).im)) (H \ S))
    (hWR : EqOn Wr Rp (Icc 0 (u : ℝ))) (hRp : Continuous Rp)
    (hGG : EqOn G Gb H) {ψ : TestOn upperHalfPlaneOpens}
    (hψ : Disjoint (tsupport ψ) (fwdHull Rp u)) :
    Chart.chartTransport (isConformal_relChart r) 1 (specOffset κ) (chiC κ)
        (g + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
      ∫ y, couplingMean κ Rp u Gb y * ψ y := by
  have hdual : 16 / (16 / κ) = κ := by field_simp [ne_of_gt hκ]
  simpa only [hdual, specOffset] using
    GB6LMean.chartTransport_eq_couplingMean (16 / κ) hr hU hO hwU hu₀ hrep
      (by simpa only [hdual] using hv) hWR hRp hGG hψ

end InteractingSLE.Theorem14.GW2JDetR8
