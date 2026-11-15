/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR8Chain

/-! # GW2: the chart mean for typed geometric marks and relative driver versions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW2JDetR8

open Supp8 Supp8.GB6 Supp8.Q3Chain Supp8.GB6LMean
open Exist.StagedLaw GW2JointKernel RelSafeS Restart Sec7.PocketTraversal

/-- Flowed boundary data at any angle only use the driver through that time. -/
theorem bhe_flowed_congr {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {W R : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hR : Continuous R) (hR0 : R 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (he : EqOn W R (Icc 0 q)) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension (flowedData κ ρL ρR xL xR W q)
      (flowedJumps xL xR W q) G) :
    IsBoundedHarmonicExtension (flowedData κ ρL ρR xL xR R q)
      (flowedJumps xL xR R q) G := by
  have hL := funext fun i => markPosL_congr_eqOn hW hW0 hR hR0 hq he (hxL i)
  have hRi := funext fun j => markPos_congr_eqOn hW hW0 hR hR0 hq he (hxR j)
  simpa only [flowedData, flowedJumps, hL, hRi] using hG

/-- The chart form used by the lines step, with the canonical extension of
any typing of the current angle word and the geometric marks of `R`. -/
theorem chartTransport_eq_bheProc {κ θ : ℝ} (hκ : 0 < κ) {c : BoundaryWord}
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (ht : FCDet.IsFlowType κ θ c xL xR ρL ρR)
    {r : RecData} {s : ℝ≥0} (hr : rtime r = s) {U : ℝ → ℝ}
    (hU : EqOn (rdrv r) U (Icc 0 (s : ℝ)))
    {S : Set ℂ} {R : ℝ≥0 → ℝ} {Wr : ℝ → ℝ} {q : ℝ≥0}
    (hO : H \ S = (relChart r).2.1 '' (H \ fwdHull (Ito.rpath R) q))
    {g : DistOn upperHalfPlaneOpens} {wU u₀ G : ℂ → ℝ}
    (hwU : InnerProductSpace.HarmonicOnNhd wU (H \ S))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hrep : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ S →
      g φ = ∫ z, wU z * φ z)
    (hv : EqOn (fun z => wU z + u₀ z)
      (fun z => G (fwdMap Wr q (relMap U s z)) - chiC κ *
        ((logDerivFwd Wr q (relMap U s z)).im + (Q3Rel.relLog U s z).im)) (H \ S))
    (he : EqOn Wr (Ito.rpath R) (Icc 0 (q : ℝ)))
    (hRc : Continuous R) (hR0 : R 0 = 0)
    (hG : IsBoundedHarmonicExtension
      (flowedData κ (flowLineRhoL κ c.fn c.jumps 0 θ)
        (flowLineRhoR κ c.fn c.jumps 0 θ) (flowLineXL c.fn c.jumps 0)
        (flowLineXR c.fn c.jumps 0) (Ito.rpath R) q)
      (flowedJumps (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
        (Ito.rpath R) q) G)
    {ψ : TestOn upperHalfPlaneOpens} (hψ : Disjoint (tsupport ψ) (fwdHull (Ito.rpath R) q)) :
    Chart.chartTransport (isConformal_relChart r) 1 (specOffset κ) (chiC κ)
        (g + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
      ∫ y, couplingMean κ (Ito.rpath R) q
        (DomainMarkov.bheProc κ ρL ρR (fun t (_ : Unit) => R t)
          (geomLW (fun t (_ : Unit) => R t) (fun _ => xL))
          (geomRW (fun t (_ : Unit) => R t) (fun _ => xR)) () q) y * ψ y := by
  have hGG := eqOn_bheProc_of_flowType ht (Ω := Unit)
    (R := fun t _ => R t) (ω := ()) hRc hR0 q hG
  exact chartTransport_eq_couplingMean hκ hr hU hO hwU hu₀ hrep hv he
    (hRc.comp continuous_real_toNNReal) hGG hψ

/-- A relative driver version that generates the same physical hulls through
`T` has the same chart mean. Equality of the drivers is proved by the landed
hull-uniqueness theorem and is not an extra mean-identification hypothesis. -/
theorem chartTransport_eq_bheProc_of_hulls {κ θ : ℝ} (hκ : 0 < κ) {c : BoundaryWord}
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (ht : FCDet.IsFlowType κ θ c xL xR ρL ρR)
    {r : RecData} {s T : ℝ≥0} (hr : rtime r = s) {U W Wr : ℝ → ℝ}
    (hU : EqOn (rdrv r) U (Icc 0 (s : ℝ))) {R : ℝ≥0 → ℝ}
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hRc : Continuous R) (hR0 : R 0 = 0)
    (ha0 : relClock U s W 0 = 0)
    (hac : ContinuousOn (fun t : ℝ≥0 => relClock U s W t) (Icc 0 T))
    (hW : HullsUpTo U s W Wr T) (hR : HullsUpTo U s W (Ito.rpath R) T)
    {q : ℝ≥0} (hq : (q : ℝ) = relClock U s W T)
    {S : Set ℂ} (hO : H \ S = (relChart r).2.1 '' (H \ fwdHull (Ito.rpath R) q))
    {g : DistOn upperHalfPlaneOpens} {wU u₀ G : ℂ → ℝ}
    (hwU : InnerProductSpace.HarmonicOnNhd wU (H \ S))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hrep : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ S →
      g φ = ∫ z, wU z * φ z)
    (hv : EqOn (fun z => wU z + u₀ z)
      (fun z => G (fwdMap Wr q (relMap U s z)) - chiC κ *
        ((logDerivFwd Wr q (relMap U s z)).im + (Q3Rel.relLog U s z).im)) (H \ S))
    (hG : IsBoundedHarmonicExtension
      (flowedData κ (flowLineRhoL κ c.fn c.jumps 0 θ)
        (flowLineRhoR κ c.fn c.jumps 0 θ) (flowLineXL c.fn c.jumps 0)
        (flowLineXR c.fn c.jumps 0) Wr q)
      (flowedJumps (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) Wr q) G)
    {ψ : TestOn upperHalfPlaneOpens} (hψ : Disjoint (tsupport ψ) (fwdHull (Ito.rpath R) q)) :
    Chart.chartTransport (isConformal_relChart r) 1 (specOffset κ) (chiC κ)
        (g + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
      ∫ y, couplingMean κ (Ito.rpath R) q
        (DomainMarkov.bheProc κ ρL ρR (fun t (_ : Unit) => R t)
          (geomLW (fun t (_ : Unit) => R t) (fun _ => xL))
          (geomRW (fun t (_ : Unit) => R t) (fun _ => xR)) () q) y * ψ y := by
  have hRp := hRc.comp continuous_real_toNNReal
  have hRp0 : Ito.rpath R 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using hR0
  have he := eqOn_of_hullsUpTo hWr hWr0 hRp hRp0 ha0 hac hW hR
  rw [← hq] at he
  have hGR := bhe_flowed_congr (fun i => GW3Word.flowLineXL_nonpos _ _ i)
    (fun j => GW3Word.flowLineXR_nonneg _ _ j) hWr hWr0 hRp hRp0 q.coe_nonneg he hG
  exact chartTransport_eq_bheProc hκ ht hr hU hO hwU hu₀ hrep hv he hRc hR0 hGR hψ

end InteractingSLE.Theorem14.GW2JDetR8
