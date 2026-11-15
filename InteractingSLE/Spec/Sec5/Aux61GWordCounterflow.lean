/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWordReturn
import InteractingSLE.Spec.Sec5.Aux61GNextRegular

/-! # Counterflow reference cancellation in the retained restart chart

The physical mean is the actual theta-dependent counterflow mean with the
harmonic base restored. Its returned finite word supplies the height limit.
The remaining inputs specify the chart access and the inherited relative
phase; no principal-argument reset is made.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open QuantumZipper (H chiC)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61GWord
open WangWu GlueCond LawUnique Cond44Ref
open Aux61Fib (FibData)

/-- The actual counterflow reference has the required regular germ when
the returned word and inherited relative phase match the chosen reference.
Physical harmonic heights are derived from the stopped force word. -/
theorem tendsto_charted_counterflow_sub_refMean0 (d : FibData) (θ : ℝ)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {u₀ u' : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension
      (forceBoundaryData d.κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hu' : IsBoundedHarmonicExtension
      (cfWordData d.κ
        (fun x => forceBoundaryData d.κ ρL ρR xL xR x + -(θ * chiC d.κ))
        (forceJumpFinset xL xR))
      (cfWordJumps d.κ
        (fun x => forceBoundaryData d.κ ρL ρR xL xR x + -(θ * chiC d.κ))
        (forceJumpFinset xL xR)) u')
    (s : ℝ≥0) (y : HistorySpace 0 0) {c : Chart} (hc : c.IsConformal)
    (hsub : (c.dom : Set ℂ) ⊆ H \ cfHullQ s y)
    {a ξ phase offset : ℝ} (ha0 : a ≠ 0) (haJ : a ∉ d.JR)
    (hξ : ξ ∉ returnedCfJumps d.κ
      (fun x => forceBoundaryData d.κ ρL ρR xL xR x + -(θ * chiC d.κ))
      (forceJumpFinset xL xR) s y)
    (htransition : Tendsto
      (fun z => revChart (Ito.rpath (Sec4.regPath (cfStop s y))) s (c.2.1 z))
      (𝓝[H] (a : ℂ)) (𝓝[H] (ξ : ℂ)))
    (hrelative_phase : Tendsto (fun z => c.2.2 (c.2.1 z) -
      (GlueImg.logDerivPsi (Ito.rpath (Sec4.regPath (cfStop s y))) s (c.2.1 z)).im)
      (𝓝[H] (a : ℂ)) (𝓝 phase))
    (hword : d.bR a = returnedCfData d.κ
      (fun x => forceBoundaryData d.κ ρL ρR xL xR x + -(θ * chiC d.κ))
      (forceJumpFinset xL xR) s y ξ + θ * chiC d.κ + offset + chiC d.κ * phase) :
    Tendsto (fun z =>
      cfMeanQ d.κ
        (fun x => forceBoundaryData d.κ ρL ρR xL xR x + -(θ * chiC d.κ))
        (forceJumpFinset xL xR) u' s y (c.2.1 z) + u₀ (c.2.1 z) + offset +
        chiC d.κ * c.2.2 (c.2.1 z) - Aux61GlueK.refMean0 d z)
      (𝓝[H] (a : ℂ)) (𝓝 0) := by
  have hheight := (tendsto_returnedCfMean d.κ
    (fun x => forceBoundaryData d.κ ρL ρR xL xR x + -(θ * chiC d.κ))
    (forceJumpFinset xL xR) s y hξ).comp htransition
  have ht := (((hheight.add_const (θ * chiC d.κ)).add_const offset).add
    (hrelative_phase.const_mul (chiC d.κ))).sub
      (Aux61GNext.tendsto_refMean0_regular d ha0 haJ)
  rw [← hword, sub_self] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he := CrossCond.Theta.cfMeanQ_add_eq_retMean_addT d.κ_pos θ ρL ρR xL xR
    hu₀ hu' s y (hsub (hc.inv_mem_dom hz))
  dsimp only [Function.comp_apply]
  linarith only [he]

end InteractingSLE.Sec5.Aux61GWord
