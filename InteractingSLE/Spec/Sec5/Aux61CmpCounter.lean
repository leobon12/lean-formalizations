/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CmpCover
import InteractingSLE.Spec.Sec5.Aux61GWordCounterflow

/-! # The counterflow side of the cover from its regular transition

`CounterGerm` (the counterflow clause of `PastGermCover`) at a window point
`b` follows from: a landing point `z₀` of the inverse chart in the counterflow
hull or on `ℝ`, a ball around `z₀` whose part off the counterflow hull lies in
the retained domain, a regular transition `Ψ_s ∘ c⁻¹ → ξ` into the
counterflow chart, the inherited relative phase limit, and the reference
height identity with the returned counterflow word (`counterGerm_of_transition`).

The mean clause is the landed returned-word calculation of
`Aux61GWord.tendsto_charted_counterflow_sub_refMean0`, redone here at the
source parameter `S.κ` with the actual source counterflow mean. The
containment clause uses the actual zero-time marked set `H \ dom c`.
Deterministic in the access data; no source statement is replaced.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cmp
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61ChLoc LawUnique GlueCond
open WangWu Cond44Ref Aux61GWord
universe u

variable {S : SourceSetting.{u}} {F : SourceRestartData S.Ω S.nL S.nR}

/-- The retained counterflow driver read from the glued record. -/
abbrev cfW (S : SourceSetting.{u}) (p : S.Ω × HistorySpace 0 0) : ℝ → ℝ :=
  Ito.rpath (Sec4.regPath (cfStop (rationalTime S.s) p.2))

/-- **The counterflow clause from a regular transition.** -/
theorem counterGerm_of_transition {i : F.ι} {p : S.Ω × HistorySpace 0 0}
    (hc : ((S.marksData F).chart i p).IsConformal)
    (hsub : (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ cfHullQ (rationalTime S.s) p.2)
    (hlive : p ∈ liveEv ((S.marksData F).Z i) ((S.marksData F).B i) ((S.marksData F).code i) 0)
    {b ξ phase : ℝ} {z₀ : ℂ} (hb0 : b ≠ 0) (hbJ : b ∉ (F.data i).JR)
    (hξ : ξ ∉ returnedCfJumps S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
      (rationalTime S.s) p.2)
    (htransition : Tendsto (fun z => revChart (cfW S p) (rationalTime S.s)
      (((S.marksData F).chart i p).2.1 z)) (𝓝[H] (b : ℂ)) (𝓝[H] (ξ : ℂ)))
    (hphase : Tendsto (fun z => ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
      (GlueImg.logDerivPsi (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 z)).im)
      (𝓝[H] (b : ℂ)) (𝓝 phase))
    (hword : (F.data i).bR b = returnedCfData S.κ (sourceCounterBoundary S)
      (forceJumpFinset S.xL S.xR) (rationalTime S.s) p.2 ξ + S.θ * chiC S.κ + chiC S.κ * phase)
    (hz₀ : z₀ ∈ cfHullQ (rationalTime S.s) p.2 ∪ {z : ℂ | z.im = 0})
    (hland : Tendsto ((S.marksData F).chart i p).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀))
    (hball : ∃ ρ > 0, ball z₀ ρ ∩ (H \ cfHullQ (rationalTime S.s) p.2) ⊆
      ((S.marksData F).chart i p).dom) :
    CounterGerm S F i p b := by
  refine ⟨z₀, hz₀, ?_, hland, ?_⟩
  · obtain ⟨ρ, hρ, hb⟩ := hball
    refine ⟨ρ, hρ, fun w hw => ?_⟩
    rw [baseSets_zero_eq S F hc hlive] at hw
    by_contra hwK
    exact hw.1.2 (hb ⟨hw.2, hw.1.1, hwK⟩)
  · have hheight := (tendsto_returnedCfMean S.κ (sourceCounterBoundary S)
      (forceJumpFinset S.xL S.xR) (rationalTime S.s) p.2 hξ).comp htransition
    have ht := ((hheight.add_const (S.θ * chiC S.κ)).add (hphase.const_mul (chiC S.κ))).sub
      (Aux61GNext.tendsto_refMean0_regular (F.data i) hb0 hbJ)
    rw [← hword, sub_self] at ht
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have he := CrossCond.Theta.cfMeanQ_add_eq_retMean_addT S.κ_pos S.θ S.ρL S.ρR S.xL S.xR
      (Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR)
      (sourceCounterExtension_spec S) (rationalTime S.s) p.2 (hsub (hc.inv_mem_dom hz))
    change _ = sourceReferenceMean S (.inr ()) p (((S.marksData F).chart i p).2.1 z) + 0 +
      chiC S.κ * ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
      Aux61GlueK.refMean0 (F.data i) z
    have he' : cfMeanQ S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
        (sourceCounterExtension S) (rationalTime S.s) p.2 (((S.marksData F).chart i p).2.1 z) +
        Impl.forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR (((S.marksData F).chart i p).2.1 z) +
        chiC S.κ * (GlueImg.logDerivPsi (cfW S p) (rationalTime S.s)
          (((S.marksData F).chart i p).2.1 z)).im =
        GlueImg.retMean S.κ (cfU S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
          (rationalTime S.s) (cfStop (rationalTime S.s) p.2))
          (revChart (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 z)) +
        S.θ * chiC S.κ := he
    simp only [sourceReferenceMean, Function.comp_apply]
    linarith only [he']

end InteractingSLE.Sec5.Aux61Cmp
