/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GNextSeed
import InteractingSLE.Spec.Sec4.Prob41Flow

/-! # The reference word has the canonical seed germ

Local basic heights imply zero seed weights in the actual flow-line word.
Thus the preceding finite-word seed cancellation applies to `refMean0`.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open QuantumZipper (H chiC)

namespace InteractingSLE.Sec5.Aux61GNext
open PiecewiseConstantBoundaryData
open Aux61Fib (FibData)

/-- The two passive seed marks have weight zero when the one-sided
boundary heights are the canonical flow-line heights. All other marks are
strictly separated from zero by their defining jump enumeration. -/
theorem effective_flowLine_marks_of_seedLimits {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ}
    (hleft : leftLim b 0 = -sleLambda κ) (hright : rightLim b 0 = sleLambda κ) :
    (∀ i, flowLineXL b J 0 i < 0 ∨ flowLineRhoL κ b J 0 0 i = 0) ∧
      (∀ j, 0 < flowLineXR b J 0 j ∨ flowLineRhoR κ b J 0 0 j = 0) := by
  have hLambda : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  constructor
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · right
      change -(leftLim b 0 + 0 * chiC κ) / sleLambda κ - 1 = 0
      simp only [zero_mul, add_zero, hleft, neg_neg,
        div_self hLambda, sub_self]
    · left
      simp only [flowLineXL, sub_zero]
      exact (Finset.mem_filter.1
        (((jumpSet b J).filter (· < 0)).orderEmbOfFin_mem rfl (Fin.rev i))).2
  · intro j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · right
      change (rightLim b 0 + 0 * chiC κ) / sleLambda κ - 1 = 0
      simp only [zero_mul, add_zero, hright, div_self hLambda, sub_self]
    · left
      simp only [flowLineXR, sub_zero]
      exact (Finset.mem_filter.1
        (((jumpSet b J).filter (0 < ·)).orderEmbOfFin_mem rfl j)).2

/-- The reference mean has exactly the canonical singular term at zero. -/
theorem tendsto_refMean0_sub_basicSeedMean (d : FibData)
    (hleft : leftLim d.bR 0 = -sleLambda d.κ)
    (hright : rightLim d.bR 0 = sleLambda d.κ) :
    Tendsto (fun z => Aux61GlueK.refMean0 d z - basicSeedMean d.κ z) (𝓝[H] 0) (𝓝 0) := by
  obtain ⟨hL, hR⟩ := effective_flowLine_marks_of_seedLimits d.κ_pos hleft hright
  simpa only [Aux61GlueK.refMean0, MartChar.meanExt, sub_zero] using
    tendsto_forceExt_sub_basicSeedMean d.κ
      (Ito.weightWord (flowLineRhoL d.κ d.bR d.JR 0 0) (flowLineRhoR d.κ d.bR d.JR 0 0))
      (flowLineXL d.bR d.JR 0) (flowLineXR d.bR d.JR 0) hL hR

/-- Basic heights on an actual open seed patch supply the two one-sided
limits needed by the canonical reference-germ calculation. -/
theorem tendsto_refMean0_sub_basicSeedMean_of_seedPatch (d : FibData)
    {δ : ℝ} (hδ : 0 < δ)
    (hleft : ∀ t ∈ Ioo (-δ) 0, d.bR t = -sleLambda d.κ)
    (hright : ∀ t ∈ Ioo 0 δ, d.bR t = sleLambda d.κ) :
    Tendsto (fun z => Aux61GlueK.refMean0 d z - basicSeedMean d.κ z) (𝓝[H] 0) (𝓝 0) :=
  tendsto_refMean0_sub_basicSeedMean d
    (Sec4.leftLim_eq_of_forall (neg_neg_of_pos hδ) hleft)
    (Sec4.rightLim_eq_of_forall hδ hright)

/-- Canonical own-word data and a zero inherited relative phase agree with
the reference mean at the seed itself. The exact remaining local geometric
input is a positive real derivative of the chart transition. -/
theorem tendsto_charted_forceMean_sub_refMean0_seed (d : FibData) (F : Impl.ForceWord)
    (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ)
    (hL : ∀ i, vL i < 0 ∨ F.ρL i = 0) (hR : ∀ j, 0 < vR j ∨ F.ρR j = 0)
    (hleft : leftLim d.bR 0 = -sleLambda d.κ)
    (hright : rightLim d.bR 0 = sleLambda d.κ)
    {G : ℂ → ℂ} {a : ℝ} (ha : 0 < a) (hG0 : G 0 = 0)
    (htransition_derivative : HasDerivAt G (a : ℂ) 0)
    (hGH : ∀ᶠ z in 𝓝[H] 0, G z ∈ H)
    {L : ℂ → ℝ} (hphase : Tendsto L (𝓝[H] 0) (𝓝 0)) :
    Tendsto (fun z => Impl.forceExt d.κ F vL vR (G z) + chiC d.κ * L z - Aux61GlueK.refMean0 d z)
      (𝓝[H] 0) (𝓝 0) := by
  have hGlim : Tendsto G (𝓝[H] 0) (𝓝[H] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa only [hG0] using
      htransition_derivative.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, hGH⟩
  have ht := ((((tendsto_forceExt_sub_basicSeedMean d.κ F vL vR hL hR).comp hGlim).add
    (tendsto_basicSeedMean_comp_sub d.κ ha hG0 htransition_derivative hGH)).add
      (hphase.const_mul (chiC d.κ))).sub (tendsto_refMean0_sub_basicSeedMean d hleft hright)
  simp only [add_zero, mul_zero, sub_zero] at ht
  convert ht using 1
  funext z
  dsimp only [Function.comp_apply]
  ring

end InteractingSLE.Sec5.Aux61GNext
