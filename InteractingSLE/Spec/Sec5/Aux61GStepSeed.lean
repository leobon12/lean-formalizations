/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GStepReflect
import InteractingSLE.Spec.Sec5.Aux61GNextRefSeed

/-! # Singular seed comparison through the reflected inverse access

The actual own coordinate need only be an inverse on the upper half-plane.
Its arbitrary values below the real line need no differentiability assumption.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology
open QuantumZipper (H chiC)

namespace InteractingSLE.Sec5.Aux61GStep
open Aux61TwoS Aux61GNext
open Aux61Fib (FibData)

/-- The singular basic seed terms cancel through the upper-half-plane
inverse of a positive reflected transition. -/
theorem tendsto_basicSeedMean_inverse_sub (κ : ℝ) {Ξ G Θ : ℂ → ℂ} {ε : ℝ}
    (hG : IsPosReflect Ξ G 0 ε) (hG0 : G 0 = 0)
    (hleft : ∀ w ∈ H ∩ ball ((0 : ℝ) : ℂ) ε, Θ (Ξ w) = w)
    (hright : ∀ z ∈ H, Ξ (Θ z) = z) :
    Tendsto (fun z => basicSeedMean κ (Θ z) - basicSeedMean κ z) (𝓝[H] 0) (𝓝 0) := by
  have hΘ : Tendsto Θ (𝓝[H] 0) (𝓝[H] 0) := by
    have ht := hG.tendsto_leftInv hleft
    simpa only [hG0, ofReal_zero] using ht
  have h0ball : (0 : ℂ) ∈ ball ((0 : ℝ) : ℂ) ε := mem_ball_self hG.pos
  obtain ⟨him, hpos⟩ := hG.deriv_pos h0ball
  have hder : HasDerivAt G (((deriv G 0).re : ℝ) : ℂ) 0 := by
    have he : deriv G 0 = (((deriv G 0).re : ℝ) : ℂ) :=
      Complex.ext rfl (by simp only [ofReal_im]; exact him)
    rw [← he]
    exact (hG.diff.differentiableAt (isOpen_ball.mem_nhds h0ball)).hasDerivAt
  have hGH : ∀ᶠ z in 𝓝[H] 0, G z ∈ H := by
    have hev : ∀ᶠ z in 𝓝[H] 0, z ∈ H ∩ ball ((0 : ℝ) : ℂ) ε :=
      inter_mem_nhdsWithin H (ball_mem_nhds _ hG.pos)
    exact hev.mono fun z hz => hG.conf.2.2.2.1 hz
  have ht := ((tendsto_basicSeedMean_comp_sub κ hpos hG0 hder hGH).neg).comp hΘ
  simp only [neg_zero] at ht
  refine ht.congr' ?_
  have hnear : ∀ᶠ z in 𝓝[H] 0, Θ z ∈ H ∩ ball ((0 : ℝ) : ℂ) ε :=
    hΘ.eventually (inter_mem_nhdsWithin H (ball_mem_nhds _ hG.pos))
  filter_upwards [hnear, self_mem_nhdsWithin] with z hz hzH
  dsimp only [Function.comp_apply]
  rw [hG.eqOn hz, hright z hzH]
  ring

/-- Canonical own marks, the reflected transition and the inherited zero
relative phase prove the entire seed reference comparison. -/
theorem tendsto_forceMean_inverse_sub_reference_seed (d : FibData) (F : Impl.ForceWord)
    (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ)
    (hL : ∀ i, vL i < 0 ∨ F.ρL i = 0) (hR : ∀ j, 0 < vR j ∨ F.ρR j = 0)
    (hleft_height : PiecewiseConstantBoundaryData.leftLim d.bR 0 = -sleLambda d.κ)
    (hright_height : PiecewiseConstantBoundaryData.rightLim d.bR 0 = sleLambda d.κ)
    {Ξ G Θ : ℂ → ℂ} {ε : ℝ} (hG : IsPosReflect Ξ G 0 ε) (hG0 : G 0 = 0)
    (hleft : ∀ w ∈ H ∩ ball ((0 : ℝ) : ℂ) ε, Θ (Ξ w) = w)
    (hright : ∀ z ∈ H, Ξ (Θ z) = z)
    {L : ℂ → ℝ} (hphase : Tendsto L (𝓝[H] 0) (𝓝 0)) :
    Tendsto (fun z => Impl.forceExt d.κ F vL vR (Θ z) + chiC d.κ * L z - Aux61GlueK.refMean0 d z)
      (𝓝[H] 0) (𝓝 0) := by
  have hΘ : Tendsto Θ (𝓝[H] 0) (𝓝[H] 0) := by
    have ht := hG.tendsto_leftInv hleft
    simpa only [hG0, ofReal_zero] using ht
  have ht := ((((tendsto_forceExt_sub_basicSeedMean d.κ F vL vR hL hR).comp hΘ).add
    (tendsto_basicSeedMean_inverse_sub d.κ hG hG0 hleft hright)).add
      (hphase.const_mul (chiC d.κ))).sub
        (tendsto_refMean0_sub_basicSeedMean d hleft_height hright_height)
  simp only [add_zero, mul_zero, sub_zero] at ht
  convert ht using 1
  funext z
  dsimp only [Function.comp_apply]
  ring

end InteractingSLE.Sec5.Aux61GStep
