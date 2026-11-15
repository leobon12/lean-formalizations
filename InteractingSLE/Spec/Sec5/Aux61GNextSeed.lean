/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.FrameQChart
import InteractingSLE.Spec.Sec5.Aux61GContBoundary
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Canonical seed cancellation for finite force words

The singular basic seed term is retained explicitly. Effective force points
away from the seed have a vanishing remainder there, and a positive real
derivative of the coordinate transition cancels the two singular terms.
This proves a limit at the seed itself, not merely limits on its two sides.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61GNext
open Impl (ForceWord)

/-- The canonical seed germ with boundary heights `-π/√κ` and `π/√κ`. -/
def basicSeedMean (κ : ℝ) (z : ℂ) : ℝ :=
  Real.pi / Real.sqrt κ * (-1 + 2 * Impl.jumpExt 0 z)

/-- Nonzero effective force positions leave no residual constant at the
seed. A zero-weight mark may still be located at zero. -/
theorem tendsto_forceExt_sub_basicSeedMean (κ : ℝ) (F : ForceWord)
    (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ)
    (hL : ∀ i, vL i < 0 ∨ F.ρL i = 0) (hR : ∀ j, 0 < vR j ∨ F.ρR j = 0) :
    Tendsto (fun z => Impl.forceExt κ F vL vR z - basicSeedMean κ z)
      (𝓝[H] 0) (𝓝 0) := by
  have hleft : ∀ i, Tendsto (fun z => F.ρL i * (1 - Impl.jumpExt (min 0 (vL i)) z))
      (𝓝[H] 0) (𝓝 0) := by
    intro i
    rcases hL i with hi | hi
    · have ht := Impl.tendsto_jumpExt (b := vL i) (t := 0) hi.ne
      simp only [ite_eq_left hi.le, ofReal_zero] at ht
      have h1 : Tendsto (fun _ : ℂ => (1 : ℝ)) (𝓝[H] 0) (𝓝 1) := tendsto_const_nhds
      simpa only [min_eq_right hi.le, sub_self, mul_zero] using
        (h1.sub ht).const_mul (F.ρL i)
    · simp only [hi, zero_mul]
      exact tendsto_const_nhds
  have hright : ∀ j, Tendsto (fun z => F.ρR j * Impl.jumpExt (max 0 (vR j)) z)
      (𝓝[H] 0) (𝓝 0) := by
    intro j
    rcases hR j with hj | hj
    · have ht := Impl.tendsto_jumpExt (b := vR j) (t := 0) hj.ne'
      simp only [ite_eq_right (not_le.2 hj), ofReal_zero] at ht
      simpa only [max_eq_right hj.le, mul_zero] using ht.const_mul (F.ρR j)
    · simp only [hj, zero_mul]
      exact tendsto_const_nhds
  have ht := ((tendsto_finsetSum Finset.univ (fun i _ => hleft i)).neg.add
    (tendsto_finsetSum Finset.univ (fun j _ => hright j))).const_mul (Real.pi / Real.sqrt κ)
  simp only [Finset.sum_const_zero, neg_zero, add_zero, mul_zero] at ht
  convert ht using 1
  funext z
  dsimp only [Impl.forceExt, basicSeedMean]
  ring

/-- A positive real derivative fixes the singular seed angle without any
integer argument reset. -/
theorem tendsto_arg_sub_of_pos_deriv {G : ℂ → ℂ} {a : ℝ}
    (ha : 0 < a) (hG0 : G 0 = 0) (hderiv : HasDerivAt G (a : ℂ) 0)
    (hGH : ∀ᶠ z in 𝓝[H] 0, G z ∈ H) :
    Tendsto (fun z => arg (G z) - arg z) (𝓝[H] 0) (𝓝 0) := by
  have hfilter : 𝓝[H] (0 : ℂ) ≤ 𝓝[≠] (0 : ℂ) :=
    nhdsWithin_mono _ (fun z hz => DerivLog.ne_zero_of_mem_H hz)
  have hratio : Tendsto (fun z => G z / z) (𝓝[H] 0) (𝓝 (a : ℂ)) := by
    have ht := hderiv.tendsto_slope_zero.mono_left hfilter
    simpa only [zero_add, hG0, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using ht
  have harg := (continuousAt_arg (Or.inl (by simpa only [ofReal_re] using ha))).tendsto.comp hratio
  rw [arg_ofReal_of_nonneg ha.le] at harg
  refine harg.congr' ?_
  filter_upwards [hGH, self_mem_nhdsWithin] with z hGz hz
  exact FrameQ.arg_div_of_mem_H hGz hz

/-- The basic singular seed means cancel under a transition with positive
real derivative at zero. -/
theorem tendsto_basicSeedMean_comp_sub (κ : ℝ) {G : ℂ → ℂ} {a : ℝ}
    (ha : 0 < a) (hG0 : G 0 = 0) (hderiv : HasDerivAt G (a : ℂ) 0)
    (hGH : ∀ᶠ z in 𝓝[H] 0, G z ∈ H) :
    Tendsto (fun z => basicSeedMean κ (G z) - basicSeedMean κ z) (𝓝[H] 0) (𝓝 0) := by
  have ht := (tendsto_arg_sub_of_pos_deriv ha hG0 hderiv hGH).const_mul
    (-(2 * (Real.pi / Real.sqrt κ) / Real.pi))
  simp only [mul_zero] at ht
  convert ht using 1
  funext z
  simp only [basicSeedMean, Impl.jumpExt_eq, ofReal_zero, sub_zero]
  ring

/-- Two canonical force means have the same singular seed germ after a
positive-derivative coordinate transition. Effective marks may differ away
from the seed. -/
theorem tendsto_forceExt_comp_sub_seed (κ : ℝ) (F A : ForceWord)
    (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ)
    (uL : Fin A.nL → ℝ) (uR : Fin A.nR → ℝ)
    (hFL : ∀ i, vL i < 0 ∨ F.ρL i = 0) (hFR : ∀ j, 0 < vR j ∨ F.ρR j = 0)
    (hAL : ∀ i, uL i < 0 ∨ A.ρL i = 0) (hAR : ∀ j, 0 < uR j ∨ A.ρR j = 0)
    {G : ℂ → ℂ} {a : ℝ} (ha : 0 < a) (hG0 : G 0 = 0)
    (hderiv : HasDerivAt G (a : ℂ) 0) (hGH : ∀ᶠ z in 𝓝[H] 0, G z ∈ H) :
    Tendsto (fun z => Impl.forceExt κ F vL vR (G z) - Impl.forceExt κ A uL uR z)
      (𝓝[H] 0) (𝓝 0) := by
  have hGlim : Tendsto G (𝓝[H] 0) (𝓝[H] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa only [hG0] using
      hderiv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, hGH⟩
  have ht := (((tendsto_forceExt_sub_basicSeedMean κ F vL vR hFL hFR).comp hGlim).add
    (tendsto_basicSeedMean_comp_sub κ ha hG0 hderiv hGH)).sub
      (tendsto_forceExt_sub_basicSeedMean κ A uL uR hAL hAR)
  simp only [add_zero, sub_zero] at ht
  convert ht using 1
  funext z
  dsimp only [Function.comp_apply]
  ring

end InteractingSLE.Sec5.Aux61GNext
