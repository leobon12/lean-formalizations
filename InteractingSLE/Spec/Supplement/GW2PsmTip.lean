/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmContact

/-!
# GW2's open lines: interior tips through the launch chart

Packet PROVE-GW2-STAGEMEAN, R121 round (deterministic):

* `mem_H_of_ext_mem_dom`: a boundary point of `ℍ̄` whose boundary-extension image lies in the chart's domain is
  interior;
* **`trace_mem_H_of_tipAt`**: if a tip read through `c.trans infinitySourceChart` lies in `c`'s domain, the trace is
  interior (the premise `γ t₀ ∈ ℍ` of the kernel union mean, from an interior physical counterflow tip off the
  explored hull).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Psm

/-- **A point of `ℍ̄` whose boundary-extension image is in the domain is interior.** -/
theorem mem_H_of_ext_mem_dom {c : Chart} (hc : c.IsConformal) {f : ℂ → ℂ} {p : ℂ} (hp : p ∈ Hbar)
    (hf : Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) (hfp : f p ∈ (c.dom : Set ℂ)) : p ∈ H := by
  have hne : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp
  have hcont : ContinuousAt c.1 (f p) :=
    (hc.differentiableOn_fwd.differentiableAt (c.dom.isOpen.mem_nhds hfp)).continuousAt
  have h1 : Tendsto (fun w => c.1 (c.2.1 w)) (𝓝[H] p) (𝓝 (c.1 (f p))) := hcont.tendsto.comp hf
  have h2 : Tendsto (fun w => c.1 (c.2.1 w)) (𝓝[H] p) (𝓝 p) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_mem_nhdsWithin.mono fun w hw =>
      (hc.2.2 w hw).symm)
  have heq : c.1 (f p) = p := tendsto_nhds_unique h1 h2
  rw [← heq]
  exact hc.fwd_mem hfp

/-- **An interior trace from a tip in the chart's domain.** -/
theorem trace_mem_H_of_tipAt {c : Chart} (hc : c.IsConformal) {f : ℂ → ℂ}
    (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ) {q : ℝ≥0} (hq0 : γ q ≠ 0) {z : ℂ}
    (htip : (c.trans infinitySourceChart).tipAt W q z) (hz : z ∈ (c.dom : Set ℂ)) : γ q ∈ H := by
  have hγbar : γ q ∈ Hbar := by
    have : (𝓝[H] (0 : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℂ) ∈ Hbar by simp [QuantumZipper.Hbar])
    have hWc : Continuous fun s : ℝ => W s.toNNReal := hW.comp continuous_real_toNNReal
    have hW0' : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simp [hW0]
    have hcl : γ q ∈ closure {z : ℂ | 0 < z.im} :=
      mem_closure_of_tendsto (hγ.tendsto_fwdMapInv_tip hW.continuousOn hW0 ENNReal.coe_lt_top)
        (eventually_mem_nhdsWithin.mono fun w hw => QuantumZipper.RS.fwdMapInv_mem_H hWc hW0' q.coe_nonneg hw)
    rw [Complex.closure_setOfPred_lt_im] at hcl
    exact hcl
  have hpbar : -(γ q)⁻¹ ∈ Hbar := by
    show 0 ≤ (-(γ q)⁻¹).im
    have hg : 0 ≤ (γ q).im := hγbar
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_nonneg hg (Complex.normSq_nonneg _)
  have hzf := eq_ext_of_tipAt hf hW hW0 hγ hq0 htip
  rw [hzf] at hz
  have hpH := mem_H_of_ext_mem_dom hc hpbar (hf _ hpbar) hz
  have hp' : 0 < (-(γ q)⁻¹).im := hpH
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg] at hp'
  show 0 < (γ q).im
  by_contra hle
  push Not at hle
  have : (γ q).im / Complex.normSq (γ q) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hle (Complex.normSq_nonneg _)
  linarith

end InteractingSLE.Theorem14.GW2Psm
