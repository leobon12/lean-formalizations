/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Jordan.Transport
import InteractingSLE.GFF.PushforwardLoewner
import InteractingSLE.Spec.Coupling.ResampleFamily

/-!
# Aux. lemma 79 at a later line: the mean identification from the chart composition and the word identity

Packet PROVE-RETAUX79 (specification Aux. lemma 79, pp. 289–290; PROVE-DOMAINMARKOV8's "What remains" §2). In a
retained setting the field is read through the chart `c₀` fixed at the stop line, and the continuation is a curve in
that chart, driven by `W` in its own capacity time. At a later line, read at the capacity time `Q`, three things are
known or to be proved:

* **(III-a) chart composition**: the chart `cₜ` of the later line is `c₀` followed by the centred Loewner chart
  `Chart.id.loewner W Q` (inverse maps and lifts agree on `ℍ`);
* **(the landed later-line identification)**: the chart transport of the line mean `M` in `cₜ` (height shift `0`,
  lift coefficient `χ`) is the function `m` (the word mean of the later line);
* **(III-b) word identity**: the bounded harmonic extension `u` of the continuation's force data is `m + a` on `ℍ`
  (`a = θ₂χ`).

From these, the chart transport of `M` in `c₀` (height shift `a`) is, against test functions supported off the hull
`K̃_Q`, the coupling mean `𝔥_Q = u ∘ f_Q − χ arg f_Q′` of the continuation: this is `hmean` of
`Aux79.hasSafeLaw_of_lineKernel`.

## Main results

* `Chart.exists_pushTest_eq`: every test function supported in a conformal chart's domain is a transported test
  function (the inverse of `pushTest`);
* `Chart.pushTest_congr`: two conformal charts with the same inverse on `ℍ` transport test functions alike;
* **`chartTransport_eq_integral_couplingMean_of_trans`**: the pathwise (III) assembly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open QuantumZipper (H isOpen_H)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance (IsConformalBijection confPushTest)

namespace InteractingSLE

namespace Chart

variable {c c' : Chart}

/-- The forward map of a conformal chart is a conformal bijection of its domain onto `ℍ`. -/
theorem IsConformal.isConformalBijection_fwd (hc : c.IsConformal) :
    IsConformalBijection c.1 (c.dom : Set ℂ) (upperHalfPlaneOpens : Set ℂ) := by
  refine ⟨hc.differentiableOn_fwd, fun z hz => hc.fwd_mem hz, fun z₁ hz₁ z₂ hz₂ he => ?_, fun w hw => ?_⟩
  · rw [← hc.inv_fwd hz₁, ← hc.inv_fwd hz₂, he]
  · exact ⟨c.2.1 w, hc.inv_mem_dom hw, hc.2.2 w hw⟩

/-- On `ℍ`, the inverse function of the forward map chosen by `invFunOn` is the chart inverse. -/
theorem IsConformal.invFunOn_fwd_eq (hc : c.IsConformal) {w : ℂ} (hw : w ∈ H) :
    Function.invFunOn c.1 (c.dom : Set ℂ) w = c.2.1 w := by
  have hex : ∃ z ∈ (c.dom : Set ℂ), c.1 z = w := ⟨c.2.1 w, hc.inv_mem_dom hw, hc.2.2 w hw⟩
  have h1 := Function.invFunOn_mem hex
  have h2 := Function.invFunOn_eq hex
  rw [← hc.inv_fwd h1, h2]

/-- The chain rule for a chart and its inverse: `inv′(fwd z) · fwd′(z) = 1` on the domain. -/
theorem IsConformal.deriv_inv_fwd_mul_deriv_fwd (hc : c.IsConformal) {z : ℂ} (hz : z ∈ c.dom) :
    deriv c.2.1 (c.1 z) * deriv c.1 z = 1 := by
  have hdo : IsOpen (c.dom : Set ℂ) := c.dom.isOpen
  have hd₁ : DifferentiableAt ℂ c.1 z := (hc.differentiableOn_fwd z hz).differentiableAt (hdo.mem_nhds hz)
  have hd₂ : DifferentiableAt ℂ c.2.1 (c.1 z) :=
    (hc.1 _ (hc.fwd_mem hz)).differentiableAt (isOpen_H.mem_nhds (hc.fwd_mem hz))
  have hev : (fun y => c.2.1 (c.1 y)) =ᶠ[𝓝 z] fun y => y :=
    Filter.eventuallyEq_of_mem (hdo.mem_nhds hz) fun y hy => hc.inv_fwd hy
  have h := deriv_comp z hd₂ hd₁
  rw [show (c.2.1 ∘ c.1) = fun y => c.2.1 (c.1 y) from rfl, hev.deriv_eq, deriv_id''] at h
  exact h.symm

/-- **The inverse of the test-function transport**: a test function supported in the domain of a conformal chart is
`pushTest` of the test function `|inv′|² (ψ ∘ inv)` on `ℍ`. -/
theorem exists_pushTest_eq (hc : c.IsConformal) (ψ : TestOn upperHalfPlaneOpens) (hψ : tsupport ψ ⊆ c.dom) :
    ∃ φ : TestOn upperHalfPlaneOpens, pushTest hc φ = ψ := by
  refine ⟨confPushTest hc.isConformalBijection_fwd (Coupling.testRestrict ψ hψ), ?_⟩
  ext z
  by_cases hz : z ∈ c.dom
  · rw [pushTest_apply_of_mem hc _ hz]
    have hw : c.1 z ∈ H := hc.fwd_mem hz
    change ‖deriv c.1 z‖ ^ 2 * (upperHalfPlaneOpens : Set ℂ).indicator (fun y =>
      ‖deriv (Function.invFunOn c.1 (c.dom : Set ℂ)) y‖ ^ 2 *
        ψ (Function.invFunOn c.1 (c.dom : Set ℂ) y)) (c.1 z) = ψ z
    rw [indicator_of_mem (show c.1 z ∈ (upperHalfPlaneOpens : Set ℂ) from hw), hc.invFunOn_fwd_eq hw,
      hc.inv_fwd hz]
    have hev : Function.invFunOn c.1 (c.dom : Set ℂ) =ᶠ[𝓝 (c.1 z)] c.2.1 :=
      Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hw) fun y hy => hc.invFunOn_fwd_eq hy
    rw [hev.deriv_eq]
    have h1 := hc.deriv_inv_fwd_mul_deriv_fwd hz
    have h2 : ‖deriv c.1 z‖ ^ 2 * ‖deriv c.2.1 (c.1 z)‖ ^ 2 = 1 := by
      rw [← mul_pow, ← norm_mul, mul_comm, h1, norm_one, one_pow]
    rw [← mul_assoc, h2, one_mul]
  · rw [pushTest_apply_of_notMem hc _ hz]
    exact (image_eq_zero_of_notMem_tsupport fun h => hz (hψ h)).symm

/-- **Transport congruence**: two conformal charts with the same inverse on `ℍ` transport test functions alike. -/
theorem pushTest_congr (hc : c.IsConformal) (hc' : c'.IsConformal) (he : ∀ w ∈ H, c'.2.1 w = c.2.1 w)
    (φ : TestOn upperHalfPlaneOpens) : pushTest hc' φ = pushTest hc φ := by
  have hdom : (c'.dom : Set ℂ) = c.dom := by
    rw [hc'.coe_dom, hc.coe_dom]
    exact image_congr he
  have hfwd : ∀ z ∈ (c.dom : Set ℂ), c'.1 z = c.1 z := by
    intro z hz
    rw [hc.coe_dom] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [← he w hw, hc'.2.2 w hw, he w hw, hc.2.2 w hw]
  ext z
  by_cases hz : z ∈ c.dom
  · have hz' : z ∈ c'.dom := by
      rw [← SetLike.mem_coe, hdom]; exact hz
    rw [pushTest_apply_of_mem hc' _ hz', pushTest_apply_of_mem hc _ hz, hfwd z hz]
    have hev : c'.1 =ᶠ[𝓝 z] c.1 := Filter.eventuallyEq_of_mem (c.dom.isOpen.mem_nhds hz) hfwd
    rw [hev.deriv_eq]
  · have hz' : z ∉ c'.dom := by
      rw [← SetLike.mem_coe, hdom]; exact hz
    rw [pushTest_apply_of_notMem hc' _ hz', pushTest_apply_of_notMem hc _ hz]

end Chart

namespace Restart.RetAux79

open Chart

/-- **(III) at a later line, pathwise** (PROVE-DOMAINMARKOV8 §2). Let `c₀` be the chart of the stop line (lift
continuous in the coordinate of `ℍ`), `W` the continuation's driver in that chart (continuous, `W 0 = 0`) and `Q ≥ 0`
a capacity time. Suppose

* (III-a) the later-line chart `cₜ` is `c₀` followed by the centred Loewner chart `Chart.id.loewner W Q`: same
  inverse on `ℍ` and the chain-rule lift `arg f_Q′ ∘ f_Q⁻¹ + lift₀ ∘ inv₀ ∘ f_Q⁻¹`;
* the line mean `M` read in `cₜ` (shift `0`, coefficient `χ`) is the function `m`, continuous on `ℍ`;
* (III-b) `u = m + a` on `ℍ`.

Then `M` read in `c₀` with height shift `a` is the coupling mean `𝔥_Q = u ∘ f_Q − χ arg f_Q′` against every test
function supported off the hull `K̃_Q`. -/
theorem chartTransport_eq_integral_couplingMean_of_trans (κ : ℝ) {c₀ cₜ : Chart} (h₀ : c₀.IsConformal)
    (hₜ : cₜ.IsConformal) (hℓ₀ : ContinuousOn (fun w => c₀.2.2 (c₀.2.1 w)) H) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {Q : ℝ} (hQ : 0 ≤ Q)
    (hinv : ∀ w ∈ H, cₜ.2.1 w = c₀.2.1 (QuantumZipper.fwdMapInv W Q w))
    (hlift : ∀ w ∈ H, cₜ.2.2 (cₜ.2.1 w) =
      (QuantumZipper.logDerivFwd W Q (QuantumZipper.fwdMapInv W Q w)).im +
        c₀.2.2 (c₀.2.1 (QuantumZipper.fwdMapInv W Q w)))
    {M : DistOn upperHalfPlaneOpens} {m u : ℂ → ℝ} (hm : ContinuousOn m H) (a : ℝ)
    (hid : ∀ φ : TestOn upperHalfPlaneOpens,
      chartTransport hₜ 1 0 (QuantumZipper.chiC κ) M φ = ∫ w, m w * φ w)
    (hu : ∀ w ∈ H, u w = m w + a) (ψ : TestOn upperHalfPlaneOpens)
    (hψ : tsupport ψ ⊆ H \ QuantumZipper.fwdHull W Q) :
    chartTransport h₀ 1 a (QuantumZipper.chiC κ) M ψ = ∫ z, couplingMean κ W Q u z * ψ z := by
  set χ := QuantumZipper.chiC κ with hχ
  set L := Chart.id.loewner W Q with hLdef
  have hL : L.IsConformal := isConformal_id.loewner hW hW0 hQ
  have hLdom : (L.dom : Set ℂ) = H \ QuantumZipper.fwdHull W Q := by
    rw [hL.coe_dom]; exact QuantumZipper.RS.image_fwdMapInv_H hW hW0 hQ
  obtain ⟨φ, hφ⟩ := exists_pushTest_eq hL ψ (by rw [hLdom]; exact hψ)
  have hpush : pushTest hₜ φ = pushTest h₀ ψ := by
    rw [pushTest_congr (h₀.trans hL) hₜ (fun w hw => hinv w hw) φ, pushTest_trans h₀ hL φ, hφ]
  -- the three functions on `ℍ`
  set Lg : ℂ → ℝ := fun w => L.2.2 (L.2.1 w) with hLg
  set ℓ' : ℂ → ℝ := fun w => c₀.2.2 (c₀.2.1 (L.2.1 w)) with hℓ'
  have hLgc : ContinuousOn Lg H := isConformal_id.continuousOn_loewner_lift continuousOn_id_lift hW hW0 hQ
  have hℓ'c : ContinuousOn ℓ' H := hℓ₀.comp hL.1.continuousOn hL.2.1
  have hGe : EqOn (fun w => cₜ.2.2 (cₜ.2.1 w)) (fun w => Lg w + ℓ' w) H := fun w hw => by
    show cₜ.2.2 (cₜ.2.1 w) = (QuantumZipper.logDerivFwd W Q (QuantumZipper.fwdMapInv W Q w)).im + 0 +
      c₀.2.2 (c₀.2.1 (QuantumZipper.fwdMapInv W Q w))
    rw [hlift w hw, add_zero]
  have hGc : ContinuousOn (fun w => cₜ.2.2 (cₜ.2.1 w)) H := (hLgc.add hℓ'c).congr hGe
  -- the line identification, expanded
  have h1 := hid φ
  rw [chartTransport_apply hₜ (locallyIntegrableOn_of_continuousOn hGc), hpush] at h1
  rw [chartTransport_apply h₀ (locallyIntegrableOn_of_continuousOn hℓ₀)]
  -- integrals against `ψ` are integrals against `φ`
  have hψφ : ∀ f : ℂ → ℝ, ∫ z, f z * ψ z = ∫ w, f (L.2.1 w) * φ w := fun f => by
    rw [← hφ, integral_mul_pushTest hL φ f]
  have hD : ∫ z, ψ z = ∫ w, φ w := by rw [← hφ, integral_pushTest hL φ]
  have hIφ : Integrable fun w => φ w := by
    simpa only [one_mul] using integrable_mul_testOn_of_continuousOn (f := fun _ => (1 : ℝ)) continuousOn_const φ
  have hIm := integrable_mul_testOn_of_continuousOn hm φ
  have hILg := integrable_mul_testOn_of_continuousOn hLgc φ
  have hIℓ := integrable_mul_testOn_of_continuousOn hℓ'c φ
  have hG : ∫ w, cₜ.2.2 (cₜ.2.1 w) * φ w = (∫ w, Lg w * φ w) + ∫ w, ℓ' w * φ w := by
    rw [← integral_add hILg hIℓ]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    by_cases hw : w ∈ H
    · simp only [hGe hw, add_mul]
    · simp only [testOn_eq_zero_of_notMem_H φ hw, mul_zero, add_zero]
  have hcm : ∫ z, couplingMean κ W Q u z * ψ z =
      (∫ w, m w * φ w) + a * (∫ w, φ w) - χ * ∫ w, Lg w * φ w := by
    have he : ∫ w, couplingMean κ W Q u (L.2.1 w) * φ w =
        ∫ w, (m w * φ w + a * φ w - χ * (Lg w * φ w)) := by
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      by_cases hw : w ∈ H
      · have e1 : QuantumZipper.fwdMap W Q (QuantumZipper.fwdMapInv W Q w) = w :=
          QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hQ hw
        change (u (QuantumZipper.fwdMap W Q (QuantumZipper.fwdMapInv W Q w)) -
          χ * (QuantumZipper.logDerivFwd W Q (QuantumZipper.fwdMapInv W Q w)).im) * φ w =
          m w * φ w + a * φ w -
            χ * (((QuantumZipper.logDerivFwd W Q (QuantumZipper.fwdMapInv W Q w)).im + 0) * φ w)
        rw [e1, hu w hw]
        ring
      · simp only [testOn_eq_zero_of_notMem_H φ hw, mul_zero, sub_zero, add_zero]
    have hIs : Integrable fun w => m w * φ w + a * φ w := hIm.add (hIφ.const_mul a)
    have hIc : Integrable fun w => χ * (Lg w * φ w) := hILg.const_mul χ
    have hIa : Integrable fun w => a * φ w := hIφ.const_mul a
    rw [hψφ, he, integral_sub hIs hIc, integral_add hIm hIa, integral_const_mul, integral_const_mul]
  rw [hcm, hD, hψφ (fun z => c₀.2.2 (c₀.2.1 z))]
  rw [hG] at h1
  change 1 * M (pushTest h₀ ψ) + 0 * (∫ w, φ w) + χ * ((∫ w, Lg w * φ w) + ∫ w, ℓ' w * φ w) =
    ∫ w, m w * φ w at h1
  change 1 * M (pushTest h₀ ψ) + a * (∫ w, φ w) + χ * ∫ w, ℓ' w * φ w = _
  linear_combination h1

end Restart.RetAux79

end InteractingSLE
