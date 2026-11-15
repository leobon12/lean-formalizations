/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Jordan.Chart
import InteractingSLE.Spec.Coupling.MartMeans2Chart

/-!
# The field read in composed and changed charts

Packet PROVE-JORDANCPL. The frozen relation `IsChartTransport c σ a k h h'` (`h' = (σ h + a) ∘ inv + k lift ∘ inv`,
Specification p. 2, (1.4)) is compatible with the chain-rule lift of composed charts (Specification p. 2: "for
compositions use the analytic chain-rule lift inherited from these choices"), and the field read in a chart of a
domain `D` with two marked prime ends depends on the chart only through a dilation and one constant `2πnk`.

## Main results

* `Chart.pushTest_trans`: the transported test function of a composed chart is the composite transport;
* **`IsChartTransport.trans`**: reading `h` in `c₁` and then the result in `c₂` (coefficient `k`, no new offset)
  is reading `h` in `c₁.trans c₂`;
* `IsChartTransport.of_trans`: conversely, the field read in `c₁.trans c₂` is the field read in `c₁`, read in `c₂`;
* **`IsDomainChartAt.isChartTransport_dilation`** (chart independence of the field): if `c, c'` are charts of `D`
  taking the same prime ends to `0, ∞`, with `fwd' = r fwd` and `lift' = lift + 2πn`, then the fields read in them
  satisfy `h₂ = h₁ ∘ (· / r) + 2πn k`, i.e. `IsChartTransport (Chart.dilation r) 1 (2πnk) k h₁ h₂`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H isOpen_H)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Chart

variable {c₁ c₂ : Chart}

/-- Membership in the domain of a composed chart. -/
theorem IsConformal.mem_dom_trans_iff (h₁ : c₁.IsConformal) (h₂ : c₂.IsConformal) {z : ℂ} :
    z ∈ (c₁.trans c₂).dom ↔ z ∈ c₁.dom ∧ c₁.1 z ∈ c₂.dom := by
  rw [(h₁.trans h₂).mem_dom_iff, h₁.mem_dom_iff, h₂.mem_dom_iff]
  constructor
  · rintro ⟨hw, hz⟩
    -- `z = inv₁ (inv₂ w)` with `w = fwd₂ (fwd₁ z) ∈ ℍ`
    have hv : c₂.2.1 (c₂.1 (c₁.1 z)) ∈ H := h₂.2.1 hw
    have hfz : c₁.1 z = c₂.2.1 (c₂.1 (c₁.1 z)) := by
      conv_lhs => rw [← hz]
      exact h₁.2.2 _ hv
    refine ⟨⟨hfz ▸ hv, ?_⟩, ?_, hfz.symm⟩
    · conv_lhs => rw [hfz]
      exact hz
    · exact hw
  · rintro ⟨⟨_, hz₁⟩, hw, hz₂⟩
    refine ⟨hw, ?_⟩
    change c₁.2.1 (c₂.2.1 (c₂.1 (c₁.1 z))) = z
    rw [hz₂, hz₁]

/-- **The transported test function of a composed chart** is the composite transport
(`|(fwd₂ ∘ fwd₁)′|² = |fwd₂′ ∘ fwd₁|² |fwd₁′|²`). -/
theorem pushTest_trans (h₁ : c₁.IsConformal) (h₂ : c₂.IsConformal) (φ : TestOn upperHalfPlaneOpens) :
    pushTest (h₁.trans h₂) φ = pushTest h₁ (pushTest h₂ φ) := by
  ext z
  by_cases hz : z ∈ (c₁.trans c₂).dom
  · obtain ⟨hz₁, hz₂⟩ := (h₁.mem_dom_trans_iff h₂).1 hz
    rw [pushTest_apply_of_mem _ φ hz, pushTest_apply_of_mem h₁ _ hz₁, pushTest_apply_of_mem h₂ φ hz₂]
    have hd₁ : DifferentiableAt ℂ c₁.1 z :=
      h₁.differentiableOn_fwd.differentiableAt (c₁.dom.isOpen.mem_nhds hz₁)
    have hd₂ : DifferentiableAt ℂ c₂.1 (c₁.1 z) :=
      h₂.differentiableOn_fwd.differentiableAt (c₂.dom.isOpen.mem_nhds hz₂)
    have hder : deriv (c₁.trans c₂).1 z = deriv c₂.1 (c₁.1 z) * deriv c₁.1 z :=
      deriv_comp (h₂ := c₂.1) (h := c₁.1) z hd₂ hd₁
    rw [hder, norm_mul, mul_pow]
    change ‖deriv c₂.1 (c₁.1 z)‖ ^ 2 * ‖deriv c₁.1 z‖ ^ 2 * φ (c₂.1 (c₁.1 z)) =
      ‖deriv c₁.1 z‖ ^ 2 * (‖deriv c₂.1 (c₁.1 z)‖ ^ 2 * φ (c₂.1 (c₁.1 z)))
    ring
  · rw [pushTest_apply_of_notMem _ φ hz]
    by_cases hz₁ : z ∈ c₁.dom
    · have hz₂ : c₁.1 z ∉ c₂.dom := fun hz₂ => hz ((h₁.mem_dom_trans_iff h₂).2 ⟨hz₁, hz₂⟩)
      rw [pushTest_apply_of_mem h₁ _ hz₁, pushTest_apply_of_notMem h₂ φ hz₂, mul_zero]
    · rw [pushTest_apply_of_notMem h₁ _ hz₁]

/-- `∫ pushTest φ = ∫ φ` (change of variables with `u = 1`). -/
theorem integral_pushTest {c : Chart} (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) :
    ∫ z, pushTest hc φ z = ∫ w, φ w := by
  have h := integral_mul_pushTest hc φ fun _ => 1
  simp only [one_mul] at h
  exact h

end Chart

/-- A function continuous on `ℍ`, times a test function on `ℍ`, is integrable. -/
theorem integrable_mul_testOn_of_continuousOn {f : ℂ → ℝ} (hf : ContinuousOn f H)
    (φ : TestOn upperHalfPlaneOpens) : Integrable (fun z => f z * φ z) :=
  Coupling.MartMeans2.integrable_mul_test_of_continuousOn hf φ φ.tsupport_subset

theorem testOn_eq_zero_of_notMem_H (φ : TestOn upperHalfPlaneOpens) {w : ℂ} (hw : w ∉ H) : φ w = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hw (φ.tsupport_subset h)

namespace IsChartTransport

variable {c₁ c₂ : Chart} {σ a k : ℝ} {h h₁ h₂ : DistOn upperHalfPlaneOpens}

/-- The lift of a composed chart, in the coordinate of `ℍ`, is the sum of the two lifts read in `ℍ`. -/
theorem trans_lift_inv (hc₁ : c₁.IsConformal) {w : ℂ} (hw : c₂.2.1 w ∈ H) :
    (c₁.trans c₂).2.2 ((c₁.trans c₂).2.1 w) = c₂.2.2 (c₂.2.1 w) + c₁.2.2 (c₁.2.1 (c₂.2.1 w)) := by
  change c₂.2.2 (c₁.1 (c₁.2.1 (c₂.2.1 w))) + c₁.2.2 (c₁.2.1 (c₂.2.1 w)) = _
  rw [hc₁.2.2 _ hw]

/-- The lift integral of a composed chart splits (both lifts continuous in the coordinate of `ℍ`). -/
theorem integral_trans_lift (hc₁ : c₁.IsConformal) (hc₂ : c₂.IsConformal)
    (hℓ₁ : ContinuousOn (fun w => c₁.2.2 (c₁.2.1 w)) H) (hℓ₂ : ContinuousOn (fun w => c₂.2.2 (c₂.2.1 w)) H)
    (φ : TestOn upperHalfPlaneOpens) :
    ∫ w, (c₁.trans c₂).2.2 ((c₁.trans c₂).2.1 w) * φ w =
      (∫ w, c₁.2.2 (c₁.2.1 (c₂.2.1 w)) * φ w) + ∫ w, c₂.2.2 (c₂.2.1 w) * φ w := by
  have hc : ContinuousOn (fun w => c₁.2.2 (c₁.2.1 (c₂.2.1 w))) H :=
    hℓ₁.comp hc₂.1.continuousOn hc₂.2.1
  rw [← integral_add (integrable_mul_testOn_of_continuousOn hc φ)
    (integrable_mul_testOn_of_continuousOn hℓ₂ φ)]
  congr 1
  funext w
  by_cases hw : w ∈ H
  · rw [trans_lift_inv hc₁ (hc₂.2.1 hw)]
    ring
  · rw [testOn_eq_zero_of_notMem_H φ hw]
    ring

/-- **Composition of chart transports**: the field `h` read in `c₁` (`σ, a, k`) and then in `c₂` (coefficient `k`,
no new sign or offset) is `h` read in `c₁.trans c₂` with the chain-rule lift. -/
theorem trans (hc₁ : c₁.IsConformal) (hc₂ : c₂.IsConformal)
    (hℓ₁ : ContinuousOn (fun w => c₁.2.2 (c₁.2.1 w)) H) (hℓ₂ : ContinuousOn (fun w => c₂.2.2 (c₂.2.1 w)) H)
    (ht₁ : IsChartTransport c₁ σ a k h h₁) (ht₂ : IsChartTransport c₂ 1 0 k h₁ h₂) :
    IsChartTransport (c₁.trans c₂) σ a k h h₂ := by
  intro φ φ' hsupp hφ
  rw [Chart.eq_pushTest (hc₁.trans hc₂) hsupp hφ, Chart.pushTest_trans hc₁ hc₂,
    ht₂.apply_eq hc₂ φ', ht₁.apply_eq hc₁ (Chart.pushTest hc₂ φ'), Chart.integral_pushTest hc₂,
    Chart.integral_mul_pushTest hc₂ φ' (fun z => c₁.2.2 (c₁.2.1 z)),
    integral_trans_lift hc₁ hc₂ hℓ₁ hℓ₂ φ']
  ring

/-- **The converse**: the field read in `c₁.trans c₂` is the field read in `c₁`, read in `c₂`. -/
theorem of_trans (hc₁ : c₁.IsConformal) (hc₂ : c₂.IsConformal)
    (hℓ₁ : ContinuousOn (fun w => c₁.2.2 (c₁.2.1 w)) H) (hℓ₂ : ContinuousOn (fun w => c₂.2.2 (c₂.2.1 w)) H)
    (ht₁ : IsChartTransport c₁ σ a k h h₁) (ht : IsChartTransport (c₁.trans c₂) σ a k h h₂) :
    IsChartTransport c₂ 1 0 k h₁ h₂ := by
  have hℓ₂' := Chart.locallyIntegrableOn_of_continuousOn hℓ₂
  have h₂' := Chart.isChartTransport_chartTransport hc₂ hℓ₂' 1 0 k h₁
  have := (trans hc₁ hc₂ hℓ₁ hℓ₂ ht₁ h₂').unique (hc₁.trans hc₂) ht
  rw [← this]
  exact h₂'

end IsChartTransport

/-! ### Chart independence of the field read in a normalized chart -/

namespace IsDomainChartAt

variable {D : Set ℂ} {a b : PrimeEnd D} {c c' : Chart} {σ a₀ k : ℝ} {h h₁ h₂ : DistOn upperHalfPlaneOpens}

/-- **Chart independence of the field.** Let `c, c'` be charts of `D` taking the same prime ends to `0, ∞`, so that
`fwd' = r fwd` on `D` and `lift' = lift + 2πn` (`exists_dilation`). Then the fields read in them are related by
the dilation and the constant `2πnk`: `h₂ = h₁ ∘ (· / r) + 2πn k`. -/
theorem isChartTransport_dilation (hc : IsDomainChartAt D a b c) (hc' : IsDomainChartAt D a b c') {r : ℝ}
    (hr : 0 < r) (hfwd : EqOn c'.1 (fun z => (r : ℂ) * c.1 z) D) {n : ℤ}
    (hlift : EqOn c'.2.2 (fun z => c.2.2 z + 2 * Real.pi * n) D)
    (ht₁ : IsChartTransport c σ a₀ k h h₁) (ht₂ : IsChartTransport c' σ a₀ k h h₂) :
    IsChartTransport (Chart.dilation r) 1 (2 * Real.pi * n * k) k h₁ h₂ := by
  obtain ⟨hD, -, -⟩ := hc
  obtain ⟨hD', -, -⟩ := hc'
  have hdc := Chart.isConformal_dilation hr
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  -- the inverse of `c'` is `inv ∘ (· / r)` on `ℍ`
  have hinv : ∀ w ∈ H, c'.2.1 w = c.2.1 (w / r) := fun w hw => by
    have hm : c'.2.1 w ∈ D := hD'.inv_mem hw
    have h1 : (r : ℂ) * c.1 (c'.2.1 w) = w := by
      have := hfwd hm
      simp only at this
      rw [← this, hD'.fwd_inv hw]
    have h2 : c.1 (c'.2.1 w) = w / r := by
      rw [eq_div_iff hr0, mul_comm]
      exact h1
    rw [← h2, hD.inv_fwd hm]
  -- the transported test functions agree
  have hpush : ∀ φ : TestOn upperHalfPlaneOpens,
      Chart.pushTest hD'.isConformal φ = Chart.pushTest hD.isConformal (Chart.pushTest hdc φ) := by
    intro φ
    rw [← Chart.pushTest_trans hD.isConformal hdc]
    ext z
    have hdom : z ∈ c'.dom ↔ z ∈ (c.trans (Chart.dilation r)).dom := by
      rw [← SetLike.mem_coe, hD'.coe_dom, ← SetLike.mem_coe,
        (hD.isConformal.trans hdc).coe_dom, Chart.trans_image, Chart.dilation_image_H hr, hD.image_eq]
    by_cases hz : z ∈ c'.dom
    · have hzD : z ∈ D := by rw [← SetLike.mem_coe, hD'.coe_dom] at hz; exact hz
      rw [Chart.pushTest_apply_of_mem _ φ hz, Chart.pushTest_apply_of_mem _ φ (hdom.1 hz)]
      have hev : c'.1 =ᶠ[𝓝 z] (c.trans (Chart.dilation r)).1 :=
        Filter.eventuallyEq_of_mem (hD.isOpen.mem_nhds hzD) fun y hy => hfwd hy
      rw [hev.deriv_eq, hfwd hzD]
      rfl
    · rw [Chart.pushTest_apply_of_notMem _ φ hz,
        Chart.pushTest_apply_of_notMem _ φ (fun h => hz (hdom.2 h))]
  -- the lift integrals
  have hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H := hD.continuousOn_lift_inv
  have hℓr : ContinuousOn (fun w => c.2.2 (c.2.1 (w / r))) H :=
    hℓ.comp (continuous_id.div_const _).continuousOn fun w hw => Chart.div_mem_H hr hw
  have hlift_int : ∀ φ : TestOn upperHalfPlaneOpens, ∫ w, c'.2.2 (c'.2.1 w) * φ w =
      (∫ w, c.2.2 (c.2.1 (w / r)) * φ w) + 2 * Real.pi * n * ∫ w, φ w := by
    intro φ
    rw [← integral_const_mul, ← integral_add (integrable_mul_testOn_of_continuousOn hℓr φ)
      ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).const_mul _)]
    congr 1
    funext w
    by_cases hw : w ∈ H
    · rw [hlift (hD'.inv_mem hw), hinv w hw]
      ring
    · rw [testOn_eq_zero_of_notMem_H φ hw]
      ring
  intro φ φ' hsupp hφ
  rw [Chart.eq_pushTest hdc hsupp hφ, ht₂.apply_eq hD'.isConformal φ', hpush φ',
    ht₁.apply_eq hD.isConformal (Chart.pushTest hdc φ'), Chart.integral_pushTest hdc,
    Chart.integral_mul_pushTest hdc φ' (fun z => c.2.2 (c.2.1 z)), hlift_int φ']
  change _ = 1 * (σ * h (Chart.pushTest hD.isConformal (Chart.pushTest hdc φ')) + a₀ * (∫ w, φ' w) +
      k * ∫ w, c.2.2 (c.2.1 (w / r)) * φ' w) + 2 * Real.pi * n * k * (∫ w, φ' w) +
      k * ∫ w, (0 : ℝ) * φ' w
  simp only [zero_mul, integral_zero]
  ring

end IsDomainChartAt

end InteractingSLE
