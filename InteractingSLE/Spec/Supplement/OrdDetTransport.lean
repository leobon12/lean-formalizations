/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetAux79
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Spec.Coupling.MartMeans2Chart
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.Spec.Sec6.DrivingArgLift
import InteractingSLE.Spec.Sec7.Lemma78MeanBdry
import InteractingSLE.Spec.Sec7.SideHeightHull
import InteractingSLE.WangWu.UnboundedComponent

/-!
# Aux. lemma 79 at a later line, pathwise: the transported word at alive real points

Packet PROVE-T15-ORDDET (Theorem 1.5's leaf 3, `RLC.RetOrdDetStatement`; specification Aux. lemma 79, pp. 289–290:
"nested comparison with the stop line"). In a retained setting the stop-line chart `c₀` and a later-line chart `cₜ` are
related by the continuation's Loewner map ((III-a): `cₜ⁻¹ = c₀⁻¹ ∘ f_Q⁻¹` on `ℍ`, lifts by the chain rule). Suppose the
two line means `M₀`, `Mₜ` read in their own charts are the word means of sorted words `β₀`, `βₜ`, and that their
difference `Mₜ − M₀` is represented off the later set `A` by a harmonic function `v` (Proposition 3.8 for nested local
sets gives such a `v`, `RetZone.ae_tendsto_zero_of_history`). Then:

* **`eqOn_couplingMean_sub_mean`**: `v ∘ c₀⁻¹ = 𝔥_Q[βₜ] − β₀.mean` on `ℍ \ K_Q`, where
  `𝔥_Q[βₜ] = βₜ.mean ∘ f_Q − χ arg f_Q′` is the coupling mean of the later word (both sides harmonic, with the same
  pairings against every test function supported off the hull: change of variables `integral_mul_pushTest`, the
  chart composition `RetAux79.chartTransport_eq_integral_couplingMean_of_trans`, and harmonic uniqueness
  `Sec6.eqOn_of_integral_mul_eq`);
* **`fn_eq_of_tendsto`**: if moreover `v ∘ c₀⁻¹ → 0` at a real point `x` that is alive at capacity `Q` (a forward
  solution `u` from `x` up to `Q`), then `βₜ(f_Q x) = β₀(x)` whenever `x` and `f_Q x = u(Q)` are not jumps (word means
  tend to their boundary values, `BoundaryWord.tendsto_mean_comp`; `f_Q` is continuous at `x` from `ℍ` with a real
  limit, `tendsto_fwdMap_of_isForwardSol_real`; `arg f_Q′ → 0` there, `tendsto_im_logDerivFwd_of_isForwardSol_real`).

This is the word identity (III-b) on the old part of the boundary, without zone geometry: it applies to every retained
pair, touching or not, and through real contacts of the continuation.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace RLC

namespace OrdDet

open Chart Restart
open SupercriticalConformalCovariance (confPushTest)

/-- **The support of a transported test function** lies in the chart image of the support. -/
theorem tsupport_pushTest_subset_image {c : Chart} (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) :
    tsupport (pushTest hc φ) ⊆ c.2.1 '' tsupport φ := by
  have h := WangWu.tsupport_confPushTest_subset hc.isConformalBijection φ
  change tsupport ⇑(GFF.testIncl c.dom upperHalfPlaneOpens (confPushTest hc.isConformalBijection φ)) ⊆ _
  rwa [GFF.coe_testIncl hc.dom_le]

variable {κ : ℝ} {c₀ cₜ : Chart} {W : ℝ → ℝ} {Q : ℝ}

/-- **The difference of the two line means, read in the stop-line chart, is the coupling mean of the later word minus
the stop-line word mean** on `ℍ \ K_Q` (see the module docstring). -/
theorem eqOn_couplingMean_sub_mean (h₀ : c₀.IsConformal) (hₜ : cₜ.IsConformal)
    (hℓ₀ : ContinuousOn (fun w => c₀.2.2 (c₀.2.1 w)) H) (hW : Continuous W) (hW0 : W 0 = 0) (hQ : 0 ≤ Q)
    (hinv : ∀ w ∈ H, cₜ.2.1 w = c₀.2.1 (fwdMapInv W Q w))
    (hlift : ∀ w ∈ H, cₜ.2.2 (cₜ.2.1 w) =
      (logDerivFwd W Q (fwdMapInv W Q w)).im + c₀.2.2 (c₀.2.1 (fwdMapInv W Q w)))
    {M₀ Mₜ : DistOn upperHalfPlaneOpens} {β₀ βₜ : BoundaryWord} (hs₀ : β₀.IsSorted) (hsₜ : βₜ.IsSorted)
    (hid₀ : ∀ φ : TestOn upperHalfPlaneOpens,
      chartTransport h₀ 1 0 (QuantumZipper.chiC κ) M₀ φ = ∫ w, β₀.mean w * φ w)
    (hidₜ : ∀ φ : TestOn upperHalfPlaneOpens,
      chartTransport hₜ 1 0 (QuantumZipper.chiC κ) Mₜ φ = ∫ w, βₜ.mean w * φ w)
    {A : Set ℂ} (hAo : IsOpen (H \ A)) (hAt : MapsTo c₀.2.1 (H \ fwdHull W Q) (H \ A))
    {v : ℂ → ℝ} (hv : InnerProductSpace.HarmonicOnNhd v (H \ A))
    (hvr : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A → Mₜ φ - M₀ φ = ∫ z, v z * φ z) :
    EqOn (fun w => v (c₀.2.1 w)) (fun w => couplingMean κ W Q βₜ.mean w - β₀.mean w) (H \ fwdHull W Q) := by
  set O := H \ fwdHull W Q with hOdef
  have hOo : IsOpen O := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hQ
  have hOH : O ⊆ H := sdiff_subset
  have hmₜ := (βₜ.isBoundedHarmonicExtension_mean hsₜ).1
  have hm₀ := (β₀.isBoundedHarmonicExtension_mean hs₀).1
  -- harmonicity of both sides
  have hvh : InnerProductSpace.HarmonicOnNhd (fun w => v (c₀.2.1 w)) O :=
    LQGMetric.harmonicOnNhd_comp_holo hAo hOo hv (h₀.1.mono hOH) hAt
  have hch : InnerProductSpace.HarmonicOnNhd (fun w => couplingMean κ W Q βₜ.mean w - β₀.mean w) O :=
    (Sec7.SideHeight.harmonicOnNhd_couplingMean hW hQ hmₜ).sub fun z hz => hm₀ z (hOH hz)
  refine Sec6.eqOn_of_integral_mul_eq hOo hOH hvh hch fun φ hφ => ?_
  -- the pushed test function is supported off `A`
  have hsupp : tsupport (pushTest h₀ φ) ⊆ H \ A :=
    (tsupport_pushTest_subset_image h₀ φ).trans ((image_mono hφ).trans hAt.image_subset)
  have hcont : ∀ f : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd f O → ContinuousOn f O :=
    fun f hf z hz => (hf z hz).1.continuousAt.continuousWithinAt
  have hmc : ContinuousOn βₜ.mean H := fun z hz => (hmₜ z hz).1.continuousAt.continuousWithinAt
  -- the later line in the stop-line chart
  have hT := Restart.RetAux79.chartTransport_eq_integral_couplingMean_of_trans κ h₀ hₜ hℓ₀ hW hW0 hQ hinv hlift
    hmc 0 hidₜ (fun w _ => (add_zero _).symm) φ hφ
  have h0 := hid₀ φ
  rw [chartTransport_apply'] at hT h0
  have hI₁ : Integrable fun z => couplingMean κ W Q βₜ.mean z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (hcont _ (Sec7.SideHeight.harmonicOnNhd_couplingMean hW hQ hmₜ)) φ hφ
  have hI₂ : Integrable fun z => β₀.mean z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn (fun z hz => hcont _ (fun z hz => hm₀ z (hOH hz)) z hz)
      φ hφ
  have e : (fun z => (couplingMean κ W Q βₜ.mean z - β₀.mean z) * φ z) =
      fun z => couplingMean κ W Q βₜ.mean z * φ z - β₀.mean z * φ z := by
    funext z; ring
  rw [e, integral_sub hI₁ hI₂, ← integral_mul_pushTest h₀ φ v, ← hvr _ hsupp]
  linear_combination hT - h0

/-- **The transported word at an alive real point** (see the module docstring). -/
theorem fn_eq_of_tendsto (hW : Continuous W) (hW0 : W 0 = 0) (hQ : 0 ≤ Q) {β₀ βₜ : BoundaryWord}
    (hs₀ : β₀.IsSorted) (hsₜ : βₜ.IsSorted) {v : ℂ → ℝ}
    (heq : EqOn (fun w => v (c₀.2.1 w)) (fun w => couplingMean κ W Q βₜ.mean w - β₀.mean w) (H \ fwdHull W Q))
    {x : ℝ} {u : ℝ → ℂ} (hu : QuantumZipper.IsForwardSol W x Q u) (hx : x ∉ β₀.jumps) (hy : (u Q).re ∉ βₜ.jumps)
    (hdec : Tendsto (fun w => v (c₀.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 0)) :
    βₜ.fn (u Q).re = β₀.fn x := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hQ hu
  have hev : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H \ fwdHull W Q := by
    have hc : Continuous fun z : ℂ => ‖z - x‖ * Real.exp (2 / δ ^ 2 * Q) := by fun_prop
    have h0 : (fun z : ℂ => ‖z - x‖ * Real.exp (2 / δ ^ 2 * Q)) x < δ := by simp [hδ]
    have hball := hc.continuousAt.eventually_lt continuousAt_const h0
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hz hzH
    exact ⟨hzH, not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hzH hz⟩
  have huQ : u Q = ((u Q).re : ℂ) :=
    Complex.ext (by simp) (by simp [im_eq_zero_of_isForwardSol_real hW hu ⟨hQ, le_rfl⟩])
  -- the three limits
  have hf : Tendsto (fwdMap W Q) (𝓝[H] (x : ℂ)) (𝓝[H] ((u Q).re : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hev.mono fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hW hQ hz⟩
    rw [← huQ]
    exact tendsto_fwdMap_of_isForwardSol_real hW hW0 hQ hu
  have h1 := BoundaryWord.tendsto_mean_comp hsₜ hf hy
  have h2 := Sec6.tendsto_im_logDerivFwd_of_isForwardSol_real hW hQ hu
  have h3 := BoundaryWord.tendsto_mean_comp hs₀ (f := id) tendsto_id hx
  have hlim : Tendsto (fun w => couplingMean κ W Q βₜ.mean w - β₀.mean w) (𝓝[H] (x : ℂ))
      (𝓝 (βₜ.fn (u Q).re - QuantumZipper.chiC κ * 0 - β₀.fn x)) :=
    (h1.sub (h2.const_mul _)).sub h3
  have hlim' : Tendsto (fun w => couplingMean κ W Q βₜ.mean w - β₀.mean w) (𝓝[H] (x : ℂ)) (𝓝 0) :=
    hdec.congr' (hev.mono fun z hz => heq hz)
  have hNe : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact show (0 : ℝ) ≤ (x : ℂ).im by simp)
  have := tendsto_nhds_unique hlim hlim'
  linarith
