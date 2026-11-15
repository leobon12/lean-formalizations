/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerDRefl
import InteractingSLE.Spec.Sec5.CfDownRec

/-!
# The first-contact chart of the reflected pair

Packet PROVE-T15-FCKER4. The first-contact chart of `reflPair d` is the conjugate of the chart of `d` by
`σ(z) = −z̄`: on its domain `σ(D)`, forward map `σ ∘ fwd ∘ σ`, inverse `σ ∘ inv ∘ σ` on `ℍ`, lift `−lift ∘ σ`. Hence
the field read in the reflected chart is the reflected field read in the chart (`chartField_reflPair`).

* hulls: `isHPHull_image_reflectC`, **`isMapOut_reflect`** (`σ ∘ g ∘ σ` maps `ℍ ∖ σ(A)` out),
  `mapOut_image_reflectC`, **`isCanonicalDerivLog_reflect`**, `canonDerivLog_image_reflectC`,
  **`hcapSet_image_reflectC`**, `chartClock_reflect`;
* the reflected chart: `reflPair_g`, `reflPair_shift`, `reflPair_fwd`, `reflPair_lift`, `reflPair_inv`,
  `reflPair_chart_rel`;
* `isChartTransport_reflect_of'` (`Sec5.CfDown.IsChartTransport.reflect_of` with the forward map and lift asked only
  on the chart domain), **`chartTransport_reflPair`**, **`chartField_reflPair`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal ComplexConjugate
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb.FCKerD

open LP (reflectC)

section Hull

theorem reflectC_eq_neg_conj (z : ℂ) : reflectC z = -conj z := rfl

theorem reflectC_comp_eq (f : ℂ → ℂ) :
    (fun w => reflectC (f (reflectC w))) = conj ∘ (fun w => -f (-w)) ∘ conj := by
  funext w
  simp only [reflectC_eq_neg_conj, Function.comp_apply, map_neg]

theorem differentiableAt_reflectC_comp {f : ℂ → ℂ} {z : ℂ} (h : DifferentiableAt ℂ f (reflectC z)) :
    DifferentiableAt ℂ (fun w => reflectC (f (reflectC w))) z := by
  rw [reflectC_comp_eq, differentiableAt_conj_conj_iff]
  exact (h.comp (conj z) differentiableAt_id.neg).neg

theorem isHPHull_image_reflectC {A : Set ℂ} (hA : IsHPHull A) : IsHPHull (reflectC '' A) := by
  obtain ⟨hAH, hb, ho, hs⟩ := hA
  refine ⟨Sec7.FlowReflect.image_reflectC_subset_H hAH, LP.isBounded_reflectC_image_iff.2 hb, ?_, ?_⟩
  · rw [LP.H_diff_reflectC_image]
    exact Sec7.FlowReflect.isOpen_image_reflectC ho
  · rw [LP.H_diff_reflectC_image, ← LP.coe_reflectHomeo, Homeomorph.isSimplyConnected_image]
    exact hs

theorem tendsto_reflectC_cobounded_inf {S : Set ℂ} :
    Tendsto reflectC (Bornology.cobounded ℂ ⊓ 𝓟 (reflectC '' S)) (Bornology.cobounded ℂ ⊓ 𝓟 S) := by
  refine Tendsto.inf ?_ (tendsto_principal_principal.2 fun z hz => ?_)
  · rw [← tendsto_norm_atTop_iff_cobounded]
    simp only [LP.norm_reflectC]
    exact tendsto_norm_cobounded_atTop
  · obtain ⟨w, hw, rfl⟩ := hz
    rwa [LP.reflectC_reflectC]

/-- **The mapping-out function of the reflected hull** is the reflected mapping-out function. -/
theorem isMapOut_reflect {A : Set ℂ} {g : ℂ → ℂ} (hA : IsHPHull A) (hg : IsMapOut A g) :
    IsMapOut (reflectC '' A) (fun z => reflectC (g (reflectC z))) := by
  have hmem : ∀ z ∈ H \ reflectC '' A, reflectC z ∈ H \ A := by
    intro z hz
    rw [LP.H_diff_reflectC_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rwa [LP.reflectC_reflectC]
  refine ⟨⟨fun z hz => (differentiableAt_reflectC_comp ((hg.1.1 _ (hmem z hz)).differentiableAt
    (hA.isOpen.mem_nhds (hmem z hz)))).differentiableWithinAt, ?_⟩, ?_⟩
  · have hσ : ∀ S : Set ℂ, BijOn reflectC (reflectC '' S) S := fun S => by
      refine ⟨fun z hz => ?_, LP.reflectC_injective.injOn, fun z hz => ⟨reflectC z, mem_image_of_mem _ hz,
        LP.reflectC_reflectC z⟩⟩
      obtain ⟨w, hw, rfl⟩ := hz
      rwa [LP.reflectC_reflectC]
    have h1 := hσ (H \ A)
    rw [← LP.H_diff_reflectC_image] at h1
    have h2 := hσ H
    rw [Sec7.FlowReflect.reflectC_image_H] at h2
    exact h2.comp (hg.1.2.comp h1)
  · have e : (fun z => reflectC (g (reflectC z)) - z) = reflectC ∘ (fun w => g w - w) ∘ reflectC := by
      funext z
      simp only [Function.comp_apply, LP.reflectC_sub, LP.reflectC_reflectC]
    rw [e]
    have hc : Tendsto reflectC (𝓝 0) (𝓝 0) := by
      have := LP.continuous_reflectC.tendsto 0
      rwa [LP.reflectC_zero] at this
    refine hc.comp (hg.2.comp ?_)
    rw [LP.H_diff_reflectC_image]
    exact tendsto_reflectC_cobounded_inf

theorem mapOut_image_reflectC {A : Set ℂ} (hA : IsHPHull A) :
    EqOn (ConformalImage.mapOut (reflectC '' A)) (fun z => reflectC (ConformalImage.mapOut A (reflectC z)))
      (H \ reflectC '' A) :=
  IsMapOut.eqOn (isHPHull_image_reflectC hA) (ConformalImage.isMapOut_mapOut (isHPHull_image_reflectC hA))
    (isMapOut_reflect hA (ConformalImage.isMapOut_mapOut hA))

/-- **The canonical logarithm of the reflected hull's mapping-out derivative** is the conjugated reflected one. -/
theorem isCanonicalDerivLog_reflect {A : Set ℂ} (hA : IsHPHull A) :
    IsCanonicalDerivLog (reflectC '' A) (ConformalImage.mapOut (reflectC '' A))
      (fun z => conj (canonDerivLog A (reflectC z))) := by
  have hA' := isHPHull_image_reflectC hA
  have hg := ConformalImage.isMapOut_mapOut hA
  have hL := isCanonicalDerivLog_canonDerivLog hA
  have hmem : ∀ z ∈ H \ reflectC '' A, reflectC z ∈ H \ A := by
    intro z hz
    rw [LP.H_diff_reflectC_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rwa [LP.reflectC_reflectC]
  have hderiv : ∀ z ∈ H \ reflectC '' A, deriv (ConformalImage.mapOut (reflectC '' A)) z =
      conj (deriv (ConformalImage.mapOut A) (reflectC z)) := by
    intro z hz
    have hev : ConformalImage.mapOut (reflectC '' A) =ᶠ[𝓝 z]
        fun w => reflectC (ConformalImage.mapOut A (reflectC w)) :=
      Filter.eventually_of_mem (hA'.isOpen.mem_nhds hz) (mapOut_image_reflectC hA)
    rw [hev.deriv_eq, Sec5.CfDown.deriv_reflectC_comp]
  refine ⟨⟨fun z hz => ?_, fun z hz => ?_⟩, ?_⟩
  · have hd : DifferentiableAt ℂ (canonDerivLog A) (reflectC z) :=
      (hL.1.1 _ (hmem z hz)).differentiableAt (hA.isOpen.mem_nhds (hmem z hz))
    have e : (fun z => conj (canonDerivLog A (reflectC z))) =
        conj ∘ (fun w => canonDerivLog A (-w)) ∘ conj := by
      funext w
      simp only [reflectC_eq_neg_conj, Function.comp_apply]
    rw [e]
    refine (differentiableAt_conj_conj_iff.2 ?_).differentiableWithinAt
    exact hd.comp (conj z) differentiableAt_id.neg
  · rw [hderiv z hz, ← hL.1.2 _ (hmem z hz), ← Complex.exp_conj]
  · obtain ⟨R, hR, hAR⟩ := hA.exists_subset_ball
    have hAr : A ⊆ Metric.closedBall 0 R := hAR.trans Metric.ball_subset_closedBall
    refine ⟨8 * R, fun w hw => ?_⟩
    have hw' : 8 * R < (reflectC w).im := by rwa [LP.im_reflectC]
    have hwH : w ∈ H \ reflectC '' A := by
      refine ⟨show 0 < w.im by have := hR; linarith, fun ⟨v, hv, he⟩ => ?_⟩
      have h1 := mem_closedBall_zero_iff.1 (hAr hv)
      have h2 : w.im ≤ R := by
        rw [← he, LP.im_reflectC]
        exact ((le_abs_self _).trans (abs_im_le_norm v)).trans h1
      linarith
    have hq := norm_deriv_sub_one_le_quarter_of_isMapOut hA hg hR hAr hw'
    have hslit := mem_slitPlane_of_norm_sub_one_le (hq.trans (by norm_num))
    simp only
    rw [IsCanonicalDerivLog.eq_log hL hA hg hR hAr hw', hderiv w hwH,
      Complex.log_conj _ (mem_slitPlane_iff_arg.1 hslit).1]

/-- **The lift of the reflected hull** is the opposite reflected lift. -/
theorem canonDerivLog_image_reflectC {A : Set ℂ} (hA : IsHPHull A) {z : ℂ} (hz : z ∈ H \ reflectC '' A) :
    canonDerivLog (reflectC '' A) z = conj (canonDerivLog A (reflectC z)) :=
  IsCanonicalDerivLog.eqOn (isCanonicalDerivLog_canonDerivLog (isHPHull_image_reflectC hA))
    (isCanonicalDerivLog_reflect hA) (isHPHull_image_reflectC hA)
    (ConformalImage.isMapOut_mapOut (isHPHull_image_reflectC hA)) hz

/-- **The half-plane capacity is reflection invariant.** -/
theorem hcapSet_image_reflectC (A : Set ℂ) :
    ConformalImage.hcapSet (reflectC '' A) = ConformalImage.hcapSet A := by
  by_cases hA : IsHPHull A
  · have hA' := isHPHull_image_reflectC hA
    rw [ConformalImage.hcapSet_eq hA', ConformalImage.hcapSet_eq hA]
    have hg := ConformalImage.isMapOut_mapOut hA
    refine HPHull.hcap_eq_of_tendsto ⟨_, hA'⟩ (isMapOut_reflect hA hg) ?_
    have e : (fun z => z * (reflectC (ConformalImage.mapOut A (reflectC z)) - z)) =
        conj ∘ (fun u => u * (ConformalImage.mapOut A u - u)) ∘ reflectC := by
      funext z
      simp only [Function.comp_apply, reflectC_eq_neg_conj, map_mul, map_sub, map_neg, conj_conj]
      ring
    rw [e]
    have h1 := (HPHull.tendsto_hcap ⟨A, hA⟩ hg).comp (tendsto_reflectC_cobounded_inf (S := H \ A))
    rw [← LP.H_diff_reflectC_image] at h1
    have h2 := (Complex.continuous_conj.tendsto _).comp h1
    rwa [Complex.conj_ofReal] at h2
  · have hA' : ¬ IsHPHull (reflectC '' A) := fun h => hA (by
      have := isHPHull_image_reflectC h
      rwa [Sec7.FlowReflect.reflectC_image_image] at this)
    simp only [ConformalImage.hcapSet, hA, hA', dite_false]

/-- **The chart clock is reflection invariant.** -/
theorem chartClock_reflect (Γ : ℝ≥0 → ℂ) (r : ℝ≥0) : chartClock (fun t => reflectC (Γ t)) r = chartClock Γ r := by
  unfold chartClock
  rw [show (fun t => reflectC (Γ t)) '' Icc 0 r = reflectC '' (Γ '' Icc 0 r) from (image_image _ _ _).symm,
    LP.fillH_image_reflectC, hcapSet_image_reflectC]

end Hull

section PairChart

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω} (hd : d.IsMeasGood)
include hd

theorem reflPair_fillK (ω : Ω) : fillH ((reflPair d).K ω) = reflectC '' fillH (d.K ω) := by
  rw [reflPair_K hd, LP.fillH_image_reflectC]

theorem reflPair_g {ω : Ω} {z : ℂ} (hz : z ∈ (reflPair d).D ω) :
    (reflPair d).g ω z = reflectC (d.g ω (reflectC z)) := by
  have hz' : z ∈ H \ reflectC '' fillH (d.K ω) := by rwa [← reflPair_fillK hd]
  change ConformalImage.mapOut (fillH ((reflPair d).K ω)) z = _
  rw [reflPair_fillK hd]
  exact mapOut_image_reflectC (hd.isHPHull ω) hz'

theorem reflPair_shift {ω : Ω} (hω : ω ∈ d.E) : (reflPair d).shift ω = reflectC (d.shift ω) := by
  have hd' := isMeasGood_reflPair hd
  have hD : (reflPair d).D ω = reflectC '' d.D ω := reflPair_D hd ω
  have hp : (reflPair d).p ω = reflectC (d.p ω) := reflPair_p hd hω
  have hσ : Tendsto reflectC (𝓝[(reflPair d).D ω] ((reflPair d).p ω)) (𝓝[d.D ω] (d.p ω)) := by
    have h := (LP.continuous_reflectC.continuousWithinAt (s := (reflPair d).D ω)
      (x := (reflPair d).p ω)).tendsto_nhdsWithin (t := d.D ω) (fun z hz => by
        rw [hD] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        rwa [LP.reflectC_reflectC])
    rw [hp] at h ⊢
    rwa [LP.reflectC_reflectC] at h
  have hlim : Tendsto ((reflPair d).g ω) (𝓝[(reflPair d).D ω] ((reflPair d).p ω))
      (𝓝 (reflectC (d.shift ω))) := by
    have h := (LP.continuous_reflectC.tendsto _).comp ((hd.tendsto_shift ω).comp hσ)
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (reflPair_g hd hz).symm
  have hne : (𝓝[(reflPair d).D ω] ((reflPair d).p ω)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (hd'.p_mem_closure ω)
  exact hlim.limUnder_eq

theorem reflPair_fwd {ω : Ω} (hω : ω ∈ d.E) {z : ℂ} (hz : z ∈ (reflPair d).D ω) :
    (reflPair d).fwd ω z = reflectC (d.fwd ω (reflectC z)) := by
  simp only [PairData.fwd]
  rw [reflPair_g hd hz, reflPair_shift hd hω, LP.reflectC_sub]

theorem reflPair_lift {ω : Ω} {z : ℂ} (hz : z ∈ (reflPair d).D ω) :
    (reflPair d).lift ω z = -d.lift ω (reflectC z) := by
  have hz' : z ∈ H \ reflectC '' fillH (d.K ω) := by rwa [← reflPair_fillK hd]
  simp only [PairData.lift]
  rw [reflPair_fillK hd, canonDerivLog_image_reflectC (hd.isHPHull ω) hz', Complex.conj_im]

theorem reflPair_inv {ω : Ω} (hω : ω ∈ d.E) {w : ℂ} (hw : w ∈ H) :
    (reflPair d).inv ω w = reflectC (d.inv ω (reflectC w)) := by
  have hd' := isMeasGood_reflPair hd
  have hω' : ω ∈ (reflPair d).E := by rwa [E_reflPair]
  obtain ⟨-, hC⟩ := hd.isFirstContactChart hω
  obtain ⟨-, hC'⟩ := hd'.isFirstContactChart hω'
  have hAD : activeDomain ((reflPair d).η₁ ω) ((reflPair d).s₀ ω) ((reflPair d).η₂ ω) ((reflPair d).t₀ ω) =
      reflectC '' activeDomain (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) := by
    rw [reflPair_s₀ hd, reflPair_t₀ hd]
    exact activeDomain_refl _ _
  have hσw : reflectC w ∈ H := LP.reflectC_mem_H_iff.2 hw
  have hv : reflectC (d.inv ω (reflectC w)) ∈
      activeDomain ((reflPair d).η₁ ω) ((reflPair d).s₀ ω) ((reflPair d).η₂ ω) ((reflPair d).t₀ ω) := by
    rw [hAD]
    exact mem_image_of_mem _ (hC.2.1.mapsTo hσw)
  have hvD : reflectC (d.inv ω (reflectC w)) ∈ (reflPair d).D ω := by rwa [hd'.D_of_mem hω']
  refine hC'.1.1.injOn (hC'.2.1.mapsTo hw) hv ?_
  rw [hC'.2.2.1 w hw, reflPair_fwd hd hω hvD, LP.reflectC_reflectC, hC.2.2.1 _ hσw, LP.reflectC_reflectC]

end PairChart

section Transport

open Sec7.FlowReflect (reflTest reflField)

/-- **The chart transport commutes with the reflection**, with the reflected forward map and lift asked only on the
(open) chart domain (`Sec5.CfDown.IsChartTransport.reflect_of` asks them everywhere). -/
theorem isChartTransport_reflect_of' {c c' : Chart} (hO : IsOpen (c'.2.1 '' H))
    (hfwd : ∀ z ∈ c'.2.1 '' H, c'.1 z = reflectC (c.1 (reflectC z)))
    (hinv : ∀ w ∈ H, c'.2.1 w = reflectC (c.2.1 (reflectC w)))
    (hlift : ∀ z ∈ c'.2.1 '' H, c'.2.2 z = -c.2.2 (reflectC z))
    {s a k : ℝ} {f g : DistOn upperHalfPlaneOpens} (hT : IsChartTransport c s a k f g) :
    IsChartTransport c' s (-a) k (reflField f) (reflField g) := by
  have himg := Sec5.CfDown.image_inv_reflect_of hinv
  intro φ φ' hsupp hφ
  have hsupp' : tsupport (reflTest φ) ⊆ c.2.1 '' H := by
    rw [Sec7.FlowReflect.tsupport_reflTest]
    rintro _ ⟨z, hz, rfl⟩
    have h1 := hsupp hz
    rw [himg] at h1
    obtain ⟨v, hv, e⟩ := h1
    rw [← e, LP.reflectC_reflectC]
    exact hv
  have hrel : ∀ z ∈ c.2.1 '' H, reflTest φ z = reflTest φ' (c.1 z) * ‖deriv c.1 z‖ ^ 2 := by
    intro z hz
    have hσz : reflectC z ∈ c'.2.1 '' H := by
      rw [himg]
      exact mem_image_of_mem _ hz
    have hev : c'.1 =ᶠ[𝓝 (reflectC z)] fun w => reflectC (c.1 (reflectC w)) :=
      Filter.eventually_of_mem (hO.mem_nhds hσz) hfwd
    rw [Sec7.FlowReflect.reflTest_apply, Sec7.FlowReflect.reflTest_apply, hφ _ hσz, hev.deriv_eq,
      Sec5.CfDown.norm_deriv_reflectC_comp, hfwd _ hσz, LP.reflectC_reflectC]
  have key := hT (reflTest φ) (reflTest φ') hsupp' hrel
  have hI1 : ∫ w, reflTest φ' w = ∫ w, φ' w := Sec7.FlowReflect.integral_comp_reflectC (fun w => φ' w)
  have hI2 : ∫ w, c'.2.2 (c'.2.1 w) * φ' w = -∫ w, c.2.2 (c.2.1 w) * reflTest φ' w := by
    have e1 : ∫ w, c.2.2 (c.2.1 w) * reflTest φ' w = ∫ w, c.2.2 (c.2.1 (reflectC w)) * φ' w := by
      rw [← Sec7.FlowReflect.integral_comp_reflectC (fun w => c.2.2 (c.2.1 (reflectC w)) * φ' w)]
      congr 1
      funext w
      simp only [LP.reflectC_reflectC, Sec7.FlowReflect.reflTest_apply]
    rw [e1, ← integral_neg]
    congr 1
    funext w
    by_cases hw : w ∈ H
    · rw [hlift _ (mem_image_of_mem _ hw), hinv w hw, LP.reflectC_reflectC, neg_mul]
    · have h0 : φ' w = 0 := φ'.zero_on_compl (show w ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hw)
      rw [h0, mul_zero, mul_zero, neg_zero]
  rw [Sec7.FlowReflect.reflField_apply, Sec7.FlowReflect.reflField_apply, key, hI1, hI2]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω} (hd : d.IsMeasGood)
include hd

/-- **The reflected chart is the conjugate chart**: on its domain, `(σ ∘ fwd ∘ σ, σ ∘ inv ∘ σ, −lift ∘ σ)`. -/
theorem reflPair_chart_rel (ω : Ω) :
    (∀ z ∈ ((reflPair d).chart ω).2.1 '' H, ((reflPair d).chart ω).1 z = reflectC ((d.chart ω).1 (reflectC z))) ∧
    (∀ w ∈ H, ((reflPair d).chart ω).2.1 w = reflectC ((d.chart ω).2.1 (reflectC w))) ∧
    (∀ z ∈ ((reflPair d).chart ω).2.1 '' H, ((reflPair d).chart ω).2.2 z = -(d.chart ω).2.2 (reflectC z)) := by
  have hd' := isMeasGood_reflPair hd
  have hdom : ((reflPair d).chart ω).2.1 '' H = (reflPair d).D ω := by
    rw [← (hd'.isConformal_chart ω).coe_dom, hd'.coe_dom_chart ω]
  rw [hdom]
  by_cases hω : ω ∈ d.E
  · have hω' : ω ∈ (reflPair d).E := by rwa [E_reflPair]
    rw [PairData.chart_of_mem hω', PairData.chart_of_mem hω]
    exact ⟨fun z hz => reflPair_fwd hd hω hz, fun w hw => reflPair_inv hd hω hw,
      fun z hz => reflPair_lift hd hz⟩
  · have hω' : ω ∉ (reflPair d).E := by rwa [E_reflPair]
    rw [PairData.chart_of_notMem hω', PairData.chart_of_notMem hω]
    simp only [Chart.id, LP.reflectC_reflectC, neg_zero, implies_true, and_self]

/-- **The chart transport in the reflected chart is the reflected chart transport** (the additive constant changes
sign). -/
theorem chartTransport_reflPair (ω : Ω) (a k : ℝ) (G : DistOn upperHalfPlaneOpens) :
    Chart.chartTransport ((isMeasGood_reflPair hd).isConformal_chart ω) 1 (-a) k (reflField G) =
      reflField (Chart.chartTransport (hd.isConformal_chart ω) 1 a k G) := by
  have hd' := isMeasGood_reflPair hd
  obtain ⟨hf, hi, hl⟩ := reflPair_chart_rel hd ω
  have hO : IsOpen (((reflPair d).chart ω).2.1 '' H) := by
    rw [← (hd'.isConformal_chart ω).coe_dom]
    exact ((reflPair d).chart ω).dom.isOpen
  have hT := Chart.isChartTransport_chartTransport (hd.isConformal_chart ω)
    (Chart.locallyIntegrableOn_of_continuousOn
      ((hd.isConformal_chart ω).continuousOn_lift_inv (hd.continuousOn_lift_chart ω))) 1 a k G
  have hT' := Chart.isChartTransport_chartTransport (hd'.isConformal_chart ω)
    (Chart.locallyIntegrableOn_of_continuousOn
      ((hd'.isConformal_chart ω).continuousOn_lift_inv (hd'.continuousOn_lift_chart ω))) 1 (-a) k (reflField G)
  exact hT'.unique (hd'.isConformal_chart ω) (isChartTransport_reflect_of' hO hf hi hl hT)

/-- **The chart field of the reflected configuration is the reflected chart field.** -/
theorem chartField_reflPair (κ : ℝ) (h : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) :
    (isMeasGood_reflPair hd).chartField κ (fun ω => reflField (h ω)) ω = reflField (hd.chartField κ h ω) := by
  have e := chartTransport_reflPair hd ω 0 (chiC κ) (h ω)
  rw [neg_zero] at e
  exact e

end Transport

end InteractingSLE.Restart.FCPlumb.FCKerD
