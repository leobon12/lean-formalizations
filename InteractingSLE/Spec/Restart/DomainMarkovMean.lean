/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovK2
import InteractingSLE.Spec.Restart.R1Glue

/-!
# K2's input (S) in a chart: the later-line Gaussian kernels read through the retained chart

Packet PROVE-DOMAINMARKOV6. PROVE-DOMAINMARKOV5 proved K2 (`K2.ae_isOptionalHullCoupling_k`) from three `P`-side inputs;
input (S) is `K2.HasSafeLaw`: at every deterministic capacity time `q` of the continuation, on every event of the
continuation filtration inside the avoidance event, the field has the coupling characteristic functional `cfAt_q`
(spec Aux. lemma 79, p. 289: "for every retained bounded continuation stop, its conditional harmonic mean in the current
active component is the canonical finite-force mean associated with this initial piecewise constant datum and the
relative Loewner maps").

In every consumer setting the field `X` is the chart transport `chartTransport c 1 a k h` of the physical field `h`
through a retained chart `c` (fixed by the retained σ-algebra), and the physical side supplies, at every later line,
a marked Gaussian kernel of `h` on the active component `inv(ℍ ∖ K̃_q)` with some mean `M_q` (Aux. lemma 77; S2's
`ae_condExp_exp_eq_ruleStop`). This file proves the generic step from those kernels to (S):

* `zeroGFFTestCov_pushTest_of_subset`: conformal invariance of the zero-boundary covariance on a sub-domain
  `inv(V)` of the chart domain (SupercriticalConformalCovariance's `zeroGFFTestCov_conformal` for `inv|_V`);
* `ae_condExp_cexp_pullField_sub`, `ae_condExp_cexp_chartTransport_sub`: the conditional law of the pulled-back and of
  the transported field, for a test function supported in a random open `V ⊆ ℍ`, on a measurable event, from the
  Gaussian kernel of `h` on `inv(V)`;
* `ae_condExp_cexp_chartTransport_eq_cfAt`: with `V = ℍ ∖ K̃_q` and the mean identification
  `chartTransport c 1 a k M_q = 𝔥_q` (the canonical finite-force mean of the continuation at time `q`), the transported
  field has the coupling characteristic functional `cfAt_q`;
* `hasSafeLaw_of_ae_condExp`: (S) from conditional identities given σ-algebras containing `𝓗_q`;
* **`hasSafeLaw_chartTransport`**: (S) for the transported field from the later-line kernels and the later-line mean
  identification.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov fwdHull)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance (IsConformalBijection confPushTest)
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.DomainMarkov.Mean

open Coupling K2

/-! ### Conformal invariance of the covariance on a sub-domain of a chart -/

section Cov

variable {c : Chart}

/-- The transported field splits as the pulled-back field plus the transport of `0` (offset and lift terms), for
any offset `a` (`Restart.chartTransport_apply_eq_pullField_add` is the case `a = 0`). -/
theorem chartTransport_apply_eq_pullField_add_const (hc : c.IsConformal) (a k : ℝ) (h : DistOn upperHalfPlaneOpens)
    (φ : TestOn upperHalfPlaneOpens) :
    Chart.chartTransport hc 1 a k h φ = Chart.pullField hc h φ + Chart.chartTransport hc 1 a k 0 φ := by
  rw [Chart.chartTransport_apply', Chart.chartTransport_apply', Chart.pullField_apply]
  simp only [one_mul, zero_apply]
  ring

/-- The image of an open subset of `ℍ` under a conformal chart inverse is open. -/
theorem isOpen_image_inv (hc : c.IsConformal) {V : Set ℂ} (hVo : IsOpen V) (hVH : V ⊆ H) :
    IsOpen (c.2.1 '' V) :=
  SmallGammaGeodesics.CC.isOpen_image_conf hVo (hc.1.mono hVH) (hc.injOn.mono hVH)

/-- For a test function supported in `V ⊆ ℍ`, SupercriticalConformalCovariance's push by the restricted inverse
`inv : V → inv(V)` is the chart push `pushTest`. -/
theorem coe_confPushTest_restrict (hc : c.IsConformal) {V U : Opens ℂ} (hVH : (V : Set ℂ) ⊆ H)
    (hU : (U : Set ℂ) = c.2.1 '' V) (hb : IsConformalBijection c.2.1 V U) (ψ : TestOn upperHalfPlaneOpens)
    (hψ : tsupport ψ ⊆ V) :
    ⇑(confPushTest hb (testRestrict ψ hψ)) = ⇑(Chart.pushTest hc ψ) := by
  funext z
  change (U : Set ℂ).indicator (fun y => ‖deriv (Function.invFunOn c.2.1 V) y‖ ^ 2 *
    ψ (Function.invFunOn c.2.1 V y)) z = _
  by_cases hz : z ∈ (U : Set ℂ)
  · rw [indicator_of_mem hz]
    rw [hU] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hdom : c.2.1 w ∈ c.dom := hc.inv_mem_dom (hVH hw)
    rw [Chart.pushTest_apply_of_mem hc ψ hdom]
    have hev : Function.invFunOn c.2.1 V =ᶠ[𝓝 (c.2.1 w)] c.1 := by
      have hUo : IsOpen (c.2.1 '' V) := isOpen_image_inv hc V.isOpen hVH
      refine Filter.eventuallyEq_of_mem (hUo.mem_nhds (mem_image_of_mem _ hw)) ?_
      rintro y ⟨v, hv, rfl⟩
      rw [(hc.injOn.mono hVH).leftInvOn_invFunOn hv, hc.2.2 v (hVH hv)]
    rw [hev.deriv_eq, hev.eq_of_nhds]
  · rw [indicator_of_notMem hz]
    by_cases hd : z ∈ c.dom
    · rw [Chart.pushTest_apply_of_mem hc ψ hd]
      have : ψ (c.1 z) = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun h => hz ?_
        rw [hU]
        exact ⟨c.1 z, hψ h, hc.inv_fwd hd⟩
      rw [this, mul_zero]
    · rw [Chart.pushTest_apply_of_notMem hc ψ hd]

/-- **Conformal invariance of the zero-boundary covariance on a sub-domain of the chart**: for an open `V ⊆ ℍ` and a
test function supported in `V`, `Cov_{inv(V)}(pushTest ψ, pushTest ψ) = Cov_V(ψ, ψ)`. -/
theorem zeroGFFTestCov_pushTest_of_subset (hc : c.IsConformal) {V : Set ℂ} (hVo : IsOpen V) (hVH : V ⊆ H)
    {ψ : TestOn upperHalfPlaneOpens} (hψ : tsupport ψ ⊆ V) :
    zeroGFFTestCov (c.2.1 '' V) (Chart.pushTest hc ψ) (Chart.pushTest hc ψ) = zeroGFFTestCov V ψ ψ := by
  set V' : Opens ℂ := ⟨V, hVo⟩
  set U' : Opens ℂ := ⟨c.2.1 '' V, isOpen_image_inv hc hVo hVH⟩
  have hb : IsConformalBijection c.2.1 (V' : Set ℂ) (U' : Set ℂ) :=
    ⟨hc.1.mono hVH, (hc.injOn.mono hVH).bijOn_image⟩
  have h := SupercriticalConformalCovariance.ZBConformal.zeroGFFTestCov_conformal hb
    (testRestrict (V := V') ψ hψ) (testRestrict (V := V') ψ hψ)
  rw [coe_confPushTest_restrict hc (V := V') (U := U') hVH rfl hb ψ hψ] at h
  exact h

end Cov

/-! ### The chart law on a random sub-domain -/

section Law

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The conditional law of the pulled-back field on a random sub-domain of the chart, on an event.** Suppose that,
given `𝒢`, almost surely on `Mset`, the field `h` paired with every test function supported in the random open set
`inv(V)` (`V ⊆ ℍ` open) is Gaussian with mean `M` and the zero-boundary covariance of `inv(V)`. Then, for a test
function `ψ` supported in `V` on a `𝒢`-event `E` (almost surely inside `Mset`), the pulled-back field `h ∘ inv`
paired with `ψ` is Gaussian given `𝒢` with mean `(M ∘ inv)(ψ)` and the zero-boundary covariance of `V`
(`zeroGFFTestCov_pushTest_of_subset`).
This is `Restart.ae_condExp_cexp_pullField_random_on` with the chart domain replaced by `inv(V)`. -/
theorem ae_condExp_cexp_pullField_sub (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) {V : Ω → Set ℂ} (hVo : ∀ ω, IsOpen (V ω))
    (hVH : ∀ ω, V ω ⊆ H) {Mset : Set Ω}
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset → tsupport φ ⊆ (c ω).2.1 '' V ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' V ω) φ φ : ℝ) : ℂ)))
    (ψ : TestOn upperHalfPlaneOpens) {E : Set Ω} (hE : MeasurableSet[𝒢] E) (hEM : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ Mset)
    (hEV : ∀ ω ∈ E, tsupport ψ ⊆ V ω) :
    ∀ᵐ ω ∂P, ω ∈ E →
      P[fun ω => Complex.exp (Complex.I * (Chart.pullField (hc ω) (h ω) ψ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (Chart.pullField (hc ω) (M ω) ψ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (V ω) ψ ψ : ℝ) : ℂ)) := by
  classical
  set U' : Ω → Set ℂ := fun ω => if ω ∈ E then (c ω).2.1 '' V ω else ∅ with hU'
  set Ψ' : Ω → TestOn upperHalfPlaneOpens → ℂ := fun ω φ => if ω ∈ E then
      Complex.exp (Complex.I * (M ω φ : ℂ) - (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' V ω) φ φ : ℝ) : ℂ))
    else ∫ u, Complex.exp (Complex.I * (u φ : ℂ)) ∂(Measure.dirac (0 : DistOn upperHalfPlaneOpens)) with hΨ'
  set T' : Ω → TestOn upperHalfPlaneOpens := fun ω => if ω ∈ E then Chart.pushTest (hc ω) ψ else 0 with hT'
  have hT'm : ∀ z, Measurable[𝒢] fun ω => T' ω z := fun z => by
    have h1 : Measurable[𝒢] fun ω => Chart.pushTest (hc ω) ψ z :=
      @Chart.measurable_pushTest_apply Ω 𝒢 c hc hdom hfwd ψ z
    have e : (fun ω => T' ω z) = E.piecewise (fun ω => Chart.pushTest (hc ω) ψ z) fun _ => 0 := by
      funext ω
      by_cases hω : ω ∈ E
      · simp only [hT', hω, ↓reduceIte, piecewise_eq_of_mem]
      · rw [piecewise_eq_of_notMem _ _ _ hω]
        simp only [hT', hω, ↓reduceIte]
        rfl
    rw [e]
    exact Measurable.piecewise hE h1 measurable_const
  have hsub : ∀ ω, ω ∈ E → tsupport (Chart.pushTest (hc ω) ψ) ⊆ (c ω).2.1 '' V ω := fun ω hω => by
    intro z hz
    have hzd := Chart.tsupport_pushTest_subset (hc ω) ψ hz
    refine ⟨(c ω).1 z, ?_, (hc ω).inv_fwd hzd⟩
    by_contra hnot
    have hz0 : ∀ᶠ y in 𝓝 z, Chart.pushTest (hc ω) ψ y = 0 := by
      have hcl : IsClosed (tsupport ψ) := isClosed_tsupport _
      have hcont : ContinuousAt (c ω).1 z :=
        ((hc ω).differentiableOn_fwd.differentiableAt ((c ω).dom.isOpen.mem_nhds hzd)).continuousAt
      have hopen : ∀ᶠ y in 𝓝 z, (c ω).1 y ∉ tsupport ψ := hcont.eventually (hcl.isOpen_compl.mem_nhds
        fun h => hnot (hEV ω hω h))
      filter_upwards [hopen, (c ω).dom.isOpen.mem_nhds hzd] with y hy hyd
      rw [Chart.pushTest_apply_of_mem (hc ω) ψ hyd, image_eq_zero_of_notMem_tsupport hy, mul_zero]
    exact (notMem_tsupport_iff_eventuallyEq.2 hz0) hz
  have hT'U : ∀ ω, tsupport (T' ω) ⊆ U' ω := fun ω => by
    by_cases hω : ω ∈ E
    · simp only [hT', hU', hω, ↓reduceIte]
      exact hsub ω hω
    · simp only [hT', hU', hω, ↓reduceIte]
      simp
  have hU'o : ∀ ω, IsOpen (U' ω) := fun ω => by
    by_cases hω : ω ∈ E
    · simp only [hU', hω, ↓reduceIte]; exact isOpen_image_inv (hc ω) (hVo ω) (hVH ω)
    · simp only [hU', hω, ↓reduceIte]; exact isOpen_empty
  have hU'V : ∀ ω, U' ω ⊆ upperHalfPlaneOpens := fun ω => by
    by_cases hω : ω ∈ E
    · simp only [hU', hω, ↓reduceIte]
      rintro _ ⟨w, hw, rfl⟩
      exact (hc ω).2.1 (hVH ω hw)
    · simp only [hU', hω, ↓reduceIte]; exact empty_subset _
  have hΨ'law : ∀ ω, ∃ μ : Measure (DistOn upperHalfPlaneOpens), IsProbabilityMeasure μ ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ U' ω →
        ∫ u, Complex.exp (Complex.I * (u φ : ℂ)) ∂μ = Ψ' ω φ := fun ω => by
    by_cases hω : ω ∈ E
    · set O : Opens ℂ := ⟨(c ω).2.1 '' V ω, isOpen_image_inv (hc ω) (hVo ω) (hVH ω)⟩
      have hOH : (O : Set ℂ) ⊆ H := by
        rintro _ ⟨w, hw, rfl⟩
        exact (hc ω).2.1 (hVH ω hw)
      obtain ⟨μ, hμP, hμ⟩ := RandomTest.exists_gaussExtLaw hOH (M ω)
      refine ⟨μ, hμP, fun φ _ => ?_⟩
      simp only [hΨ', hω, ↓reduceIte]
      exact hμ φ
    · refine ⟨Measure.dirac 0, inferInstance, fun φ _ => ?_⟩
      simp only [hΨ', hω, ↓reduceIte]
  have hcond' : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ U' ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω = Ψ' ω φ := by
    intro φ
    by_cases hφ : φ = 0
    · subst hφ
      have hc1 : P[fun ω => Complex.exp (Complex.I * (h ω 0 : ℂ)) | 𝒢] = fun _ => (1 : ℂ) := by
        simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
        exact condExp_const h𝒢 1
      filter_upwards [hcond 0, hEM] with ω h1 hEMω _
      by_cases hω : ω ∈ E
      · simp only [hΨ', hω, ↓reduceIte]
        exact h1 (hEMω hω) (by
          intro z hz
          exact absurd hz (by simp))
      · simp only [hΨ', hω, ↓reduceIte, hc1]
        rw [integral_dirac' _ _ (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply 0)).stronglyMeasurable]
        simp
    · filter_upwards [hcond φ, hEM] with ω h1 hEMω hsupp
      by_cases hω : ω ∈ E
      · simp only [hU', hω, ↓reduceIte] at hsupp
        simp only [hΨ', hω, ↓reduceIte]
        exact h1 (hEMω hω) hsupp
      · simp only [hU', hω, ↓reduceIte] at hsupp
        exact absurd (eq_zero_of_tsupport_subset_empty hsupp) hφ
  have key := RandomTest.condExp_cexp_apply_ae_eq_of_subset h𝒢 hh hU'o hU'V hΨ'law hcond' hT'm hT'U
  have hTm : Measurable fun ω => h ω (T' ω) :=
    RandomTest.measurable_apply_of_forall_measurable hh fun z => (hT'm z).mono h𝒢 le_rfl
  have hPm : Measurable fun ω => Chart.pullField (hc ω) (h ω) ψ :=
    RandomTest.measurable_apply_of_forall_measurable hh fun z =>
      (@Chart.measurable_pushTest_apply Ω 𝒢 c hc hdom hfwd ψ z).mono h𝒢 le_rfl
  have hloc := ae_condExp_congr_on (𝒦 := 𝒢) (P := P) hE (GFF.integrable_exp_I_mul hTm)
    (GFF.integrable_exp_I_mul hPm) (X := fun ω => Complex.exp (Complex.I * (h ω (T' ω) : ℂ)))
    (Y := fun ω => Complex.exp (Complex.I * (Chart.pullField (hc ω) (h ω) ψ : ℂ)))
    (Eventually.of_forall fun ω hω => by simp only [hT', hω, ↓reduceIte, Chart.pullField_apply])
  filter_upwards [key, hloc] with ω hk hl hω
  rw [← hl hω, hk]
  simp only [hT', hΨ', hω, ↓reduceIte, Chart.pullField_apply,
    zeroGFFTestCov_pushTest_of_subset (hc ω) (hVo ω) (hVH ω) (hEV ω hω)]

/-- **The conditional law of the transported field on a random sub-domain of the chart, on an event**
(`Restart.ae_condExp_cexp_chartTransport_random_on` with the chart domain replaced by `inv(V)`): the lift term is
`𝒢`-measurable and is pulled out of the conditional expectation; the pulled-back part is
`ae_condExp_cexp_pullField_sub`. -/
theorem ae_condExp_cexp_chartTransport_sub (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ) {V : Ω → Set ℂ} (hVo : ∀ ω, IsOpen (V ω)) (hVH : ∀ ω, V ω ⊆ H) {Mset : Set Ω}
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset → tsupport φ ⊆ (c ω).2.1 '' V ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' V ω) φ φ : ℝ) : ℂ)))
    (ψ : TestOn upperHalfPlaneOpens) {E : Set Ω} (hE : MeasurableSet[𝒢] E) (hEM : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ Mset)
    (hEV : ∀ ω ∈ E, tsupport ψ ⊆ V ω) :
    ∀ᵐ ω ∂P, ω ∈ E →
      P[fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k (h ω) ψ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k (M ω) ψ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (V ω) ψ ψ : ℝ) : ℂ)) := by
  set T₀ : Ω → ℝ := fun ω => Chart.chartTransport (hc ω) 1 a k 0 ψ with hT₀
  have hT₀m : Measurable[𝒢] T₀ := by
    have h0 := @Chart.measurable_chartTransport_random' Ω 𝒢 c hc hdom hfwd hliftm hliftc
      (fun _ => (0 : DistOn upperHalfPlaneOpens))
      (measurable_const : Measurable[𝒢] fun _ : Ω => (0 : DistOn upperHalfPlaneOpens)) 1 a k
    exact (LQGMetric.measurable_distOn_apply ψ).comp h0
  have hHm : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) ψ := by
    have h1 := Chart.measurable_chartTransport_random' hc (fun z => h𝒢 _ (hdom z))
      (fun z => (hfwd z).mono h𝒢 le_rfl) (fun z => (hliftm z).mono h𝒢 le_rfl) hliftc hh 1 a k
    exact (LQGMetric.measurable_distOn_apply ψ).comp h1
  set A : Ω → ℝ := fun ω => Chart.pullField (hc ω) (h ω) ψ with hA
  have hsplit : ∀ ω, Chart.chartTransport (hc ω) 1 a k (h ω) ψ = A ω + T₀ ω := fun ω =>
    chartTransport_apply_eq_pullField_add_const (hc ω) a k (h ω) ψ
  have hAm : Measurable A := by
    have : A = fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) ψ - T₀ ω := by
      funext ω; rw [hsplit ω]; ring
    rw [this]; exact hHm.sub (hT₀m.mono h𝒢 le_rfl)
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (T₀ ω : ℂ)) with hf
  set g : Ω → ℂ := fun ω => Complex.exp (Complex.I * (A ω : ℂ)) with hg
  have hfm : StronglyMeasurable[𝒢] f :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hT₀m))).stronglyMeasurable
  have hgm : Measurable g := Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hAm))
  have hgi : Integrable g P :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => (norm_cexp_I_mul_ofReal _).le)
  have hfgi : Integrable (fun ω => ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω)) P := by
    refine Integrable.of_bound ((hfm.mono h𝒢).measurable.mul hgm).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    simp only [ContinuousLinearMap.mul_apply', norm_mul, hf, hg, norm_cexp_I_mul_ofReal, mul_one, le_refl]
  have hpull := condExp_bilin_of_stronglyMeasurable_left (B := ContinuousLinearMap.mul ℝ ℂ) (m := 𝒢) (μ := P)
    hfm hfgi hgi
  have hkey := ae_condExp_cexp_pullField_sub h𝒢 hc hdom hfwd hh hVo hVH hcond ψ hE hEM hEV
  have heq : (fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k (h ω) ψ : ℂ))) =
      fun ω => ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω) := by
    funext ω
    simp only [ContinuousLinearMap.mul_apply', hf, hg, hsplit ω, Complex.ofReal_add, ← Complex.exp_add]
    ring_nf
  rw [heq]
  filter_upwards [hpull, hkey] with ω h1 h2 hω
  have h2' : P[g | 𝒢] ω = Complex.exp (Complex.I * (Chart.pullField (hc ω) (M ω) ψ : ℂ) -
      (((1 / 2 : ℝ) * zeroGFFTestCov (V ω) ψ ψ : ℝ) : ℂ)) := h2 hω
  rw [h1, ContinuousLinearMap.mul_apply', h2', chartTransport_apply_eq_pullField_add_const (hc ω) a k (M ω) ψ, hf,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Law

/-! ### The coupling characteristic functional of the transported field -/

section Safe

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The regularity of the continuation's driver used at a time `q`: continuous before the lifetime and `0` at time
`0`. -/
def IsDrvReg (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0

open Classical in
/-- The continuation's active domain `ℍ ∖ K̃_q` when the driver is regular, `q` is before the lifetime and `ψ` avoids
the hull at `q`; `ℍ` otherwise (an open set containing the support of `ψ` in either case). -/
def activeOr (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ψ : ℂ → ℝ) (q : ℝ≥0) (ω : Ω) : Set ℂ :=
  if IsDrvReg W ζ ω ∧ ω ∈ DomainMarkov.avoidSet W ζ ψ q then H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q else H

omit mΩ in
theorem isOpen_activeOr (ψ : ℂ → ℝ) (q : ℝ≥0) (ω : Ω) : IsOpen (activeOr W ζ ψ q ω) := by
  unfold activeOr
  split_ifs with hω
  · exact MartMeans2.isOpen_H_diff_fwdHull_rpath hω.1.1 hω.2.1
  · exact QuantumZipper.isOpen_H

omit mΩ in
theorem activeOr_subset (ψ : ℂ → ℝ) (q : ℝ≥0) (ω : Ω) : activeOr W ζ ψ q ω ⊆ H := by
  unfold activeOr
  split_ifs
  · exact sdiff_subset
  · exact subset_rfl

omit mΩ in
theorem tsupport_subset_activeOr (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) (ω : Ω) :
    tsupport ψ ⊆ activeOr W ζ ψ q ω := by
  have hH : tsupport ψ ⊆ H := ψ.tsupport_subset
  unfold activeOr
  split_ifs with hω
  · exact subset_sdiff.2 ⟨hH, hω.2.2⟩
  · exact hH

omit mΩ in
theorem activeOr_eq {ψ : ℂ → ℝ} {q : ℝ≥0} {ω : Ω} (hreg : IsDrvReg W ζ ω)
    (hav : ω ∈ DomainMarkov.avoidSet W ζ ψ q) :
    activeOr W ζ ψ q ω = H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q := by
  unfold activeOr
  simp only [hreg, hav, and_self, ↓reduceIte]

/-- **The transported field has the coupling characteristic functional `cfAt_q`** on an event inside the avoidance
event at time `q`, given:

* (Aux. lemma 77) the later-line kernel: given `𝒢`, at `ω ∈ Mset` with `q < ζ`, the physical field paired with test
  functions supported in the chart preimage `inv(ℍ ∖ K̃_q)` of the continuation's active domain is Gaussian with mean
  `M` and the zero-boundary covariance of `inv(ℍ ∖ K̃_q)`;
* (Aux. lemma 79) the later-line mean identification: the chart transport of `M` tested against `ψ` is the canonical
  finite-force mean `𝔥_q` of the continuation (`couplingMean` of the bounded harmonic extension of its current word).

The covariance becomes the Loewner–Green energy of `K̃_q` by conformal invariance on the sub-domain
(`zeroGFFTestCov_pushTest_of_subset`) and `WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov`. -/
theorem ae_condExp_cexp_chartTransport_eq_cfAt (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ) (q : ℝ≥0) {Mset : Set Ω}
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset → (q : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q)) φ φ : ℝ) :
            ℂ)))
    (ψ : TestOn upperHalfPlaneOpens) {E : Set Ω} (hE : MeasurableSet[𝒢] E)
    (hEM : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ Mset ∧ ω ∈ DomainMarkov.avoidSet W ζ ψ q ∧ IsDrvReg W ζ ω)
    (hmean : ∀ᵐ ω ∂P, ω ∈ E → Chart.chartTransport (hc ω) 1 a k (M ω) ψ =
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) q (bheProc κ ρL ρR W VL VR ω q) z * ψ z) :
    ∀ᵐ ω ∂P, ω ∈ E →
      P[fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k (h ω) ψ : ℂ)) | 𝒢] ω =
        cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q) ω := by
  set Mset' : Set Ω := Mset ∩ {ω | IsDrvReg W ζ ω ∧ ω ∈ DomainMarkov.avoidSet W ζ ψ q} with hMset'
  have hcond' : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset' →
      tsupport φ ⊆ (c ω).2.1 '' activeOr W ζ ψ q ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' activeOr W ζ ψ q ω) φ φ : ℝ) : ℂ)) := by
    intro φ
    filter_upwards [hcond φ] with ω hω hωM hsupp
    rw [activeOr_eq hωM.2.1 hωM.2.2] at hsupp ⊢
    exact hω hωM.1 hωM.2.2.1 hsupp
  have hEM' : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ Mset' := by
    filter_upwards [hEM] with ω hω hωE
    exact ⟨(hω hωE).1, (hω hωE).2.2, (hω hωE).2.1⟩
  have hkey := ae_condExp_cexp_chartTransport_sub h𝒢 hc hdom hfwd hliftm hliftc hh a k
    (isOpen_activeOr (W := W) (ζ := ζ) ψ q) (activeOr_subset ψ q) hcond' ψ hE hEM'
    (fun ω _ => tsupport_subset_activeOr ψ q ω)
  filter_upwards [hkey, hEM, hmean] with ω hk hω hm hωE
  obtain ⟨-, hav, hreg⟩ := hω hωE
  rw [hk hωE, activeOr_eq hreg hav, hm hωE, cfAt]
  have hG := WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hreg.1 hreg.2 hav.1 ψ hav.2
  rw [hG]
  congr 1
  push_cast
  ring

/-- **(S) from conditional identities.** If, for every test function `ψ` and time `q`, a σ-algebra `𝓜 ψ q`
between `𝓗_q` and `mΩ` is given such that, almost surely on every event of `𝓗_q` inside `F ∩ avoidSet`, the field
has the coupling characteristic functional `cfAt_q`, then `HasSafeLaw` holds (`setIntegral_condExp` on events of
`𝓗_q ≤ 𝓜`). -/
theorem hasSafeLaw_of_ae_condExp {𝓗 : Filtration ℝ≥0 mΩ} {F : Set Ω} {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X)
    (𝓜 : TestOn upperHalfPlaneOpens → ℝ≥0 → MeasurableSpace Ω) (h𝓗𝓜 : ∀ ψ q, 𝓗 q ≤ 𝓜 ψ q)
    (h𝓜 : ∀ ψ q, 𝓜 ψ q ≤ mΩ)
    (hcond : ∀ (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) (D : Set Ω), MeasurableSet[𝓗 q] D →
      (∀ᵐ ω ∂P, ω ∈ D → ω ∈ F ∧ ω ∈ DomainMarkov.avoidSet W ζ ψ q) →
        ∀ᵐ ω ∂P, ω ∈ D →
          P[fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) | 𝓜 ψ q] ω =
            cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q) ω) :
    HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X := by
  intro ψ q D hD hDa
  have hDm : MeasurableSet D := (𝓗.le q) _ hD
  have hint : Integrable (fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply ψ).comp hX)
  rw [← setIntegral_condExp (h𝓜 ψ q) hint (h𝓗𝓜 ψ q _ hD)]
  exact setIntegral_congr_ae hDm (hcond ψ q D hD hDa)

/-- **K2's input (S) for a field read through a retained chart.** Let the chart `c` be measurable for `𝒢 ≤ 𝓗_0` (the
retained σ-algebra: "Condition on the retained marked common-contact history. This makes `D`, its chart, and the
piecewise constant initial conditional mean fixed", spec p. 294), and let `X = chartTransport c 1 a k h`. Suppose that
at every capacity time `q` of the continuation `(W, VL, VR, ζ)` there is a σ-algebra `𝓜_q ⊇ 𝓗_q` (the later-line
marks) with

* (Aux. lemma 77) the later-line Gaussian kernel of `h` on `inv(ℍ ∖ K̃_q)` with mean `M_q`, almost surely on
  `F ∩ {q < ζ}`;
* (Aux. lemma 79) the later-line mean identification `chartTransport c 1 a k M_q = 𝔥_q` against every test function
  supported off `K̃_q`, almost surely on `F`;
* the driver regular on `F` (continuous before `ζ`, `W_0 = 0`).

Then `HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X`. -/
theorem hasSafeLaw_chartTransport {𝓗 : Filtration ℝ≥0 mΩ} {F : Set Ω} (h𝒢𝓗 : 𝒢 ≤ 𝓗 0) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ) (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓗𝓜 : ∀ q, 𝓗 q ≤ 𝓜 q) (h𝓜 : ∀ q, 𝓜 q ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜 q] ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q)) φ φ : ℝ) :
            ℂ)))
    (hmean : ∀ (q : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      ω ∈ DomainMarkov.avoidSet W ζ ψ q → Chart.chartTransport (hc ω) 1 a k (M q ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) q (bheProc κ ρL ρR W VL VR ω q) z * ψ z)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsDrvReg W ζ ω) :
    HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := by
  have h𝒢𝓜 : ∀ q, 𝒢 ≤ 𝓜 q := fun q => h𝒢𝓗.trans ((𝓗.mono (zero_le (a := q))).trans (h𝓗𝓜 q))
  have h𝒢 : 𝒢 ≤ mΩ := (h𝒢𝓜 0).trans (h𝓜 0)
  have hX : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => h𝒢 _ (hdom z))
      (fun z => (hfwd z).mono h𝒢 le_rfl) (fun z => (hliftm z).mono h𝒢 le_rfl) hliftc hh 1 a k
  refine hasSafeLaw_of_ae_condExp hX (fun _ q => 𝓜 q) (fun _ q => h𝓗𝓜 q) (fun _ q => h𝓜 q) ?_
  intro ψ q D hD hDa
  have hEM : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ F ∧ ω ∈ DomainMarkov.avoidSet W ζ ψ q ∧ IsDrvReg W ζ ω := by
    filter_upwards [hDa, hreg] with ω h1 h2 hωD
    exact ⟨(h1 hωD).1, (h1 hωD).2, h2 (h1 hωD).1⟩
  have hmean' : ∀ᵐ ω ∂P, ω ∈ D → Chart.chartTransport (hc ω) 1 a k (M q ω) ψ =
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) q (bheProc κ ρL ρR W VL VR ω q) z * ψ z := by
    filter_upwards [hDa, hmean q ψ] with ω h1 h2 hωD
    exact h2 (h1 hωD).1 (h1 hωD).2
  exact ae_condExp_cexp_chartTransport_eq_cfAt (𝒢 := 𝓜 q) (h𝓜 q) hc (fun z => h𝒢𝓜 q _ (hdom z))
    (fun z => (hfwd z).mono (h𝒢𝓜 q) le_rfl) (fun z => (hliftm z).mono (h𝒢𝓜 q) le_rfl) hliftc hh a k q
    (hcond q) ψ (h𝓗𝓜 q _ hD) hEM hmean'

end Safe

end InteractingSLE.Restart.DomainMarkov.Mean
