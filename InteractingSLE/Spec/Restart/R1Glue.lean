/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Lemma78Chart
import InteractingSLE.GFF.LocalSets.GermApprox
import InteractingSLE.Spec.Sec6.Prop61Mean

/-!
# (R1) gluing: conditional expectations on events, and the chart law on an event

Packet PROVE-RESTART-CPL7, (R1) of `FirstContactKernelClockStatement` (Lemma 7.8, p. 290). PROVE-RESTART-CPL6 proved
the marked law off the first-contact union for the two flow lines capped at a deterministic time `m`, with the
σ-algebra `𝒦_m` of the germs and the capped retained histories. Lemma 7.7's proof covers the finite common-contact
realizations "by countably many bounded grid boxes" (p. 288); here are the measure-theoretic tools that glue the
per-box conditional laws into one conditional law, given one σ-algebra `𝒢`, on the union of the boxes:

* `ae_condExp_eq_of_trace`: conditioning on a larger σ-algebra `𝒦'` changes nothing on an event `A` on which every
  `𝒦'`-set is, up to a null set, a `𝒦`-set;
* `ae_condExp_congr_on`: conditional expectations only see the integrand on an event of the σ-algebra;
* the chart law of CPL4 (`Lemma78Chart.lean`) **on an event** (`ae_condExp_cexp_pullField_random_on`,
  `ae_condExp_cexp_chartTransport_eq_gaussCF_on`, `ae_condExp_cexp_chartField_eq_gaussCF_on`): the marked law of the
  field on the chart domain is needed only on the meeting branch.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE

namespace Restart

section Trace

variable {Ω : Type*} {𝒢 𝒦 𝒦' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Enlarging the σ-algebra by information already present on an event.** If `𝒦 ≤ 𝒦'` and, on the measurable event
`A`, every `𝒦'`-set agrees up to a null set with a `𝒦`-set (`B ∩ A ∈ aeSigma 𝒦 P`), then `E[X | 𝒦'] = E[X | 𝒦]` almost
surely on `A`. -/
theorem ae_condExp_eq_of_trace (h𝒦𝒦' : 𝒦 ≤ 𝒦') (h𝒦' : 𝒦' ≤ mΩ) {A : Set Ω}
    (htr : ∀ B, MeasurableSet[𝒦'] B → MeasurableSet[LocalSets.aeSigma 𝒦 P] (B ∩ A))
    {X : Ω → ℂ} (hX : Integrable X P) :
    ∀ᵐ ω ∂P, ω ∈ A → P[X | 𝒦'] ω = P[X | 𝒦] ω := by
  have h𝒦 : 𝒦 ≤ mΩ := h𝒦𝒦'.trans h𝒦'
  obtain ⟨A', hA'm, hAA'⟩ : ∃ A', MeasurableSet[𝒦] A' ∧ A =ᵐ[P] A' := by
    have := htr univ MeasurableSet.univ
    rwa [univ_inter] at this
  have hA'm' : MeasurableSet[𝒦'] A' := h𝒦𝒦' _ hA'm
  have hkey : A'.indicator (P[X | 𝒦]) =ᵐ[P] A'.indicator (P[X | 𝒦']) := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' h𝒦' (fun s _ _ => ?_) (fun s _ _ => ?_) ?_ ?_ ?_
    · exact (integrable_condExp.indicator (h𝒦 _ hA'm)).integrableOn
    · exact (integrable_condExp.indicator (h𝒦' _ hA'm')).integrableOn
    · intro s hs _
      rw [setIntegral_indicator (h𝒦 _ hA'm), setIntegral_indicator (h𝒦' _ hA'm')]
      obtain ⟨C, hCm, hsC⟩ : ∃ C, MeasurableSet[𝒦] C ∧ s ∩ A =ᵐ[P] C := htr s hs
      have hsC' : s ∩ A' =ᵐ[P] C := (EventuallyEqSet.rfl.inter hAA'.symm).trans hsC
      rw [setIntegral_congr_set hsC', setIntegral_condExp h𝒦 hX hCm, ← setIntegral_congr_set hsC',
        setIntegral_condExp h𝒦' hX (hs.inter hA'm')]
    · exact ((stronglyMeasurable_condExp.mono h𝒦𝒦').indicator hA'm').aestronglyMeasurable
    · exact (stronglyMeasurable_condExp.indicator hA'm').aestronglyMeasurable
  filter_upwards [hkey, hAA'] with ω hω hωAA' hωA
  have hωA' : ω ∈ A' := Eq.mp hωAA' hωA
  rw [indicator_of_mem hωA', indicator_of_mem hωA'] at hω
  exact hω.symm

omit [IsProbabilityMeasure P] in
/-- **Conditional expectations only see the integrand on an event of the σ-algebra.** -/
theorem ae_condExp_congr_on {A : Set Ω} (hA : MeasurableSet[𝒦] A) {X Y : Ω → ℂ} (hX : Integrable X P)
    (hY : Integrable Y P) (hXY : ∀ᵐ ω ∂P, ω ∈ A → X ω = Y ω) :
    ∀ᵐ ω ∂P, ω ∈ A → P[X | 𝒦] ω = P[Y | 𝒦] ω := by
  have h3 : A.indicator X =ᵐ[P] A.indicator Y := by
    filter_upwards [hXY] with ω hω
    by_cases h : ω ∈ A
    · rw [indicator_of_mem h, indicator_of_mem h, hω h]
    · rw [indicator_of_notMem h, indicator_of_notMem h]
  filter_upwards [condExp_indicator hX hA, condExp_indicator hY hA, condExp_congr_ae (m := 𝒦) h3]
    with ω e1 e2 e3 hω
  have := e1.symm.trans (e3.trans e2)
  rwa [indicator_of_mem hω, indicator_of_mem hω] at this

/-- **Tower property on an event, for a smaller σ-algebra**: if `𝒢 ≤ 𝒦`, `A ∈ 𝒢`, and `E[X | 𝒦] = Y` almost surely
on `A` for a `𝒢`-measurable bounded `Y`, then `E[X | 𝒢] = Y` almost surely on `A`. -/
theorem ae_condExp_eq_on_of_le (h𝒢𝒦 : 𝒢 ≤ 𝒦) (h𝒦 : 𝒦 ≤ mΩ) {X Y : Ω → ℂ}
    (hX : Integrable X P) (hY : StronglyMeasurable[𝒢] Y) (hYb : ∀ ω, ‖Y ω‖ ≤ 1) {A : Set Ω}
    (hA : MeasurableSet[𝒢] A) (hXY : ∀ᵐ ω ∂P, ω ∈ A → P[X | 𝒦] ω = Y ω) :
    ∀ᵐ ω ∂P, ω ∈ A → P[X | 𝒢] ω = Y ω :=
  Sec6.condExp_ae_eq_on_of_le h𝒢𝒦 h𝒦 hX hY
    (Integrable.of_bound ((hY.mono (h𝒢𝒦.trans h𝒦)).aestronglyMeasurable) 1 (Eventually.of_forall hYb)) hA hXY

end Trace

/-! ### The chart law on an event -/

/-- A test function supported in the empty set is zero. -/
theorem eq_zero_of_tsupport_subset_empty {φ : TestOn upperHalfPlaneOpens} (h : tsupport φ ⊆ ∅) : φ = 0 := by
  ext z
  exact image_eq_zero_of_notMem_tsupport fun hz => h hz

section CondOn

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The conditional law of the pulled-back field, on an event.** `Chart.condExp_cexp_pullField_random_of_subset`
when the conditional law of `h` on the chart domain is known only on a `𝒢`-event `Mset`. -/
theorem ae_condExp_cexp_pullField_random_on (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) {Mset : Set Ω} (hM : MeasurableSet[𝒢] Mset)
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset → tsupport φ ⊆ (c ω).dom →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).dom : Set ℂ) φ φ : ℝ) : ℂ)))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ Mset →
      P[fun ω => Complex.exp (Complex.I * (Chart.pullField (hc ω) (h ω) φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (Chart.pullField (hc ω) (M ω) φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov H φ φ : ℝ) : ℂ)) := by
  classical
  set U' : Ω → Set ℂ := fun ω => if ω ∈ Mset then ((c ω).dom : Set ℂ) else ∅ with hU'
  set Ψ' : Ω → TestOn upperHalfPlaneOpens → ℂ := fun ω ψ => if ω ∈ Mset then
      Complex.exp (Complex.I * (M ω ψ : ℂ) - (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).dom : Set ℂ) ψ ψ : ℝ) : ℂ))
    else ∫ u, Complex.exp (Complex.I * (u ψ : ℂ)) ∂(Measure.dirac (0 : DistOn upperHalfPlaneOpens)) with hΨ'
  set T' : Ω → TestOn upperHalfPlaneOpens := fun ω => if ω ∈ Mset then Chart.pushTest (hc ω) φ else 0 with hT'
  have hT'm : ∀ z, Measurable[𝒢] fun ω => T' ω z := fun z => by
    have h1 : Measurable[𝒢] fun ω => Chart.pushTest (hc ω) φ z :=
      @Chart.measurable_pushTest_apply Ω 𝒢 c hc hdom hfwd φ z
    have e : (fun ω => T' ω z) = Mset.piecewise (fun ω => Chart.pushTest (hc ω) φ z) fun _ => 0 := by
      funext ω
      by_cases hω : ω ∈ Mset
      · simp only [hT', hω, ↓reduceIte, piecewise_eq_of_mem]
      · rw [piecewise_eq_of_notMem _ _ _ hω]
        simp only [hT', hω, ↓reduceIte]
        rfl
    rw [e]
    exact Measurable.piecewise hM h1 measurable_const
  have hT'U : ∀ ω, tsupport (T' ω) ⊆ U' ω := fun ω => by
    by_cases hω : ω ∈ Mset
    · simp only [hT', hU', hω, ↓reduceIte]
      exact Chart.tsupport_pushTest_subset (hc ω) φ
    · simp only [hT', hU', hω, ↓reduceIte]
      simp
  have hU'o : ∀ ω, IsOpen (U' ω) := fun ω => by
    by_cases hω : ω ∈ Mset
    · simp only [hU', hω, ↓reduceIte]; exact (c ω).dom.isOpen
    · simp only [hU', hω, ↓reduceIte]; exact isOpen_empty
  have hU'V : ∀ ω, U' ω ⊆ upperHalfPlaneOpens := fun ω => by
    by_cases hω : ω ∈ Mset
    · simp only [hU', hω, ↓reduceIte]; exact (hc ω).dom_subset
    · simp only [hU', hω, ↓reduceIte]; exact empty_subset _
  have hΨ'law : ∀ ω, ∃ μ : Measure (DistOn upperHalfPlaneOpens), IsProbabilityMeasure μ ∧
      ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U' ω →
        ∫ u, Complex.exp (Complex.I * (u ψ : ℂ)) ∂μ = Ψ' ω ψ := fun ω => by
    by_cases hω : ω ∈ Mset
    · obtain ⟨μ, hμP, hμ⟩ := RandomTest.exists_gaussExtLaw (hc ω).dom_subset (M ω)
      refine ⟨μ, hμP, fun ψ _ => ?_⟩
      simp only [hΨ', hω, ↓reduceIte]
      exact hμ ψ
    · refine ⟨Measure.dirac 0, inferInstance, fun ψ _ => ?_⟩
      simp only [hΨ', hω, ↓reduceIte]
  have hcond' : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport ψ ⊆ U' ω →
      P[fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ)) | 𝒢] ω = Ψ' ω ψ := by
    intro ψ
    by_cases hψ : ψ = 0
    · subst hψ
      have hc1 : P[fun ω => Complex.exp (Complex.I * (h ω 0 : ℂ)) | 𝒢] = fun _ => (1 : ℂ) := by
        simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
        exact condExp_const h𝒢 1
      filter_upwards [hcond 0] with ω h1 _
      by_cases hω : ω ∈ Mset
      · simp only [hΨ', hω, ↓reduceIte]
        exact h1 hω (by
          intro z hz
          exact absurd hz (by simp))
      · simp only [hΨ', hω, ↓reduceIte, hc1]
        rw [integral_dirac' _ _ (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply 0)).stronglyMeasurable]
        simp
    · filter_upwards [hcond ψ] with ω h1 hsupp
      by_cases hω : ω ∈ Mset
      · simp only [hU', hω, ↓reduceIte] at hsupp
        simp only [hΨ', hω, ↓reduceIte]
        exact h1 hω hsupp
      · simp only [hU', hω, ↓reduceIte] at hsupp
        exact absurd (eq_zero_of_tsupport_subset_empty hsupp) hψ
  have key := RandomTest.condExp_cexp_apply_ae_eq_of_subset h𝒢 hh hU'o hU'V hΨ'law hcond' hT'm hT'U
  have hTm : Measurable fun ω => h ω (T' ω) :=
    RandomTest.measurable_apply_of_forall_measurable hh fun z => (hT'm z).mono h𝒢 le_rfl
  have hPm : Measurable fun ω => Chart.pullField (hc ω) (h ω) φ := by
    have h1 : Measurable fun ω => h ω (Chart.pushTest (hc ω) φ) :=
      RandomTest.measurable_apply_of_forall_measurable hh fun z =>
        (@Chart.measurable_pushTest_apply Ω 𝒢 c hc hdom hfwd φ z).mono h𝒢 le_rfl
    exact h1
  have hloc := ae_condExp_congr_on (𝒦 := 𝒢) (P := P) hM (GFF.integrable_exp_I_mul hTm)
    (GFF.integrable_exp_I_mul hPm) (X := fun ω => Complex.exp (Complex.I * (h ω (T' ω) : ℂ)))
    (Y := fun ω => Complex.exp (Complex.I * (Chart.pullField (hc ω) (h ω) φ : ℂ)))
    (Eventually.of_forall fun ω hω => by simp only [hT', hω, ↓reduceIte, Chart.pullField_apply])
  filter_upwards [key, hloc] with ω hk hl hω
  rw [← hl hω, hk]
  simp only [hT', hΨ', hω, ↓reduceIte, Chart.pullField_apply, Chart.zeroGFFTestCov_pushTest (hc ω) φ φ]

/-- **The conditional law of the chart field, on an event** (`condExp_cexp_chartTransport_random_of_subset` when the
conditional law of `h` on the chart domain is known only on the `𝒢`-event `Mset`). -/
theorem ae_condExp_cexp_chartTransport_random_on (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (k : ℝ) {Mset : Set Ω} (hM : MeasurableSet[𝒢] Mset)
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset → tsupport φ ⊆ (c ω).dom →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).dom : Set ℂ) φ φ : ℝ) : ℂ)))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ Mset →
      P[fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 0 k (h ω) φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 0 k (M ω) φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov H φ φ : ℝ) : ℂ)) := by
  -- the lift term is `𝒢`-measurable
  set T₀ : Ω → ℝ := fun ω => Chart.chartTransport (hc ω) 1 0 k 0 φ with hT₀
  have hT₀m : Measurable[𝒢] T₀ := by
    have h0 := @Chart.measurable_chartTransport_random' Ω 𝒢 c hc hdom hfwd hliftm hliftc
      (fun _ => (0 : DistOn upperHalfPlaneOpens))
      (measurable_const : Measurable[𝒢] fun _ : Ω => (0 : DistOn upperHalfPlaneOpens)) 1 0 k
    exact (LQGMetric.measurable_distOn_apply φ).comp h0
  -- the full chart field is measurable
  have hHm : Measurable fun ω => Chart.chartTransport (hc ω) 1 0 k (h ω) φ := by
    have h1 := Chart.measurable_chartTransport_random' hc (fun z => h𝒢 _ (hdom z))
      (fun z => (hfwd z).mono h𝒢 le_rfl) (fun z => (hliftm z).mono h𝒢 le_rfl) hliftc hh 1 0 k
    exact (LQGMetric.measurable_distOn_apply φ).comp h1
  set A : Ω → ℝ := fun ω => Chart.pullField (hc ω) (h ω) φ with hA
  have hsplit : ∀ ω, Chart.chartTransport (hc ω) 1 0 k (h ω) φ = A ω + T₀ ω := fun ω =>
    chartTransport_apply_eq_pullField_add (hc ω) k (h ω) φ
  have hAm : Measurable A := by
    have : A = fun ω => Chart.chartTransport (hc ω) 1 0 k (h ω) φ - T₀ ω := by
      funext ω; rw [hsplit ω]; ring
    rw [this]; exact hHm.sub (hT₀m.mono h𝒢 le_rfl)
  -- the integrands
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
  have hkey := ae_condExp_cexp_pullField_random_on h𝒢 hc hdom hfwd hh hM hcond φ
  have heq : (fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 0 k (h ω) φ : ℂ))) =
      fun ω => ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω) := by
    funext ω
    simp only [ContinuousLinearMap.mul_apply', hf, hg, hsplit ω, Complex.ofReal_add, ← Complex.exp_add]
    ring_nf
  rw [heq]
  filter_upwards [hpull, hkey] with ω h1 h2 hω
  have h2' : P[g | 𝒢] ω = Complex.exp (Complex.I * (Chart.pullField (hc ω) (M ω) φ : ℂ) -
      (((1 / 2 : ℝ) * zeroGFFTestCov H φ φ : ℝ) : ℂ)) := h2 hω
  rw [h1, ContinuousLinearMap.mul_apply', h2', chartTransport_apply_eq_pullField_add (hc ω) k (M ω) φ, hf,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **(R1) on an event**: `ae_condExp_cexp_chartTransport_eq_gaussCF` with the marked law off the union known only on
the `𝒢`-event `Mset`. -/
theorem ae_condExp_cexp_chartTransport_eq_gaussCF_on (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (k : ℝ) {Mset : Set Ω} (hM : MeasurableSet[𝒢] Mset)
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset → tsupport φ ⊆ (c ω).dom →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).dom : Set ℂ) φ φ : ℝ) : ℂ)))
    {β : Ω → BoundaryWord}
    (hmean : ∀ᵐ ω ∂P, ω ∈ Mset → ∀ φ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport (hc ω) 1 0 k (M ω) φ = ∫ z, (β ω).mean z * φ z)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ Mset →
      P[fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hc ω') 1 0 k (h ω') φ : ℂ)) | 𝒢] ω =
        gaussCF (β ω) φ := by
  filter_upwards [ae_condExp_cexp_chartTransport_random_on h𝒢 hc hdom hfwd hliftm hliftc hh k hM hcond φ,
    hmean] with ω h1 h2 hω
  rw [h1 hω, h2 hω φ, gaussCF]
  have hH : (upperHalfPlaneOpens : Set ℂ) = H := rfl
  rw [hH]
  congr 1
  push_cast
  ring

/-- **(R1) on an event for the canonical chart field** of `𝒢`-measurable pair data. -/
theorem ae_condExp_cexp_chartField_eq_gaussCF_on (h𝒢 : 𝒢 ≤ mΩ) {d : PairData Ω}
    (hd : @PairData.IsMeasGood Ω 𝒢 d) (κ : ℝ) {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {Mset : Set Ω} (hM : MeasurableSet[𝒢] Mset)
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset → tsupport φ ⊆ d.D ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) - (((1 / 2 : ℝ) * zeroGFFTestCov (d.D ω) φ φ : ℝ) : ℂ)))
    {β : Ω → BoundaryWord}
    (hmean : ∀ᵐ ω ∂P, ω ∈ Mset → ∀ φ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport (@PairData.IsMeasGood.isConformal_chart Ω 𝒢 d hd ω) 1 0 (QuantumZipper.chiC κ) (M ω) φ =
        ∫ z, (β ω).mean z * φ z)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ Mset →
      P[fun ω' => Complex.exp (Complex.I * (@PairData.IsMeasGood.chartField Ω 𝒢 d hd κ h ω' φ : ℂ)) | 𝒢] ω =
        gaussCF (β ω) φ := by
  obtain ⟨hdom, hfwd, hliftm⟩ := @PairData.IsMeasGood.chart_measurability Ω 𝒢 d hd
  have hcond' : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Mset → tsupport φ ⊆ (d.chart ω).dom →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((d.chart ω).dom : Set ℂ) φ φ : ℝ) : ℂ)) := by
    intro φ
    filter_upwards [hcond φ] with ω hω hωM hsupp
    rw [@PairData.IsMeasGood.coe_dom_chart Ω 𝒢 d hd ω] at hsupp ⊢
    exact hω hωM hsupp
  exact ae_condExp_cexp_chartTransport_eq_gaussCF_on h𝒢 (@PairData.IsMeasGood.isConformal_chart Ω 𝒢 d hd) hdom
    hfwd hliftm (@PairData.IsMeasGood.continuousOn_lift_chart Ω 𝒢 d hd) hh (QuantumZipper.chiC κ) hM hcond' hmean φ

end CondOn

end Restart

end InteractingSLE
