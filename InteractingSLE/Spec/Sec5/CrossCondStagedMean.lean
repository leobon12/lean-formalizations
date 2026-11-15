/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSideHeightProbMean

/-!
# The staged prefix's own mean, I: a Gaussian chart law read back in the original coordinate

Packet PROVE-CROSSCOND-STAGED2 (the staged prefix's own conditional mean, PROVE-CROSSCOND-STAGED §5.1). The landed
staged law (`Exist.StagedLaw.stageLaw`, `Exist.StagedLaw.post_stage`) gives, at every instruction of a staged history,
the conditional law of the field **read in the chart after the stopped piece**, given the retained records: Gaussian,
with the data of an explicit word (`stopWord`). The consumers (`Sec5.CrossCond.Staged.ae_condExp_union_cfGlueT_add_eq`,
spec pp. 142–148) need it in the **original coordinate** and as the mean of the explored set. This file does that for
an arbitrary random chart `c` measurable in the retained σ-algebra `𝓗` (the argument of
`Sec7.StripSideHeightProb.ae_condExp_cexp_stopChart` and `Sec7.StripSideHeightProbMean.ae_apply_eq_stageMean`, there
for the two-angle program, here with the chart abstracted):

* **`ae_condExp_cexp_of_chartLaw`**: if on an `𝓗`-event `G` the field `Y` is `h` read in `c` and, given `𝓗`, `Y` has
  the Gaussian characteristic functional of a word `β`, then for every test function `φ`, almost surely on `G` with
  `supp φ ⊆ dom c`, `E[e^{i h(φ)} | 𝓗] = exp(i ∫ (𝔤_β ∘ F − χ ℓ) φ − ½ ‖φ‖²_{H⁻¹(dom c)})` (`F`, `ℓ` the forward map and
  lift of `c`, `𝔤_β` the bounded harmonic mean of `β`);
* **`ae_apply_eq_chartMean_of_chartLaw`**: hence every version of the local-set mean of a set `A` retained with `𝓗`
  (local, history-avoidance local for `𝓗`, `dom c` a clopen part of `ℍ ∖ A`) is `∫ (𝔤_β ∘ F − χ ℓ) φ − ∫ 𝔥₀ φ` on test
  functions supported in `dom c`;
* `isChartTransport_congr_dom`: the chart relation only reads the inverse on `ℍ` and the forward map and the lift on
  the domain (used to replace a composite chart by a measurable one).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Staged

open Restart LocalSets Sec7.Lemma72B Sec7.StripSideHeightProb

/-! ### The chart relation only reads the chart on `ℍ` and on the domain -/

/-- **The chart relation only reads the inverse on `ℍ` and the forward map and the lift on the image `inv '' ℍ`**
(for an open image, e.g. a conformal chart). -/
theorem isChartTransport_congr_dom {c c' : Chart} (hopen : IsOpen (c.2.1 '' H)) (h3 : EqOn c.2.1 c'.2.1 H)
    (h1 : EqOn c.1 c'.1 (c.2.1 '' H)) (h2 : EqOn c.2.2 c'.2.2 (c.2.1 '' H)) {σ a k : ℝ}
    {h h' : DistOn upperHalfPlaneOpens} (ht : IsChartTransport c σ a k h h') : IsChartTransport c' σ a k h h' := by
  have himg : c.2.1 '' H = c'.2.1 '' H := image_congr h3
  intro φ φ' hφ hφ'
  rw [← himg] at hφ hφ'
  have hφ'' : ∀ z ∈ c.2.1 '' H, φ z = φ' (c.1 z) * ‖deriv c.1 z‖ ^ 2 := by
    intro z hz
    have hd : deriv c.1 z = deriv c'.1 z :=
      Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) h1)
    rw [hφ' z hz, h1 hz, hd]
  have hint : (∫ w, c'.2.2 (c'.2.1 w) * φ' w) = ∫ w, c.2.2 (c.2.1 w) * φ' w := by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ H
    · have hmem : c.2.1 w ∈ c.2.1 '' H := mem_image_of_mem _ hw
      simp only [← h3 hw, h2 hmem]
    · have h0 : φ' w = 0 := φ'.zero_on_compl hw
      simp only [h0, mul_zero]
  rw [hint]
  exact ht φ φ' hφ hφ''

/-! ### The Gaussian chart law read back in the original coordinate -/

section Pull

variable {Ω : Type*} {𝓗 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {c : Ω → Chart}

/-- **A Gaussian chart law, read back in the original coordinate.** Let `c` be a random conformal chart measurable in
`𝓗` (domain events, masked forward maps and lifts, closed-disc events), `G` an `𝓗`-event on which the field `Y` is
`h` read in `c` (coefficients `1, 0, χ`), and suppose that given `𝓗`, on `G`, `Y` has the Gaussian characteristic
functional of the word `β`. Then for every test function `φ`, almost surely on `G` with `supp φ ⊆ dom c`,
`E[e^{i h(φ)} | 𝓗] = exp(i ∫ (𝔤_β ∘ F − χ ℓ) φ − ½ ‖φ‖²_{H⁻¹(dom c)})`. -/
theorem ae_condExp_cexp_of_chartLaw (h𝓗 : 𝓗 ≤ mΩ) (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓗] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓗] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hCm : ∀ (z : ℂ) (ε : ℝ), MeasurableSet[𝓗] {ω | Metric.closedBall z ε ⊆ (c ω).dom})
    (hliftm : ∀ z, Measurable[𝓗] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h Y : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hY : Measurable Y) {χ : ℝ} {G : Set Ω} (hG : MeasurableSet[𝓗] G)
    (htr : ∀ᵐ ω ∂P, ω ∈ G → IsChartTransport (c ω) 1 0 χ (h ω) (Y ω)) {β : Ω → BoundaryWord}
    (hlaw : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | 𝓗] ω = gaussCF (β ω) ψ)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ G → tsupport φ ⊆ (c ω).dom →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝓗] ω =
        Complex.exp (Complex.I * ((∫ z, ((β ω).mean ((c ω).1 z) - χ * (c ω).2.2 z) * φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((c ω).dom : Set ℂ) φ φ : ℝ) : ℂ)) := by
  classical
  have hSm : MeasurableSet[𝓗] {ω | tsupport φ ⊆ (c ω).dom} :=
    @measurableSet_tsupport_subset_dom Ω 𝓗 c hCm φ
  have hGS : MeasurableSet[𝓗] (G ∩ {ω | tsupport φ ⊆ (c ω).dom}) := hG.inter hSm
  -- the random test: the inverse transport of `φ` on `G`
  obtain ⟨T, hT⟩ : ∃ T : Ω → TestOn upperHalfPlaneOpens, T = fun ω =>
      if ω ∈ G then rInvTest hc φ ω else 0 := ⟨_, rfl⟩
  have hTm : ∀ w, Measurable[𝓗] fun ω => T ω w := by
    intro w
    have h1 := @measurable_rInvTest_apply Ω 𝓗 c hc hdom hfwd hCm φ w
    have e : (fun ω => T ω w) = G.piecewise (fun ω => rInvTest hc φ ω w) (fun _ => 0) := by
      funext ω
      by_cases hω : ω ∈ G
      · rw [piecewise_eq_of_mem _ _ _ hω, hT]
        simp only [hω, ↓reduceIte]
      · rw [piecewise_eq_of_notMem _ _ _ hω, hT]
        simp only [hω, ↓reduceIte]
        rfl
    rw [e]
    exact Measurable.piecewise hG h1 measurable_const
  -- the support-restricted law of the chart field
  obtain ⟨U', hU'⟩ : ∃ U' : Ω → Set ℂ, U' = fun ω => if ω ∈ G then H else ∅ := ⟨_, rfl⟩
  obtain ⟨Ψ', hΨ'⟩ : ∃ Ψ' : Ω → TestOn upperHalfPlaneOpens → ℂ, Ψ' = fun ω ψ =>
      if ω ∈ G then gaussCF (β ω) ψ else 1 := ⟨_, rfl⟩
  have hU'o : ∀ ω, IsOpen (U' ω) := fun ω => by
    rw [hU']
    dsimp only
    split_ifs
    exacts [QuantumZipper.isOpen_H, isOpen_empty]
  have hU'V : ∀ ω, U' ω ⊆ (upperHalfPlaneOpens : Set ℂ) := fun ω => by
    rw [hU']
    dsimp only
    split_ifs
    exacts [subset_rfl, empty_subset _]
  have hΨlaw : ∀ ω, ∃ μ : Measure (DistOn upperHalfPlaneOpens), IsProbabilityMeasure μ ∧
      ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U' ω →
        ∫ u, Complex.exp (Complex.I * (u ψ : ℂ)) ∂μ = Ψ' ω ψ := by
    intro ω
    by_cases hω : ω ∈ G
    · refine ⟨(β ω).gffLaw, inferInstance, fun ψ _ => ?_⟩
      rw [hΨ']
      simp only [hω, ↓reduceIte]
      exact (gaussCF_eq_integral _ ψ).symm
    · refine ⟨Measure.dirac 0, inferInstance, fun ψ _ => ?_⟩
      rw [hΨ']
      simp only [hω, ↓reduceIte]
      rw [integral_dirac' _ _ (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply ψ)).stronglyMeasurable]
      simp
  have hcond' : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport ψ ⊆ U' ω →
      P[fun ω => Complex.exp (Complex.I * (Y ω ψ : ℂ)) | 𝓗] ω = Ψ' ω ψ := by
    intro ψ
    by_cases hψ : ψ = 0
    · subst hψ
      have hc1 : P[fun ω => Complex.exp (Complex.I * (Y ω 0 : ℂ)) | 𝓗] = fun _ => (1 : ℂ) := by
        simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
        exact condExp_const h𝓗 1
      refine Eventually.of_forall fun ω _ => ?_
      rw [hc1, hΨ']
      dsimp only
      split_ifs
      · rw [gaussCF_eq_integral]
        simp
      · rfl
    · filter_upwards [hlaw ψ] with ω h1 hsupp
      by_cases hω : ω ∈ G
      · rw [hΨ']
        simp only [hω, ↓reduceIte]
        exact h1 hω
      · rw [hU'] at hsupp
        simp only [hω, ↓reduceIte] at hsupp
        exact absurd (Restart.eq_zero_of_tsupport_subset_empty hsupp) hψ
  have hTU : ∀ ω, tsupport (T ω) ⊆ U' ω := fun ω => by
    rw [hT, hU']
    dsimp only
    split_ifs
    · exact (rInvTest hc φ ω).tsupport_subset
    · simp
  have key := RandomTest.condExp_cexp_apply_ae_eq_of_subset (P := P) h𝓗 hY hU'o hU'V hΨlaw hcond' hTm hTU
  -- the lift term, an event-masked measurable variable
  obtain ⟨L, hL⟩ : ∃ L : Ω → ℝ, L = {ω | tsupport φ ⊆ (c ω).dom}.indicator
      fun ω => ∫ z, (c ω).2.2 z * φ z := ⟨_, rfl⟩
  have hLm : Measurable[𝓗] L := by
    rw [hL]
    exact @measurable_indicator_integral_lift Ω 𝓗 c hc hCm hliftm hliftc φ
  obtain ⟨f, hf⟩ : ∃ f : Ω → ℂ, f = fun ω => Complex.exp (-(Complex.I * ((χ * L ω : ℝ) : ℂ))) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Ω → ℂ, g = fun ω => Complex.exp (Complex.I * (Y ω (T ω) : ℂ)) := ⟨_, rfl⟩
  have hfm : StronglyMeasurable[𝓗] f := by
    rw [hf]
    exact (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (hLm.const_mul χ)).const_mul Complex.I).neg).stronglyMeasurable
  have hgm : Measurable g := by
    rw [hg]
    exact GFF.measurable_exp_I_mul (RandomTest.measurable_apply_of_forall_measurable hY
      fun z => (hTm z).mono h𝓗 le_rfl)
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := Restart.norm_cexp_I_mul_ofReal
  have hgi : Integrable g P :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by rw [hg]; exact (hnorm _).le)
  have hfg : ∀ ω, ‖ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω)‖ ≤ 1 := fun ω => by
    rw [ContinuousLinearMap.mul_apply', norm_mul, hf, hg]
    simp only [← neg_mul]
    rw [Complex.norm_exp, Complex.norm_exp]
    simp
  have hfgi : Integrable (fun ω => ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω)) P :=
    Integrable.of_bound ((hfm.mono h𝓗).measurable.mul hgm).aestronglyMeasurable 1 (Eventually.of_forall hfg)
  have hpull := condExp_bilin_of_stronglyMeasurable_left (B := ContinuousLinearMap.mul ℝ ℂ)
    (m := 𝓗) (μ := P) hfm hfgi hgi
  -- on `G` with `supp φ` in the domain, `e^{i h(φ)} = f · g`
  have hhφ : Measurable fun ω => h ω φ := (LQGMetric.measurable_distOn_apply φ).comp hh
  have hTω : ∀ ω (hωG : ω ∈ G) (hωS : tsupport φ ⊆ (c ω).dom), T ω = invTest (hc ω) φ hωS := by
    intro ω hωG hωS
    rw [hT]
    simp only [hωG, ↓reduceIte, rInvTest, show tsupport φ ⊆ (c ω).dom from hωS, ↓reduceDIte]
  have hLω : ∀ ω (hωS : tsupport φ ⊆ (c ω).dom), L ω = ∫ z, (c ω).2.2 z * φ z := by
    intro ω hωS
    rw [hL, indicator_of_mem (show ω ∈ {ω | tsupport φ ⊆ (c ω).dom} from hωS)]
  have hloc := Restart.ae_condExp_congr_on (𝒦 := 𝓗) (P := P) hGS
    (GFF.integrable_exp_I_mul hhφ) hfgi (X := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)))
    (Y := fun ω => ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω)) (by
      filter_upwards [htr] with ω htrω hω
      obtain ⟨hωG, hωS⟩ := hω
      rw [ContinuousLinearMap.mul_apply', hf, hg]
      dsimp only
      rw [hTω ω hωG hωS, hLω ω hωS, ← Complex.exp_add,
        apply_eq_of_isChartTransport (hc ω) (hliftc ω) (htrω hωG) φ hωS]
      congr 1
      push_cast
      ring)
  filter_upwards [hloc, hpull, key] with ω h1 h2 h3 hωG hωS
  rw [h1 ⟨hωG, hωS⟩, h2, ContinuousLinearMap.mul_apply']
  have hg' : P[g | 𝓗] ω = Ψ' ω (T ω) := by rw [hg]; exact h3
  rw [hg', hΨ', hf]
  dsimp only
  rw [hTω ω hωG hωS, hLω ω hωS]
  simp only [hωG, ↓reduceIte]
  -- the mean, by the change of variables `w = F(z)`
  have hmean : ∫ w, (β ω).mean w * invTest (hc ω) φ hωS w = ∫ z, (β ω).mean ((c ω).1 z) * φ z := by
    have h1 := Chart.integral_mul_pushTest (hc ω) (invTest (hc ω) φ hωS) (fun z => (β ω).mean ((c ω).1 z))
    rw [pushTest_invTest] at h1
    rw [h1]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ H
    · simp only [(hc ω).2.2 w hw]
    · simp only [invTest_apply_of_notMem (hc ω) φ hωS hw, mul_zero]
  -- the variance, by conformal invariance
  have hcov : QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) (invTest (hc ω) φ hωS)
      (invTest (hc ω) φ hωS) = QuantumZipper.zeroGFFTestCov ((c ω).dom : Set ℂ) φ φ := by
    have h1 := Chart.zeroGFFTestCov_pushTest (hc ω) (invTest (hc ω) φ hωS) (invTest (hc ω) φ hωS)
    rw [pushTest_invTest] at h1
    exact h1.symm
  have hsplit : ∫ z, ((β ω).mean ((c ω).1 z) - χ * (c ω).2.2 z) * φ z =
      (∫ z, (β ω).mean ((c ω).1 z) * φ z) - χ * ∫ z, (c ω).2.2 z * φ z := by
    have hm : ContinuousOn (fun z => (β ω).mean ((c ω).1 z)) (c ω).dom :=
      (BoundaryWord.continuousOn_mean _).comp (hc ω).differentiableOn_fwd.continuousOn fun z hz =>
        (hc ω).fwd_mem hz
    have hi1 := WholeField.integrable_mul_testOn hm φ hωS
    have hi2 := (WholeField.integrable_mul_testOn (hliftc ω) φ hωS).const_mul χ
    rw [← integral_const_mul, ← integral_sub hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  rw [gaussCF, hmean, hcov, hsplit, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Pull

/-! ### The local-set mean of a set retained with the records -/

section Mean

variable {Ω : Type*} {𝓗 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {c : Ω → Chart}

/-- **The local-set mean of a set retained with `𝓗` is the chart mean** (the generic form of
`Sec7.StripSideHeightProbMean.ae_apply_eq_stageMean`). In the setting of `ae_condExp_cexp_of_chartLaw`, with `h` a GFF
with piecewise-constant data `b` and bounded harmonic extension `𝔥₀`, let `A` be a local set of `h − 𝔥₀`,
history-avoidance local for `𝓗`, whose complement contains `dom c` as a clopen part on `G`. Then every version `g` of
its local-set mean satisfies, almost surely on `G`, `g(φ) = ∫ (𝔤_β ∘ F − χ ℓ) φ − ∫ 𝔥₀ φ` for every `φ` supported in
`dom c`. -/
theorem ae_apply_eq_chartMean_of_chartLaw (h𝓗 : 𝓗 ≤ mΩ) (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓗] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓗] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hCm : ∀ (z : ℂ) (ε : ℝ), MeasurableSet[𝓗] {ω | Metric.closedBall z ε ⊆ (c ω).dom})
    (hliftm : ∀ z, Measurable[𝓗] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {b : ℝ → ℝ} {jumps : Finset ℝ}
    {h Y : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hY : Measurable Y) {χ : ℝ} {G : Set Ω}
    (hG : MeasurableSet[𝓗] G) (htr : ∀ᵐ ω ∂P, ω ∈ G → IsChartTransport (c ω) 1 0 χ (h ω) (Y ω))
    {β : Ω → BoundaryWord}
    (hlaw : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | 𝓗] ω = gaussCF (β ω) ψ)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A (WholeField.centredField h u₀) P)
    (hmark : WholeField.IsHistoryAvoidanceLocal 𝓗 A (WholeField.centredField h u₀) P)
    (hAD : ∀ᵐ ω ∂P, ω ∈ G → ((c ω).dom : Set ℂ) ⊆ H \ A ω ∧ IsOpen ((H \ A ω) \ (c ω).dom))
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ G → tsupport φ ⊆ (c ω).dom →
      g ω φ = (∫ z, ((β ω).mean ((c ω).1 z) - χ * (c ω).2.2 z) * φ z) - ∫ z, u₀ z * φ z := by
  classical
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hSm : MeasurableSet[𝓗] {ω | tsupport φ ⊆ (c ω).dom} :=
    @measurableSet_tsupport_subset_dom Ω 𝓗 c hCm φ
  have hGS : MeasurableSet[𝓗] (G ∩ {ω | tsupport φ ⊆ (c ω).dom}) := hG.inter hSm
  -- the chart mean of `φ`
  obtain ⟨m, hm⟩ : ∃ m : Ω → ℝ, m = fun ω => (∫ z, ((β ω).mean ((c ω).1 z) - χ * (c ω).2.2 z) * φ z) -
      ∫ z, u₀ z * φ z := ⟨_, rfl⟩
  -- the Gaussian kernel at every frequency
  have hfreq : ∀ r : ℝ, ∀ᵐ ω ∂P, ω ∈ G ∩ {ω | tsupport φ ⊆ (c ω).dom} →
      (P[fun ω' => Complex.exp (Complex.I * ((r * WholeField.centredField h u₀ ω' φ : ℝ) : ℂ)) | 𝓗]) ω =
        Complex.exp (Complex.I * ((r * m ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (r ^ 2 * QuantumZipper.zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro r
    set U : ℝ := ∫ z, u₀ z * φ z with hU
    have hfun : (fun ω' => Complex.exp (Complex.I * ((r * WholeField.centredField h u₀ ω' φ : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * ((r * U : ℝ) : ℂ))) •
          fun ω' => Complex.exp (Complex.I * (h ω' (r • φ) : ℂ)) := by
      funext ω'
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, WholeField.centredField_apply h hu₀.1 ω' φ, map_smul,
        smul_eq_mul]
      congr 1
      push_cast
      ring
    have hsm := condExp_smul (μ := P) (Complex.exp (-(Complex.I * ((r * U : ℝ) : ℂ))))
      (fun ω' => Complex.exp (Complex.I * (h ω' (r • φ) : ℂ))) 𝓗
    filter_upwards [ae_condExp_cexp_of_chartLaw h𝓗 hc hdom hfwd hCm hliftm hliftc hh.1 hY hG htr hlaw (r • φ),
      hsm, hAD, hloc.2.1] with ω hlω hsmω hADω hAc hω
    obtain ⟨hωG, hωS⟩ := hω
    obtain ⟨hDA, hDo⟩ := hADω hωG
    have hS' : tsupport ⇑(r • φ) ⊆ (c ω).dom := (WholeField.tsupport_smul_testOn_subset r φ).trans hωS
    have hdomH : ((c ω).dom : Set ℂ) ⊆ H := fun z hz => (hDA hz).1
    have hcov : QuantumZipper.zeroGFFTestCov (H \ A ω) φ φ =
        QuantumZipper.zeroGFFTestCov ((c ω).dom : Set ℂ) φ φ :=
      zeroGFFTestCov_eq_of_isClopen hAc.2 sdiff_subset (c ω).dom.isOpen hDA hDo φ hωS
    have hcov' := zeroGFFTestCov_smul_self (c ω).dom.isOpen hdomH r φ
    rw [hfun, hsmω, Pi.smul_apply, smul_eq_mul, hlω hωG hS', WholeField.integral_mul_smul, hcov', hcov, hm]
    rw [← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the mean, recovered as a function of the records
  set ψ : ℕ → Ω → ℂ := fun n => P[fun ω' => Complex.exp (Complex.I *
      ((1 / ((n : ℝ) + 1) * WholeField.centredField h u₀ ω' φ : ℝ) : ℂ)) | 𝓗] with hψ_def
  have hψm : ∀ n, StronglyMeasurable[𝓗] (ψ n) := fun n => stronglyMeasurable_condExp
  have hmm : Measurable[𝓗] (WholeField.meanOfCharFun ψ) := WholeField.measurable_meanOfCharFun hψm
  have hmeq : ∀ᵐ ω ∂P, ω ∈ G ∩ {ω | tsupport φ ⊆ (c ω).dom} → WholeField.meanOfCharFun ψ ω = m ω := by
    filter_upwards [ae_all_iff.2 fun n : ℕ => hfreq (1 / ((n : ℝ) + 1))] with ω hω hωG
    exact WholeField.meanOfCharFun_eq fun n => hω n hωG
  have hkern : ∀ r : ℝ, ∀ᵐ ω ∂P, ω ∈ G ∩ {ω | tsupport φ ⊆ (c ω).dom} →
      (P[fun ω' => Complex.exp (Complex.I * ((r * WholeField.centredField h u₀ ω' φ : ℝ) : ℂ)) | 𝓗]) ω =
        Complex.exp (Complex.I * ((r * WholeField.meanOfCharFun ψ ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (r ^ 2 * QuantumZipper.zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro r
    filter_upwards [hfreq r, hmeq] with ω h1 h2 hωG
    rw [h2 hωG]
    exact h1 hωG
  obtain ⟨k1, -⟩ := WholeField.ae_condExp_germSigma_history_eq hh0 hA h𝓗 hmark hloc.2.1 φ hGS hmm hkern
  have e := WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup hh0 hA hloc h𝓗 hmark hg φ
  filter_upwards [k1, e, hmeq] with ω h1 h2 h3 hωG hωS
  rw [h2, h1 ⟨hωG, hωS⟩, h3 ⟨hωG, hωS⟩, hm]

end Mean

end InteractingSLE.Sec5.CrossCond.Staged
