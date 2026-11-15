/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop61BGlobal
import InteractingSLE.Spec.Sec6.CondMeanStop
import InteractingSLE.Spec.Coupling.WholeFieldMarked

/-!
# Proposition 6.1: conditioning on the ordered labeled stopped curves

Packet PROVE-SEC6-D, item (R2) 7 of `planning/handoffs/PROVE-SEC6-C.md` (specification §6.1,
`source/spec/p145-192.md`, `#prop-6.1` p. 154; supplement §2.3, `source/spec/p433-480.md`,
"Conditional-mean consequence, with its inputs stated", pp. 454–455).

Proposition 6.1 conditions on the **ordered labeled pair** `(η_{θ₁}|_{[0,τ]}, η_{θ₂})`, not only on the
unlabeled union `A(τ)`: "Condition on the ordered labeled pair … Retain the canonical revealed germs
during the local-set argument. Once the mean below has been identified, it and the residual covariance
are functions of the labeled pair, so the same Gaussian law holds after those germs are forgotten. The
notation `A(τ)` records the union; it is not used here to discard the curve labels" (p. 154). Lemma 6.2
supplies the needed locality: "the union together with the ordered tuple of stopped histories
satisfies the same history-sensitive locality condition".

PROVE-SEC6-C proved the Gaussian law of a component given the germ σ-algebra `𝒜` of the union only.
This file adds the labels, for the explored set `A = ⋃ᵢ ηᵢ([0, τᵢ])` of Lemma 6.2 (any number of
curves, `τᵢ` in Galmarino path form, ruling R37) and `ℋ = σ(ordered stopped histories)`:

* `isHistoryAvoidanceLocal_explored` : Lemma 6.2's marked locality (`le_aeSigma_explored`, landed) is
  the history-marked avoidance criterion `WholeField.IsHistoryAvoidanceLocal ℋ A h P` (Aux. lemma 18's
  first conclusion, landed with its consequences in `WholeFieldMarked`).
* `ae_condExp_exp_eq_of_component_marked` : the conditional law of the field on a component of
  `ℍ ∖ A` **given the germs and the labeled histories**, `𝒜 ∨ ℋ`, is the local-set mean plus a
  zero-boundary GFF of the component (the marks add nothing to the mean).
* `ae_condExp_exp_eq_of_eqOn_component_marked` : the same with an identified mean `v + F = 𝔥` (the
  form of Proposition 6.1).
* `ae_condExp_exp_eq_of_le_marked` : forgetting the germs (and anything else) down to a σ-algebra
  `𝒢 ≤ 𝒜 ∨ ℋ` — e.g. the labeled histories alone — for which the event, the mean pairing and the
  residual variance are measurable ("they are functions of the labeled pair"; the supplement records
  this measurable-map input, p. 455).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal Real

namespace InteractingSLE.Sec6

open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv)
open SupercriticalConformalCovariance (IsConformalBijection)
open LocalSets

/-- The σ-algebra of the ordered tuple of stopped histories `(ηᵢ|_{[0, τᵢ]})ᵢ` (each recorded as its
stopping time and its stopped rational-time coordinates). -/
@[instance_reducible]
def stoppedHistSigma {Ω : Type*} {k : ℕ} (η : Fin k → Ω → ℝ≥0 → ℂ) (τ : Fin k → Ω → ℝ≥0∞) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω i => histOf (pathCoord (η i ω)) (τ i ω)) inferInstance

section Marking

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {k : ℕ} {η : Fin k → Ω → ℝ≥0 → ℂ} {x : Fin k → ℂ}
  {τ : Fin k → Ω → ℝ≥0∞} {S : Fin k → (Fin k → Hist) → (ℚ≥0 → ℂ) → ℝ≥0∞}

/-- The stopped histories are measurable. -/
theorem stoppedHistSigma_le (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hτm : ∀ i, Measurable (τ i)) : stoppedHistSigma η τ ≤ mΩ := by
  refine Measurable.comap_le ?_
  refine Measurable.of_eval fun i => ?_
  have hc : Measurable fun ω => pathCoord (η i ω) :=
    Measurable.of_eval fun q => hηm i (q : ℝ≥0)
  exact measurable_histOf.comp ((hτm i).prodMk hc)

/-- **Lemma 6.2 with labels is Aux. 18's marked criterion.** Under the hypotheses of Lemma 6.2
(`le_aeSigma_explored`), the explored set `A = ⋃ᵢ ηᵢ([0, τᵢ])` satisfies the history-marked avoidance
criterion for the σ-algebra `ℋ` of the ordered stopped histories: for every open `U ⊆ ℍ` and every
`F ∈ ℋ`, the conditional probability of `{A ∩ U = ∅} ∩ F` given `h` is a measurable function of
`h_{U^c}`. (By Lemma 6.2 the event is almost surely an event of `h_{U^c}`.) -/
theorem isHistoryAvoidanceLocal_explored (hhm : Measurable h) (hc : ∀ i ω, Continuous (η i ω))
    (h0 : ∀ i ω, η i ω 0 = x i) (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (η i) h P)
    (hSm : ∀ j, Measurable (Function.uncurry (S j))) (hSg : ∀ j, IsGalmarino (S j))
    (hτ : ∀ j ω, τ j ω = S j (prevHist (fun i => pathCoord (η i ω)) (fun i => τ i ω) j)
      (pathCoord (η j ω))) :
    WholeField.IsHistoryAvoidanceLocal (stoppedHistSigma η τ) (explored η τ) h P := by
  intro U G hUH hG hd F hF
  obtain ⟨B, hB, rfl⟩ := hF
  set Y : Ω → Fin k → Hist := fun ω i => histOf (pathCoord (η i ω)) (τ i ω)
  set E : Set Ω := {ω | Disjoint (explored η τ ω) U}
  have hmem : MeasurableSet[markedHistSigma E Y] (E ∩ Y ⁻¹' B) :=
    MeasurableSpace.measurableSet_generateFrom ⟨B, hB, rfl⟩
  obtain ⟨S', hS', hSe⟩ :=
    (le_aeSigma_explored hhm hc h0 hηm hdet hloc hSm hSg hτ U G hUH hG hd).1 _ hmem
  obtain ⟨B', hB', rfl⟩ := hS'
  have hYm : Measurable fun ω => markovCompl G (h ω) := (measurable_markovCompl hG).comp hhm
  refine ⟨B'.indicator 1, measurable_one.indicator hB', ?_⟩
  have hm : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  have hind : (E ∩ Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) =ᵐ[P]
      ((fun ω => markovCompl G (h ω)) ⁻¹' B').indicator (fun _ => (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set hSe
  have hYm' : Measurable[MeasurableSpace.comap h inferInstance] fun ω => markovCompl G (h ω) :=
    (measurable_markovCompl hG).comp (comap_measurable h)
  have hsm : StronglyMeasurable[MeasurableSpace.comap h inferInstance]
      (((fun ω => markovCompl G (h ω)) ⁻¹' B').indicator (fun _ => (1 : ℝ))) :=
    (Measurable.indicator measurable_const (hYm' hB')).stronglyMeasurable
  have hint : Integrable (((fun ω => markovCompl G (h ω)) ⁻¹' B').indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator (hYm hB')
  filter_upwards [condExp_congr_ae (m := MeasurableSpace.comap h inferInstance) hind] with ω hω
  rw [hω, condExp_of_stronglyMeasurable hm hsm hint]
  simp only [indicator, mem_preimage, Pi.one_apply]
  rfl

end Marking

/-! ### The marked law on a component -/

section MarkedLaw

variable {Ω : Type*} {ℋ 𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}
  {g : Ω → DistOn upperHalfPlaneOpens}

/-- The local-set mean is a version of the conditional mean given the germs:
`g(φ) = E[h(φ) | 𝒜]` almost surely. -/
theorem IsLocalSetMean.ae_eq_condExp_germSigma
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    (hg : IsLocalSetMean A h P g) (φ : TestOn upperHalfPlaneOpens) :
    (fun ω => g ω φ) =ᵐ[P] P[fun ω => h ω φ | germSigma A h] := by
  have hhm := hh.measurable
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := hloc.2.1
  have hav : IsAvoidanceLocal A h P := ((isLocalSet_tfae hh hA hAc).out 4 1).1 hloc
  obtain ⟨M, h₁, hM, hMlim, hh₁m, hh₁⟩ := exists_germVersion hh hA hav hAc
  have hharm := ae_isHarmonicDistOn_germVersion hh hA hav hAc hM hMlim hh₁
  have hg₁ : IsLocalSetMean A h P h₁ :=
    ⟨hh₁m, hharm, isCondZeroBoundaryGFF_germVersion hh hA hAc hM hh₁m hh₁⟩
  have e : (fun ω => g ω φ) =ᵐ[P] fun ω => h₁ ω φ := IsLocalSetMean.ae_apply_eq hA hhm hg hg₁ φ
  exact e.trans ((hh₁ φ).trans (hM φ).2.1)

/-- **The conditional law on a component, given the germs and the marks.** Let `A` be a local set of
the zero-boundary GFF `h` on `ℍ` with local-set mean `g`, and `ℋ` a σ-algebra of marks for which `A`
satisfies the history-marked avoidance criterion (e.g. the ordered stopped histories of Lemma 6.2,
`isHistoryAvoidanceLocal_explored`). Almost surely, whenever the test function `φ` is supported in a
component `C` of `ℍ ∖ A`,
`E[e^{i h(φ)} | 𝒜 ∨ ℋ] = e^{i g(φ)} e^{−σ²_C(φ)/2}`: the marks do not change the conditional mean,
and the residual field is a zero-boundary GFF of `C`. -/
theorem ae_condExp_exp_eq_of_component_marked
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P) (hℋ : ℋ ≤ mΩ)
    (hmark : WholeField.IsHistoryAvoidanceLocal ℋ A h P) (hg : IsLocalSetMean A h P g)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ A ω, tsupport φ ⊆ connectedComponentIn (H \ A ω) z₀ →
      P[fun ω' => cexp (I * (h ω' φ : ℂ)) | germSigma A h ⊔ ℋ] ω =
        cexp (I * (g ω φ : ℂ)) *
          ((Real.exp (-(1 / 2) *
            QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ A ω) z₀) φ φ) : ℝ) : ℂ) := by
  have hhm := hh.measurable
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := hloc.2.1
  have hle := germSigma_le hA hhm
  obtain ⟨M, hMm, hM1, hM2⟩ := WholeField.exists_condExp_germSigma_history hh hA hℋ hmark hAc φ
  -- the marked mean is the unmarked one
  have hMi : Integrable M P := integrable_condExp.congr hM1.symm
  have hMg : M =ᵐ[P] fun ω => g ω φ := by
    have e1 : P[P[fun ω => h ω φ | germSigma A h ⊔ ℋ] | germSigma A h] =ᵐ[P]
        P[fun ω => h ω φ | germSigma A h] := condExp_condExp_of_le le_sup_left (sup_le hle hℋ)
    have e2 : P[P[fun ω => h ω φ | germSigma A h ⊔ ℋ] | germSigma A h] =ᵐ[P]
        P[M | germSigma A h] := condExp_congr_ae hM1.symm
    rw [condExp_of_stronglyMeasurable hle hMm.stronglyMeasurable hMi] at e2
    exact e2.symm.trans (e1.trans (IsLocalSetMean.ae_eq_condExp_germSigma hh hA hloc hg φ).symm)
  filter_upwards [hM2, hMg, hAc] with ω hω hωM ⟨hAH, hωo⟩ z₀ _ hφC
  rw [← hω, hωM, relClosureH_eq hAH hωo]
  have hCo : IsOpen (connectedComponentIn (H \ A ω) z₀) := hωo.connectedComponentIn
  have hCc : ∀ z ∈ connectedComponentIn (H \ A ω) z₀,
      connectedComponentIn (H \ A ω) z ⊆ connectedComponentIn (H \ A ω) z₀ := fun z hz => by
    rw [connectedComponentIn_eq hz]
  rw [zeroGFFTestCov_eq_of_isClopen hωo sdiff_subset hCo (connectedComponentIn_subset _ _)
    (isOpen_diff_of_forall_connectedComponentIn_subset hωo hCc) φ hφC]

/-- **The Gaussian law of Proposition 6.1 given the germs and the marks, with an identified mean.**
Almost surely: if `φ` is supported in a component `C` of `ℍ ∖ A` and a harmonic representative `v` of
`g` satisfies `v + F = 𝔥` on `C`, then given `𝒜 ∨ ℋ` the field `h + F` paired with `φ` has the
conditional characteristic function of `(𝔥, φ) + GFF_C(φ)`. -/
theorem ae_condExp_exp_eq_of_eqOn_component_marked
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P) (hℋ : ℋ ≤ mΩ)
    (hmark : WholeField.IsHistoryAvoidanceLocal ℋ A h P) (hg : IsLocalSetMean A h P g)
    {F : ℂ → ℝ} (hF : ContinuousOn F H) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ A ω, tsupport φ ⊆ connectedComponentIn (H \ A ω) z₀ →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ A ω → g ω ψ = ∫ x, v x * ψ x) →
      ∀ 𝔥 : ℂ → ℝ, (∀ z ∈ connectedComponentIn (H \ A ω) z₀, v z + F z = 𝔥 z) →
      P[fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ)) | germSigma A h ⊔ ℋ] ω =
        cexp (I * ((∫ x, 𝔥 x * φ x : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) *
            QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ A ω) z₀) φ φ) : ℝ) : ℂ) := by
  set c : ℂ := cexp (I * ((∫ x, F x * φ x : ℝ) : ℂ))
  have hsplit : (fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ))) =
      c • fun ω' => cexp (I * (h ω' φ : ℂ)) := by
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul, c, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hsm := condExp_smul (μ := P) c (fun ω' => cexp (I * (h ω' φ : ℂ))) (germSigma A h ⊔ ℋ)
  filter_upwards [hsm, ae_condExp_exp_eq_of_component_marked hh hA hloc hℋ hmark hg φ, hloc.2.1]
    with ω hsmω hlaw ⟨_, hAo⟩ z₀ hz₀ hφC v hv hrep 𝔥 heq
  rw [hsplit, hsmω, Pi.smul_apply, hlaw z₀ hz₀ hφC, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  have hCV : connectedComponentIn (H \ A ω) z₀ ⊆ H \ A ω := connectedComponentIn_subset _ _
  have hφV : tsupport φ ⊆ H \ A ω := hφC.trans hCV
  have hvc : ContinuousOn v (H \ A ω) := fun z hz => (hv z hz).1.continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (H \ A ω) := hF.mono sdiff_subset
  have hsum : g ω φ + ∫ x, F x * φ x = ∫ x, 𝔥 x * φ x := by
    rw [hrep φ hφV, ← integral_add (integrable_mul_test hAo hvc φ hφV)
      (integrable_mul_test hAo hFc φ hφV)]
    congr 1; funext x
    by_cases hx : x ∈ connectedComponentIn (H \ A ω) z₀
    · rw [← heq x hx]; ring
    · simp only [image_eq_zero_of_notMem_tsupport (fun h' => hx (hφC h')), mul_zero, add_zero]
  rw [← hsum]
  push_cast
  ring

/-- **Forgetting the germs** (p. 154: "Once the mean below has been identified, it and the residual
covariance are functions of the labeled pair, so the same Gaussian law holds after those germs are
forgotten"). For any `𝒢 ≤ 𝒜 ∨ ℋ` (e.g. `𝒢 = ℋ`, the labeled histories alone), a `𝒢`-event `G`, and
`𝒢`-measurable `M, S` such that almost surely on `G` the test function `φ` is supported in a component
`C` of `ℍ ∖ A` with `g(φ) = M` and `σ²_C(φ) = S`: almost surely on `G`,
`E[e^{i h(φ)} | 𝒢] = e^{i M} e^{−S/2}`. -/
theorem ae_condExp_exp_eq_of_le_marked
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P) (hℋ : ℋ ≤ mΩ)
    (hmark : WholeField.IsHistoryAvoidanceLocal ℋ A h P) (hg : IsLocalSetMean A h P g)
    (φ : TestOn upperHalfPlaneOpens) (h𝒢 : 𝒢 ≤ germSigma A h ⊔ ℋ)
    {G : Set Ω} (hG : MeasurableSet[𝒢] G) {M S : Ω → ℝ} (hM : Measurable[𝒢] M)
    (hS : Measurable[𝒢] S)
    (hGC : ∀ᵐ ω ∂P, ω ∈ G → ∃ z₀ ∈ H \ A ω, tsupport φ ⊆ connectedComponentIn (H \ A ω) z₀ ∧
      g ω φ = M ω ∧
        QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ A ω) z₀) φ φ = S ω) :
    ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => cexp (I * (h ω' φ : ℂ)) | 𝒢] ω =
        cexp (I * (M ω : ℂ)) * ((Real.exp (-(1 / 2) * S ω) : ℝ) : ℂ) := by
  have hhm := hh.measurable
  have hle : germSigma A h ⊔ ℋ ≤ mΩ := sup_le (germSigma_le hA hhm) hℋ
  have hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω) := hloc.2.1.mono fun _ h => h.2
  set Y : Ω → ℂ := fun ω => cexp (I * (M ω : ℂ)) * ((Real.exp (-(1 / 2) * max (S ω) 0) : ℝ) : ℂ)
    with hYdef
  have hYm : Measurable[𝒢] Y := by
    let _ : MeasurableSpace Ω := 𝒢
    exact (GFF.measurable_exp_I_mul hM).mul (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (hS.max measurable_const))))
  have hYi : Integrable Y P := by
    refine Integrable.of_bound ((hYm.mono (h𝒢.trans hle) le_rfl).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => ?_)
    rw [hYdef, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith [le_max_right (S ω) 0]
  have hX : Integrable (fun ω' => cexp (I * (h ω' φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hhm)
  have hXY : ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => cexp (I * (h ω' φ : ℂ)) | germSigma A h ⊔ ℋ] ω = Y ω := by
    filter_upwards [ae_condExp_exp_eq_of_component_marked hh hA hloc hℋ hmark hg φ, hGC, hopen]
      with ω hω hωG hωo hmem
    obtain ⟨z₀, hz₀, hφC, hgM, hσS⟩ := hωG hmem
    have hS0 : 0 ≤ S ω := by
      rw [← hσS]
      exact zeroGFFTestCov_self_nonneg hωo.connectedComponentIn
        ((connectedComponentIn_subset _ _).trans sdiff_subset) φ
    rw [hω z₀ hz₀ hφC, hgM, hσS]
    simp only [hYdef, max_eq_left hS0]
  filter_upwards [condExp_ae_eq_on_of_le h𝒢 hle hX hYm.stronglyMeasurable hYi hG hXY, hGC, hopen]
    with ω hω hωG hωo hmem
  obtain ⟨z₀, -, -, -, hσS⟩ := hωG hmem
  have hS0 : 0 ≤ S ω := by
    rw [← hσS]
    exact zeroGFFTestCov_self_nonneg hωo.connectedComponentIn
      ((connectedComponentIn_subset _ _).trans sdiff_subset) φ
  rw [hω hmem]
  simp only [hYdef, max_eq_left hS0]

end MarkedLaw

end InteractingSLE.Sec6
