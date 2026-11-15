/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72CLocal
import InteractingSLE.Spec.Sec7.LocalExtICov
import InteractingSLE.Spec.Coupling.MartMeans2Chart

/-!
# The locality (L) through the pocket chart

Packet PROVE-LEMMA72C. Specification §7.1, proof of Lemma 7.1 (`source/spec/p193-240.md` L600–L602, pp. 224–225):
"For each bounded stopping time of this mapped path, the history-locality statement of Lemma 6.2 applies to the
revealed outer curves and the middle prefix. Their original prefixes have no original-boundary contacts, so their
stopped ranges equal their stopped hulls; the optional history marking of the original coupling supplies the required
history locality."

In the pocket chart `ψ = c.fwd : C → ℍ` (inverse `c.inv`), the complement of the mapped hull `ℍ ∖ K` corresponds to
the open set `c.inv(ℍ ∖ K) ⊆ C` of the original domain; its complement `B = ℍ ∖ c.inv(ℍ ∖ K)` (the outside of the
pocket, the outer curves and the pulled-back hull) contains the explored set of the three curves. This file proves the
transport step: **if `B` is a history-marked local set of the centred original field, then `K` is a local set of the
pulled-back field `h_ψ = h ∘ ψ⁻¹ + a + k ℓ ∘ ψ⁻¹`, also conditionally on every event of positive probability of the
germs of `B` and the marks.**

* `isHarmonicDistOn_chartTransport`: a distribution harmonic on `c.inv(O)` transports to one harmonic on `O`, for a
  chart whose lift `ℓ` is harmonic on its domain (`ℓ = Im log ψ′` for the pocket chart);
* `isCondZeroBoundaryGFF_pullField_sub`: a conditional zero-boundary GFF on the random subdomain `c.inv(O)` of the
  chart domain transports to one on `O` (`IsConformal.zeroGFFTestCov_pushTest` for all test functions);
* **`isLocalSet_cond_chart_of_isHistoryAvoidanceLocal`**: the locality transport (germ law with history in the original
  domain, `exists_germLaw_of_isHistoryAvoidanceLocal`; conditioning on the mark; pullback; Lemma 3.6 (iii) ⇒ (iv)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov)
open scoped ENNReal

universe u

namespace InteractingSLE.Sec7.Lemma72C

open LQGMetric LocalSets WholeField

/-! ### Harmonic distributions through a chart -/

section Harmonic

variable {c : Chart}

/-- **Harmonic distributions transport through a chart with a harmonic lift.** If `M` is harmonic on `c.inv(O)`
(`O ⊆ ℍ` open), then `chartTransport c 1 a k M = M ∘ inv + a + k ℓ ∘ inv` is harmonic on `O`, with representative
`v ∘ inv + a + k ℓ ∘ inv`. -/
theorem isHarmonicDistOn_chartTransport (hc : c.IsConformal) (hliftc : ContinuousOn c.2.2 c.dom)
    (hlift : InnerProductSpace.HarmonicOnNhd c.2.2 c.dom) {O : Set ℂ} (hOo : IsOpen O) (hO : O ⊆ H)
    {M : DistOn upperHalfPlaneOpens} (hM : IsHarmonicDistOn M (c.2.1 '' O)) (a k : ℝ) :
    IsHarmonicDistOn (Chart.chartTransport hc 1 a k M) O := by
  obtain ⟨v, hv, hrep⟩ := hM
  have hIo : IsOpen (c.2.1 '' O) := hc.isOpen_image_of_subset hOo hO
  have hdiff : DifferentiableOn ℂ c.2.1 O := hc.1.mono hO
  have hv' : InnerProductSpace.HarmonicOnNhd (v ∘ c.2.1) O :=
    LQGMetric.harmonicOnNhd_comp_holo hIo hOo hv hdiff (mapsTo_image _ _)
  have hl' : InnerProductSpace.HarmonicOnNhd (c.2.2 ∘ c.2.1) O :=
    LQGMetric.harmonicOnNhd_comp_holo c.dom.isOpen hOo hlift hdiff fun w hw => hc.inv_mem_dom (hO hw)
  refine ⟨fun w => v (c.2.1 w) + a + k * c.2.2 (c.2.1 w), ?_, fun φ hφ => ?_⟩
  · have h := (hv'.add (InnerProductSpace.harmonicOnNhd_const a)).add (hl'.const_smul (c := k))
    convert h using 1
    funext w
    simp only [Pi.add_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  · have hloc := Chart.locallyIntegrableOn_of_continuousOn (hc.continuousOn_lift_inv hliftc)
    rw [Chart.chartTransport_apply hc hloc, one_mul]
    let O' : Opens ℂ := ⟨O, hOo⟩
    have hsupp : tsupport (Chart.pushTest hc φ) ⊆ c.2.1 '' O := hc.tsupport_pushTest_subset_image (O := O') hO φ hφ
    rw [hrep _ hsupp, Chart.integral_mul_pushTest]
    have hvc : ContinuousOn (fun w => v (c.2.1 w)) O := fun w hw => (hv' w hw).1.continuousAt.continuousWithinAt
    have hlc : ContinuousOn (fun w => c.2.2 (c.2.1 w)) O := (hc.continuousOn_lift_inv hliftc).mono hO
    have hi1 : Integrable fun w => v (c.2.1 w) * φ w :=
      Coupling.MartMeans2.integrable_mul_test_of_continuousOn hvc φ hφ
    have hi0 : Integrable fun w => φ w := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    have hi3 : Integrable fun w => c.2.2 (c.2.1 w) * φ w :=
      Coupling.MartMeans2.integrable_mul_test_of_continuousOn hlc φ hφ
    have e : (fun w => (v (c.2.1 w) + a + k * c.2.2 (c.2.1 w)) * φ w) =
        fun w => (v (c.2.1 w) * φ w + a * φ w) + k * (c.2.2 (c.2.1 w) * φ w) := by
      funext w; ring
    have h2 : ∫ w, (v (c.2.1 w) * φ w + a * φ w + k * (c.2.2 (c.2.1 w) * φ w)) =
        (∫ w, (v (c.2.1 w) * φ w + a * φ w)) + ∫ w, k * (c.2.2 (c.2.1 w) * φ w) :=
      integral_add (hi1.add (hi0.const_mul a)) (hi3.const_mul k)
    have h3 : ∫ w, (v (c.2.1 w) * φ w + a * φ w) = (∫ w, v (c.2.1 w) * φ w) + ∫ w, a * φ w :=
      integral_add hi1 (hi0.const_mul a)
    rw [e, h2, h3, integral_const_mul, integral_const_mul]

end Harmonic

/-! ### Conditional zero-boundary GFFs on a random subdomain of the chart -/

section Pull

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Conditional zero-boundary GFFs on a subdomain transport through a `𝒢`-measurable random chart.** If,
conditionally on `𝒢`, `X` is a zero-boundary GFF on `c.inv(O)` (`O ⊆ ℍ` open, random), then `X ∘ inv` is,
conditionally on `𝒢`, a zero-boundary GFF on `O`. -/
theorem isCondZeroBoundaryGFF_pullField_sub (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    {O : Ω → Set ℂ} (hOo : ∀ ω, IsOpen (O ω)) (hO : ∀ ω, O ω ⊆ H) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => (c ω).2.1 '' O ω) X) :
    IsCondZeroBoundaryGFF P 𝒢 O (fun ω => Chart.pullField (hc ω) (X ω)) := by
  intro φ
  have hT : ∀ z, Measurable[𝒢] fun ω => Chart.pushTest (hc ω) φ z := fun z =>
    @Chart.measurable_pushTest_apply Ω 𝒢 c hc hdom hfwd φ z
  have hsub : ∀ ω, (c ω).2.1 '' O ω ⊆ H := fun ω => (image_mono (hO ω)).trans (hc ω).2.1.image_subset
  have h := RandomTest.condExp_cexp_apply_ae_eq h𝒢 hX
    (Ψ := fun ω φ => ((Real.exp (-(1 / 2) * zeroGFFTestCov ((c ω).2.1 '' O ω) φ φ) : ℝ) : ℂ))
    (fun ω => RandomTest.exists_zbExtLaw (U := ⟨(c ω).2.1 '' O ω, (hc ω).isOpen_image_of_subset (hOo ω) (hO ω)⟩)
      (hsub ω)) hcond hT
  simp only [Chart.pullField_apply]
  refine h.trans (Eventually.of_forall fun ω => ?_)
  have hcov := (hc ω).zeroGFFTestCov_pushTest (O := ⟨O ω, hOo ω⟩) (hO ω) φ φ
  simp only [TopologicalSpace.Opens.coe_mk] at hcov
  simp only [hcov]

end Pull

/-! ### The locality transport -/

section Transport

variable {Ω : Type u} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **(L) through the pocket chart, conditionally on a mark** (specification p. 225). Let `h` be a measurable field
on `ℍ` whose centring `h⁰ = h − u₀` (`u₀` harmonic) is a zero-boundary GFF; `c` a random conformal chart, measurable for
the marks `ℋ` (domain events, forward maps and lifts), with lifts continuous and harmonic on the chart domains; `K` an
`ℋ`-measurable random relatively closed subset of `ℍ`. If the complement `B = ℍ ∖ c.inv(ℍ ∖ K)` of the pulled-back
region is an `ℋ`-measurable history-marked local set of `h⁰` for the marks `ℋ`, then for every event `D` of positive
probability in the germ σ-algebra of `B` joined with the marks (e.g. an event of the field off the pocket), `K` is a
local set of the pulled-back field `chartTransport c 1 a k h` under `P[· | D]`.

Proof: Lemma 3.6 (iii) with the history retained for `B` (`exists_germLaw_of_isHistoryAvoidanceLocal`: `h⁰ = h₁ + Z`,
`Z` a zero-boundary GFF on `ℍ ∖ B = c.inv(ℍ ∖ K)` given `𝒜_B ∨ ℋ`); the same conditional law under `P[· | D]`
(`D ∈ 𝒜_B ∨ ℋ`); the pullback of `Z` is a zero-boundary GFF on `ℍ ∖ K` given `𝒜_B ∨ ℋ`
(`isCondZeroBoundaryGFF_pullField_sub`); the
transport of `h₁ + u₀` is `(𝒜_B ∨ ℋ)`-measurable and harmonic on `ℍ ∖ K` (`isHarmonicDistOn_chartTransport`); and
`isLocalSet_of_isCondZeroBoundaryGFF`. -/
theorem isLocalSet_cond_chart_of_isHistoryAvoidanceLocal {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[ℋ] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[ℋ] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom)
    {K : Ω → Set ℂ} (hKm : Measurable[ℋ, hittingSigma] K) (hK : ∀ ω, K ω ⊆ H ∧ IsOpen (H \ K ω))
    (hℋ : ℋ ≤ mΩ) (hBm : Measurable[ℋ, hittingSigma] fun ω => H \ (c ω).2.1 '' (H \ K ω))
    (hloc : IsHistoryAvoidanceLocal ℋ (fun ω => H \ (c ω).2.1 '' (H \ K ω)) (centredField h u₀) P)
    {D : Set Ω} (hD : MeasurableSet[germSigma (fun ω => H \ (c ω).2.1 '' (H \ K ω)) (centredField h u₀) ⊔ ℋ] D)
    (hPD : P D ≠ 0) (a k : ℝ) :
    IsLocalSet K (fun ω => Chart.chartTransport (hc ω) 1 a k (h ω)) (P[|D]) := by
  set B : Ω → Set ℂ := fun ω => H \ (c ω).2.1 '' (H \ K ω) with hBdef
  set h0 := centredField h u₀ with hh0def
  have himH : ∀ ω, (c ω).2.1 '' (H \ K ω) ⊆ H := fun ω =>
    (image_mono sdiff_subset).trans (hc ω).2.1.image_subset
  have hHB : ∀ ω, H \ B ω = (c ω).2.1 '' (H \ K ω) := fun ω => by
    simp only [hBdef, sdiff_sdiff_right_self, inter_eq_right.2 (himH ω)]
  have hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω) := fun ω =>
    ⟨sdiff_subset, by rw [hHB]; exact (hc ω).isOpen_image_of_subset (hK ω).2 sdiff_subset⟩
  have hBm' : Measurable[mΩ, hittingSigma] B := hBm.mono hℋ le_rfl
  have hh0m : Measurable h0 := measurable_centredField hhm u₀
  obtain ⟨h₁, hh₁, hharm, hcond⟩ :=
    exists_germLaw_of_isHistoryAvoidanceLocal hh0 hBm' hℋ hloc (ae_of_all _ hBc)
  have h𝒢 : germSigma B h0 ⊔ ℋ ≤ mΩ := sup_le (germSigma_le hBm' hh0m) hℋ
  have hℋ𝒢 : ℋ ≤ germSigma B h0 ⊔ ℋ := le_sup_right
  have : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure hPD
  have hac : P[|D] ≪ P := cond_absolutelyContinuous
  have hh₁m : Measurable h₁ := hh₁.mono (germSigma_le hBm' hh0m) le_rfl
  have hXm : Measurable fun ω => h0 ω - h₁ ω :=
    measurable_distOn_iff.2 fun φ => ((measurable_distOn_apply φ).comp hh0m).sub ((measurable_distOn_apply φ).comp hh₁m)
  -- the conditional law under `P[· | D]`
  have hcondD : IsCondZeroBoundaryGFF (P[|D]) (germSigma B h0 ⊔ ℋ) (fun ω => (c ω).2.1 '' (H \ K ω))
      fun ω => h0 ω - h₁ ω := by
    intro φ
    have hcov : Measurable[germSigma B h0 ⊔ ℋ] fun ω => zeroGFFTestCov (H \ relClosureH (B ω)) φ φ :=
      (measurable_comap_zeroGFFTestCov_compl B φ φ).mono ((comap_le_germSigma B h0).trans le_sup_left) le_rfl
    set c' : Ω → ℂ := fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (B ω)) φ φ) : ℝ) : ℂ)
      with hc'def
    have hc'm : StronglyMeasurable[germSigma B h0 ⊔ ℋ] c' :=
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hcov.const_mul _))).stronglyMeasurable
    have hcB : ∀ ω, c' ω = ((Real.exp (-(1 / 2) * zeroGFFTestCov ((c ω).2.1 '' (H \ K ω)) φ φ) : ℝ) : ℂ) :=
      fun ω => by simp only [c', relClosureH_eq (hBc ω).1 (hBc ω).2, hHB]
    have hcc' : (fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ B ω) φ φ) : ℝ) : ℂ)) =ᵐ[P] c' :=
      Eventually.of_forall fun ω => by simp only [hcB, hHB]
    have hc'i : Integrable c' P := (integrable_condExp.congr (hcond φ)).congr hcc'
    have hX : Integrable (fun ω => Complex.exp (Complex.I * (((h0 ω - h₁ ω) φ : ℝ) : ℂ))) P :=
      GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp hXm)
    have key := LocalExt.condExp_cond_ae_eq le_rfl h𝒢 hD hPD hX hc'm hc'i ((hcond φ).trans hcc')
    exact key.trans (Eventually.of_forall fun ω => hcB ω)
  -- pull back through the chart
  have hpull := isCondZeroBoundaryGFF_pullField_sub h𝒢 hc (fun z => hℋ𝒢 _ (hdom z))
    (fun z => (hfwd z).mono hℋ𝒢 le_rfl) (O := fun ω => H \ K ω) (fun ω => (hK ω).2) (fun _ => sdiff_subset) hXm
    hcondD
  -- the harmonic part
  set M : Ω → DistOn upperHalfPlaneOpens := fun ω => h₁ ω + SupercriticalConformalCovariance.GM24.smoothDist
    upperHalfPlaneOpens u₀ with hMdef
  have hMm : Measurable[germSigma B h0 ⊔ ℋ] M :=
    (Coupling.measurable_add_distOnConst _).comp (hh₁.mono le_sup_left le_rfl)
  have hh₁'m : Measurable[germSigma B h0 ⊔ ℋ] fun ω => Chart.chartTransport (hc ω) 1 a k (M ω) :=
    @Chart.measurable_chartTransport_random' Ω (germSigma B h0 ⊔ ℋ) c hc (fun z => hℋ𝒢 _ (hdom z))
      (fun z => (hfwd z).mono hℋ𝒢 le_rfl) (fun z => (hliftm z).mono hℋ𝒢 le_rfl) hliftc M hMm 1 a k
  have hdiff : ∀ ω, Chart.chartTransport (hc ω) 1 a k (h ω) - Chart.chartTransport (hc ω) 1 a k (M ω) =
      Chart.pullField (hc ω) (h0 ω - h₁ ω) := fun ω => by
    rw [Chart.chartTransport_sub, one_smul]
    congr 1
    simp only [hMdef, hh0def, centredField]
    abel
  refine isLocalSet_of_isCondZeroBoundaryGFF (P := P[|D]) h𝒢 (hKm.mono hℋ𝒢 le_rfl)
    (Chart.measurable_chartTransport_random' hc (fun z => hℋ _ (hdom z)) (fun z => (hfwd z).mono hℋ le_rfl)
      (fun z => (hliftm z).mono hℋ le_rfl) hliftc hhm 1 a k) hh₁'m (ae_of_all _ hK) ?_ ?_
  · filter_upwards [hac.ae_le hharm] with ω hω
    have hsm := isHarmonicDistOn_smoothDist hu₀
    have hMh : IsHarmonicDistOn (M ω) ((c ω).2.1 '' (H \ K ω)) := by
      rw [← hHB]
      exact Coupling.IsHarmonicDistOn.add' (hBc ω).2 hω (LocalSets.IsHarmonicDistOn.mono hsm sdiff_subset)
    exact isHarmonicDistOn_chartTransport (hc ω) (hliftc ω) (hlift ω) (hK ω).2 sdiff_subset hMh a k
  · intro φ
    simp only [hdiff]
    exact hpull φ

end Transport

end InteractingSLE.Sec7.Lemma72C
