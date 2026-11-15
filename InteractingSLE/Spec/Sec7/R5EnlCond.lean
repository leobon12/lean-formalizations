/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInKernelStepLaw
import InteractingSLE.Spec.Sec5.Aux61FibKTilt

/-!
# R.5's old-chart increment law conditioned on the reference event

Packet PROVE-R5-ENLARGED. Specification §5.5, Lemma R.5's proof (`source/spec/p433-480.md` L1014, p. 475: "For each
`s`, apply the nested marked local-set law to the enlarged stop `T ∨ s`, exactly as in Aux. 35"), and Aux. 35's
proof (`source/spec/p145-192.md` L955–L960, `p193-240.md` L5–L32, pp. 192–194: "Conditionally on `𝒢`, the first
residual field is a zero-boundary GFF in `D ∖ B` … the remaining set `A ∖ B` … is a local-set reveal of that
conditional GFF").

**Why a conditioned law.** `PocketStopSide.HasOldChartIncrementLaw P M old current gOld gNow` asks for a residual
field that is a zero-boundary GFF under `P` itself. R.5's reference residual `h − 𝒞_B` read through the reference
chart is a zero-boundary GFF only *conditionally on the reference record*, and only on the event `G` where the
reference chart exists (on the R.7 and late tests, off the live event the normalized reference set is all of `ℍ`, so
no chart onto `ℍ` exists there and the conditional residual is `0`). Gluing it with anything off `G` does not give a
`P`-GFF in general. The source's statement is conditional ("Conditionally on `𝒢`"). Hence the conditioned form:

* `HasOldChartIncrementLawOn P M old current gOld gNow` — for some measurable `G ⊇ M`, the increment law holds under
  `P[· | G]`;
* `hasOldChartIncrementLawOn_of_hasOldChartIncrementLaw` — the unconditioned law implies it (`G = univ`);
* **`ae_physical_germ_of_old_chart_increment_law_on`** — the conditioned law has the same consumer conclusion as
  `ae_physical_germ_of_old_chart_increment_law` (the zero physical germ on every certified old collar), `P`-a.s.;
* `HasOldChartIncrementLaw.congr_on` — the law only sees its data on `M`, up to null sets;
* `isCondZeroBoundaryGFF_cond` — a retained kernel given `𝒢` stays a kernel under `P[· | G]` for `G ∈ 𝒢`.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.R5Enl

open LocalSets PocketStopSide

/-! ### Almost sure statements under a conditioned measure -/

section Measure

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- A `P[· | G]`-almost sure property holds `P`-almost surely on `G`. -/
theorem ae_of_ae_cond [IsFiniteMeasure P] {G : Set Ω} (hG : MeasurableSet G) {p : Ω → Prop}
    (h : ∀ᵐ ω ∂P[|G], p ω) : ∀ᵐ ω ∂P, ω ∈ G → p ω := by
  rw [← ae_restrict_iff' hG]
  by_cases hP : P G = 0
  · rw [Measure.restrict_eq_zero.2 hP, ae_zero]
    exact eventually_bot
  · have e : P[|G] = (P G)⁻¹ • P.restrict G := rfl
    rw [e, Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.2 (measure_ne_top P G))] at h
    exact h

/-- A property holding `P`-almost surely on a measurable `G` holds `P[· | G]`-almost surely. -/
theorem ae_cond_of_ae {G : Set Ω} (hG : MeasurableSet G) {p : Ω → Prop}
    (h : ∀ᵐ ω ∂P, ω ∈ G → p ω) : ∀ᵐ ω ∂P[|G], p ω := by
  filter_upwards [cond_absolutelyContinuous.ae_le h, ae_cond_mem hG] with ω h1 h2 using h1 h2

/-- **A retained Gaussian kernel survives conditioning on an event of its record.** -/
theorem isCondZeroBoundaryGFF_cond [IsFiniteMeasure P] (h𝒢 : 𝒢 ≤ mΩ)
    {G : Set Ω} (hG : MeasurableSet[𝒢] G) {U U' : Ω → Set ℂ} {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) (hK : IsCondZeroBoundaryGFF P 𝒢 U X) (hU : ∀ᵐ ω ∂P, ω ∈ G → U ω = U' ω) :
    IsCondZeroBoundaryGFF (P[|G]) 𝒢 U' X := by
  intro φ
  have hf : Integrable (fun ω => Complex.exp (Complex.I * (X ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hX)
  have h1 := Sec5.Aux61FibK.condExp_cond_ae_eq h𝒢 hG hf
  filter_upwards [h1, cond_absolutelyContinuous.ae_le (hK φ), ae_cond_of_ae (h𝒢 _ hG) hU]
    with ω e1 e2 e3
  rw [e1, e2, e3]

end Measure

/-! ### The conditioned law -/

section Law

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **R.5's old-chart increment law conditioned on a reference event** `G ⊇ M`: under `P[· | G]` the residual
increment law `HasOldChartIncrementLaw` holds (vacuous when `P G = 0`). -/
def HasOldChartIncrementLawOn (P : Measure Ω) (M : Set Ω) (old current : Ω → Chart)
    (gOld gNow : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∃ G : Set Ω, MeasurableSet G ∧ M ⊆ G ∧ ∀ hP : IsProbabilityMeasure (P[|G]),
    @HasOldChartIncrementLaw Ω mΩ (P[|G]) hP M old current gOld gNow

/-- The unconditioned law is the conditioned law with `G = Ω`. -/
theorem hasOldChartIncrementLawOn_of_hasOldChartIncrementLaw {P : Measure Ω} [IsProbabilityMeasure P]
    {M : Set Ω} {old current : Ω → Chart} {gOld gNow : Ω → DistOn upperHalfPlaneOpens}
    (h : HasOldChartIncrementLaw P M old current gOld gNow) :
    HasOldChartIncrementLawOn P M old current gOld gNow := by
  refine ⟨univ, MeasurableSet.univ, subset_univ M, ?_⟩
  have e : P[|univ] = P := cond_univ P
  rw [e]
  intro _
  exact h

/-- Pulling back along equal conformal charts gives equal fields. -/
theorem pullField_congr {c c' : Chart} (hc : c.IsConformal) (hc' : c'.IsConformal) (e : c = c')
    (X : DistOn upperHalfPlaneOpens) : Chart.pullField hc X = Chart.pullField hc' X := by
  subst e
  rfl

/-- **The increment law sees its data only on `M`, up to null sets.** -/
theorem HasOldChartIncrementLaw.congr_on {P : Measure Ω} [IsProbabilityMeasure P] {M : Set Ω}
    {old old' current current' : Ω → Chart} {gOld gOld' gNow gNow' : Ω → DistOn upperHalfPlaneOpens}
    (h : HasOldChartIncrementLaw P M old current gOld gNow)
    (he : ∀ᵐ ω ∂P, ω ∈ M → old ω = old' ω ∧ ((current ω).dom : Set ℂ) = (current' ω).dom ∧
      gOld ω = gOld' ω ∧ gNow ω = gNow' ω) :
    HasOldChartIncrementLaw P M old' current' gOld' gNow' := by
  obtain ⟨A, hRes, gInc, hZero, hMeas, hReg, hMean, hId⟩ := h
  refine ⟨A, hRes, gInc, hZero, hMeas, hReg, hMean, ?_⟩
  filter_upwards [hId, he] with ω hω heω hM
  obtain ⟨hSet, hField⟩ := hω hM
  obtain ⟨eo, ec, eg, en⟩ := heω hM
  refine ⟨?_, fun hc => ?_⟩
  · rw [hSet]
    simp only [oldChartAddedSet, hM, ↓reduceIte, eo, ec]
  · have hc0 : (old ω).IsConformal := eo ▸ hc
    rw [hField hc0, pullField_congr hc0 hc eo, eg, en]

/-- **The conditioned law sees its data only on `M`, up to null sets.** -/
theorem HasOldChartIncrementLawOn.congr_on {P : Measure Ω} [IsFiniteMeasure P] {M : Set Ω}
    {old old' current current' : Ω → Chart} {gOld gOld' gNow gNow' : Ω → DistOn upperHalfPlaneOpens}
    (h : HasOldChartIncrementLawOn P M old current gOld gNow)
    (he : ∀ᵐ ω ∂P, ω ∈ M → old ω = old' ω ∧ ((current ω).dom : Set ℂ) = (current' ω).dom ∧
      gOld ω = gOld' ω ∧ gNow ω = gNow' ω) :
    HasOldChartIncrementLawOn P M old' current' gOld' gNow' := by
  obtain ⟨G, hGm, hMG, hlaw⟩ := h
  exact ⟨G, hGm, hMG, fun hP => HasOldChartIncrementLaw.congr_on (hlaw hP)
    (cond_absolutelyContinuous.ae_le he)⟩

/-- **The conditioned law gives R.5's zero physical germ** on every certified old incident collar,
simultaneously in all representatives and all real accesses, `P`-almost surely on `M` (the consumer conclusion of
`ae_physical_germ_of_old_chart_increment_law`). -/
theorem ae_physical_germ_of_old_chart_increment_law_on {P : Measure Ω} [IsProbabilityMeasure P]
    {M : Set Ω} {old current : Ω → Chart} {gOld gNow : Ω → DistOn upperHalfPlaneOpens}
    (hOld : ∀ ω ∈ M, (old ω).IsConformal)
    (hCurrent : ∀ ω ∈ M, (current ω).IsConformal)
    (hInclusion : ∀ ω ∈ M, ((current ω).dom : Set ℂ) ⊆ (old ω).dom)
    (hLaw : HasOldChartIncrementLawOn P M old current gOld gNow) :
    ∀ᵐ ω ∂P, ω ∈ M → ∀ vOld vNow : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vOld (old ω).dom →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (old ω).dom →
        gOld ω φ = ∫ z, vOld z * φ z) →
      InnerProductSpace.HarmonicOnNhd vNow (current ω).dom →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (current ω).dom →
        gNow ω φ = ∫ z, vNow z * φ z) → ∀ (ξ x r : ℝ),
      0 < r → (old ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (current ω).dom →
      Tendsto (fun z => (old ω).1 ((current ω).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
      Tendsto (fun z => vNow ((current ω).2.1 z) - vOld ((current ω).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨G, hGm, hMG, hlaw⟩ := hLaw
  by_cases hPG : P G = 0
  · have hnull : ∀ᵐ ω ∂P, ω ∉ G := measure_eq_zero_iff_ae_notMem.1 hPG
    filter_upwards [hnull] with ω hω hM
    exact absurd (hMG hM) hω
  · have : IsProbabilityMeasure (P[|G]) := cond_isProbabilityMeasure hPG
    have h := ae_physical_germ_of_old_chart_increment_law (P := P[|G]) hOld hCurrent hInclusion
      (hlaw inferInstance)
    filter_upwards [ae_of_ae_cond hGm h] with ω hω hM
    exact hω (hMG hM) hM

end Law

end InteractingSLE.Sec7.R5Enl
