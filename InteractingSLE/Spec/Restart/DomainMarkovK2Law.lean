/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovK2Data

/-!
# K2, part 2: the protected-kernel law of a general continuation under the regular conditional law

Packet PROVE-DOMAINMARKOV5, item (K2), the conditional-law half. PROVE-DOMAINMARKOV2 proved, for the restart of one
coupling at a stopping time, that the protected-kernel law of the restarted field at the dyadic times
(`IsDyadicSampled`) holds under almost every conditional law `condExpKernel P 𝓓_T ω₀`. Here the same is done for an
**arbitrary** conditioning σ-algebra `𝒢`, live event `F ∈ 𝒢`, continuation `(W, VL, VR)` with lifetime `ζ` adapted to
a `P`-side filtration `𝓗` with `𝒢 ≤ 𝓗 0`, and field `X`, from the `P`-side input

* `HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X`: on every event `D ∈ 𝓗_q` contained (almost surely) in `F` and in the
  avoidance event `{q < ζ, supp ψ ∩ K_q = ∅}`, `∫_D e^{i X(ψ)} dP = ∫_D cfAt_q(ψ) dP` (the conditional law of `X`
  off the continuation hull at a deterministic time, given `𝓗_q`).

Results:

* one measure, any filtration `𝓖` generated at time `q` by a π-system (copies of PROVE-DOMAINMARKOV2's lemmas with the
  restart objects replaced by general weak processes): `condExp_safeU_indicator_eq_of_pi` (Dynkin),
  `ae_condExp_cexp_eq_cfAt_of_pi` (all test functions, by local Gaussian laws), `setIntegral_cexp_eq_cfAt_of_pi`,
  `nullAugmented_le_of_agree`, **`isDyadicSampled_of_agree_pi`**;
* the transfer: `ae_forall_setIntegral_piClosure_eq_k` (countably many identities under almost every `ν`);
* **`ae_isDyadicSampled_k`**: for `P`-almost every `ω₀ ∈ F`, under `ν = condExpKernel P 𝒢 ω₀`, every measurable
  version of the modified continuation (equal to it `ν`-almost surely at every time) is dyadically sampled with `X`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.DomainMarkov.K2

open Coupling Coupling.MartMeans2 Ito Sec7 Sec7.Aux122Disint Sec2.Restart Sec5.Markov LocalExt

/-! ### One measure, one filtration -/

section One

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {X : Ω → DistOn upperHalfPlaneOpens} {𝓖 : Filtration ℝ≥0 mΩ} {ν : Measure Ω}

/-- The weak path properties at every `ω`. -/
abbrev IsWeakEverywhere (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) : Prop :=
  ∀ ω, IsWeakPath (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)

variable (hweak : IsWeakEverywhere W VL VR ζ) (hWa : AdaptedBefore 𝓖 ζ W)
  (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ j, AdaptedBefore 𝓖 ζ (VR j))

include hweak in
omit mΩ in
theorem norm_safeU_indicator_cfAt_le (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) (ω : Ω) :
    ‖(safeU W ζ univ ψ q).indicator (cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 fun _ => q) ω‖ ≤ 1 := by
  by_cases hω : ω ∈ safeU W ζ univ ψ q
  · rw [indicator_of_mem hω]
    exact norm_cfAt_le_one_of_mem_safeU' hweak _ ψ hω
  · rw [indicator_of_notMem hω, norm_zero]
    exact zero_le_one

include hweak hWa hVLa hVRa in
theorem measurable_safeU_indicator_cfAt_bhe (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) :
    Measurable[𝓖 q] ((safeU W ζ univ ψ q).indicator (cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 fun _ => q)) :=
  measurable_safeU_indicator_cfAt_of_weak hweak hWa MeasurableSet.univ _
    (fun ω s => isBoundedHarmonicExtension_bheProc ω s) hVLa hVRa ψ q

variable [IsProbabilityMeasure ν]

include hweak hWa hVLa hVRa in
/-- **Dynkin under one measure.** If the identity `∫_A 1_S e^{iX(ψ)} = ∫_A 1_S cfAt q` holds on a π-system containing
`univ` and generating `𝓖 q`, then `ν[1_S e^{iX(ψ)} | 𝓖 q] = 1_S cfAt q`. -/
theorem condExp_safeU_indicator_eq_of_pi (hX : Measurable X) (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0)
    {S : Set (Set Ω)} (hgen : 𝓖 q = MeasurableSpace.generateFrom S) (hpi : IsPiSystem S) (huS : univ ∈ S)
    (hall : ∀ A ∈ S, ∫ ω in A, (safeU W ζ univ ψ q).indicator
        (fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ))) ω ∂ν =
      ∫ ω in A, (safeU W ζ univ ψ q).indicator (cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 fun _ => q) ω ∂ν) :
    ν[(safeU W ζ univ ψ q).indicator (fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ))) | 𝓖 q] =ᵐ[ν]
      (safeU W ζ univ ψ q).indicator (cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 fun _ => q) := by
  have hm : 𝓖 q ≤ mΩ := 𝓖.le q
  have hXm : Measurable fun ω => X ω ψ := (LQGMetric.measurable_distOn_apply ψ).comp hX
  have hS : MeasurableSet[𝓖 q] (safeU W ζ univ ψ q) := measurableSet_safeU hweak hWa MeasurableSet.univ ψ q
  have hXi : Integrable ((safeU W ζ univ ψ q).indicator
      fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ))) ν :=
    (GFF.integrable_exp_I_mul hXm).indicator (hm _ hS)
  have hYm := measurable_safeU_indicator_cfAt_bhe (κ := κ) (ρL := ρL) (ρR := ρR) hweak hWa hVLa hVRa ψ q
  have hYi : Integrable ((safeU W ζ univ ψ q).indicator
      (cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 fun _ => q)) ν :=
    Integrable.of_bound (hYm.mono hm le_rfl).aestronglyMeasurable 1
      (Eventually.of_forall (norm_safeU_indicator_cfAt_le hweak ψ q))
  have hdyn : ∀ A, MeasurableSet[𝓖 q] A →
      ∫ ω in A, (safeU W ζ univ ψ q).indicator (fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ))) ω ∂ν =
        ∫ ω in A, (safeU W ζ univ ψ q).indicator (cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 fun _ => q) ω ∂ν :=
    fun A hA => setIntegral_eq_of_isPiSystem hXi hYi hm hgen hpi
      (by simpa only [Measure.restrict_univ] using hall univ huS) hall hA
  exact (ae_eq_condExp_of_forall_setIntegral_eq hm hXi (fun s _ _ => hYi.integrableOn)
    (fun s hs _ => (hdyn s hs).symm) hYm.aestronglyMeasurable).symm

include hweak hWa hVLa hVRa in
/-- **Every test function, under one measure.** If the identities of `condExp_safeU_indicator_eq_of_pi` hold at a time
`q` for the countably many test functions `ratTest p`, then for every test function `ψ`, `ν`-almost surely on the
avoidance event, `ν[e^{iX(ψ)} | 𝓖 q] = cfAt q` (local Gaussian laws, `condExp_cexp_ae_eq_of_local_countable`). -/
theorem ae_condExp_cexp_eq_cfAt_of_pi (hX : Measurable X) (q : ℝ≥0) {S : Set (Set Ω)}
    (hgen : 𝓖 q = MeasurableSpace.generateFrom S) (hpi : IsPiSystem S) (huS : univ ∈ S)
    (hall : ∀ (p : RatIdx), ∀ A ∈ S,
      ∫ ω in A, (safeU W ζ univ (ratTest upperHalfPlaneOpens p) q).indicator
          (fun ω => Complex.exp (Complex.I * (X ω (ratTest upperHalfPlaneOpens p) : ℂ))) ω ∂ν =
        ∫ ω in A, (safeU W ζ univ (ratTest upperHalfPlaneOpens p) q).indicator
          (cfAt κ W (bheProc κ ρL ρR W VL VR) (ratTest upperHalfPlaneOpens p) 1 fun _ => q) ω ∂ν)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂ν, ω ∈ avoidSet W ζ ψ q →
      ν[fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) | 𝓖 q] ω =
        cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q) ω := by
  classical
  have hm : 𝓖 q ≤ mΩ := 𝓖.le q
  -- the random open sets
  set U : Ω → Set ℂ := fun ω => if (q : ℝ≥0∞) < ζ ω then H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q else ∅
    with hUdef
  have hUo : ∀ ω, IsOpen (U ω) := fun ω => by
    by_cases hq : (q : ℝ≥0∞) < ζ ω
    · simp only [hUdef, hq, ↓reduceIte]
      exact isOpen_H_diff_fwdHull_rpath (w := fun t => W t ω) (hweak ω).2.1 hq
    · simp only [hUdef, hq, ↓reduceIte]
      exact isOpen_empty
  have hUH : ∀ ω, U ω ⊆ H := fun ω => by
    by_cases hq : (q : ℝ≥0∞) < ζ ω
    · simp only [hUdef, hq, ↓reduceIte]
      exact sdiff_subset
    · simp only [hUdef, hq, ↓reduceIte]
      exact empty_subset _
  -- the mean
  set m : Ω → ℂ → ℝ := fun ω z => couplingMean κ (fun s : ℝ => W s.toNNReal ω) q
    (bheProc κ ρL ρR W VL VR ω q) z with hmdef
  have hmc : ∀ ω, ContinuousOn (m ω) (U ω) := fun ω => by
    by_cases hq : (q : ℝ≥0∞) < ζ ω
    · have hr := continuousOn_rpath (u := fun t => W t ω) (hweak ω).2.1 hq
      have hcm := continuousOn_couplingMean κ hr (isBoundedHarmonicExtension_bheProc (κ := κ) (ρL := ρL)
        (ρR := ρR) (W := W) (VL := VL) (VR := VR) ω q).1
      refine hcm.mono fun z hz => ?_
      simp only [hUdef, hq, ↓reduceIte] at hz
      exact mem_hullDom hr hz.1 hz.2
    · simp only [hUdef, hq, ↓reduceIte]
      exact continuousOn_empty _
  set Ψ : Ω → TestOn upperHalfPlaneOpens → ℂ := fun ω φ =>
    Complex.exp (Complex.I * ((∫ z, m ω z * φ z : ℝ) : ℂ) -
      (((1 / 2 : ℝ) * zeroGFFTestCov (U ω) φ φ : ℝ) : ℂ)) with hΨdef
  have hΨ : ∀ᵐ ω ∂ν, ∀ R : Opens ℂ, (R : Set ℂ) ⊆ U ω → ∃ μ : Measure (DistOn R), IsProbabilityMeasure μ ∧
      ∀ ψ : TestOn R, ∫ v, Complex.exp (Complex.I * (v ψ : ℂ)) ∂μ =
        Ψ ω (GFF.testIncl R upperHalfPlaneOpens ψ) := Eventually.of_forall fun ω R hR => by
    have hRH : R ≤ upperHalfPlaneOpens := fun x hx => hUH ω (hR hx)
    obtain ⟨μ, hμP, hμ⟩ := exists_gaussLocalLaw (U := ⟨U ω, hUo ω⟩) (hUH ω) (R := R) hR
      (((hmc ω).mono hR).locallyIntegrableOn R.isOpen.measurableSet)
    refine ⟨μ, hμP, fun ψ => ?_⟩
    rw [hμ ψ, hΨdef]
    simp only [GFF.coe_testIncl hRH ψ, Opens.coe_mk]
  -- on the avoidance event, `cfAt` is `Ψ`
  have hcfΨ : ∀ (φ : TestOn upperHalfPlaneOpens) (ω : Ω), ω ∈ avoidSet W ζ φ q →
      cfAt κ W (bheProc κ ρL ρR W VL VR) φ 1 (fun _ => q) ω = Ψ ω φ := by
    intro φ ω hav
    obtain ⟨hq, hdis⟩ := hav
    simp only [hΨdef, hmdef, hUdef, hq, ↓reduceIte, cfAt]
    rw [← WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov (w := fun t => W t ω)
      (hweak ω).2.1 (hweak ω).1 hq φ hdis]
    congr 1
    push_cast
    ring
  -- the countably many identities as conditional expectations
  have hkey : ∀ φ : TestOn upperHalfPlaneOpens,
      (∀ A ∈ S, ∫ ω in A, (safeU W ζ univ φ q).indicator
            (fun ω => Complex.exp (Complex.I * (X ω φ : ℂ))) ω ∂ν =
          ∫ ω in A, (safeU W ζ univ φ q).indicator
            (cfAt κ W (bheProc κ ρL ρR W VL VR) φ 1 fun _ => q) ω ∂ν) →
      ∀ᵐ ω ∂ν, ω ∈ avoidSet W ζ φ q →
        ν[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | 𝓖 q] ω =
          cfAt κ W (bheProc κ ρL ρR W VL VR) φ 1 (fun _ => q) ω := by
    intro φ hφ
    have h1 := condExp_safeU_indicator_eq_of_pi hweak hWa hVLa hVRa hX φ q hgen hpi huS hφ
    have hXi : Integrable (fun ω => Complex.exp (Complex.I * (X ω φ : ℂ))) ν :=
      GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hX)
    have h2 := condExp_indicator hXi (measurableSet_safeU hweak hWa MeasurableSet.univ φ q)
    filter_upwards [h1, h2] with ω h1ω h2ω hav
    have hωS := mem_safeU_of_mem_avoidSet hweak φ (mem_univ ω) hav
    rw [h2ω, indicator_of_mem hωS, indicator_of_mem hωS] at h1ω
    exact h1ω
  have hcond : ∀ p : RatIdx, ∀ᵐ ω ∂ν, tsupport (ratTest upperHalfPlaneOpens p) ⊆ U ω →
      ν[fun ω => Complex.exp (Complex.I * (X ω (ratTest upperHalfPlaneOpens p) : ℂ)) | 𝓖 q] ω =
        Ψ ω (ratTest upperHalfPlaneOpens p) := by
    intro p
    by_cases hφ0 : ratTest upperHalfPlaneOpens p = 0
    · rw [hφ0]
      have e : (fun ω => Complex.exp (Complex.I * (X ω 0 : ℂ))) = fun _ => (1 : ℂ) := by
        funext ω; simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      have h1 : ν[fun ω => Complex.exp (Complex.I * (X ω 0 : ℂ)) | 𝓖 q] = fun _ => (1 : ℂ) := by
        rw [e, condExp_const hm]
      refine Eventually.of_forall fun ω _ => ?_
      rw [h1]
      have e2 : ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = (0 : ℂ → ℝ) := rfl
      simp only [hΨdef, e2, Pi.zero_apply, mul_zero, integral_zero, Complex.ofReal_zero,
        GFF.zeroGFFTestCov_zero_zero, sub_zero, Complex.exp_zero]
    · filter_upwards [hkey _ (hall p)] with ω hω hsupp
      have hq : (q : ℝ≥0∞) < ζ ω := by
        by_contra hq
        simp only [hUdef, hq, ↓reduceIte, subset_empty_iff] at hsupp
        exact hφ0 (TestFunction.ext fun z => image_eq_zero_of_notMem_tsupport (by rw [hsupp]; exact id))
      have hav : ω ∈ avoidSet W ζ (ratTest upperHalfPlaneOpens p) q := by
        refine ⟨hq, Set.disjoint_left.2 fun z hz hzK => ?_⟩
        have := hsupp hz
        simp only [hUdef, hq, ↓reduceIte] at this
        exact this.2 hzK
      rw [hω hav, hcfΨ _ ω hav]
  have hall' := condExp_cexp_ae_eq_of_local_countable hm hX hUo hUH hΨ hcond ψ
  filter_upwards [hall'] with ω hω hav
  have hsupp : tsupport ψ ⊆ U ω := by
    obtain ⟨hq, hdis⟩ := hav
    simp only [hUdef, hq, ↓reduceIte]
    exact fun z hz => ⟨ψ.tsupport_subset hz, fun hK => Set.disjoint_left.1 hdis hz hK⟩
  rw [hω hsupp, hcfΨ ψ ω hav]

include hweak hWa hVLa hVRa in
/-- **The set-integral form under one measure**, for every test function and every event that is `ν`-almost surely
an event of `𝓖 q` inside the avoidance event. -/
theorem setIntegral_cexp_eq_cfAt_of_pi (hX : Measurable X) (q : ℝ≥0) {S : Set (Set Ω)}
    (hgen : 𝓖 q = MeasurableSpace.generateFrom S) (hpi : IsPiSystem S) (huS : univ ∈ S)
    (hall : ∀ (p : RatIdx), ∀ A ∈ S,
      ∫ ω in A, (safeU W ζ univ (ratTest upperHalfPlaneOpens p) q).indicator
          (fun ω => Complex.exp (Complex.I * (X ω (ratTest upperHalfPlaneOpens p) : ℂ))) ω ∂ν =
        ∫ ω in A, (safeU W ζ univ (ratTest upperHalfPlaneOpens p) q).indicator
          (cfAt κ W (bheProc κ ρL ρR W VL VR) (ratTest upperHalfPlaneOpens p) 1 fun _ => q) ω ∂ν)
    (ψ : TestOn upperHalfPlaneOpens) {A : Set Ω}
    (hA'ex : ∃ A', MeasurableSet[𝓖 q] A' ∧ A =ᵐ[ν] A')
    (hAav : ∀ᵐ ω ∂ν, ω ∈ A → ω ∈ avoidSet W ζ ψ q) :
    ∫ ω in A, Complex.exp (Complex.I * (X ω ψ : ℂ)) ∂ν =
      ∫ ω in A, cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q) ω ∂ν := by
  obtain ⟨A', hA', hAA'⟩ := hA'ex
  have hm : 𝓖 q ≤ mΩ := 𝓖.le q
  have hc := ae_condExp_cexp_eq_cfAt_of_pi hweak hWa hVLa hVRa hX q hgen hpi huS hall ψ
  have hXi : Integrable (fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ))) ν :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply ψ).comp hX)
  have hA'av : ∀ᵐ ω ∂ν, ω ∈ A' → ω ∈ avoidSet W ζ ψ q := by
    filter_upwards [hAav, hAA'] with ω h1 h2 hω
    exact h1 (by rw [h2]; exact hω)
  rw [setIntegral_congr_set hAA', setIntegral_congr_set hAA', ← setIntegral_condExp hm hXi hA']
  refine setIntegral_congr_ae (hm _ hA') ?_
  filter_upwards [hc, hA'av] with ω h1 h2 hω using h1 (h2 hω)

omit [IsProbabilityMeasure ν] in
include hWa hVLa hVRa in
/-- **Events of the augmented killed driving filtration of versions are almost surely events of `𝓖`**, for versions
agreeing almost surely with the processes before the lifetime. -/
theorem nullAugmented_le_of_agree {W' : ℝ≥0 → Ω → ℝ} {VL' : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR' : Fin nR → ℝ≥0 → Ω → ℝ} (hX' : IsMeasurableKilledDriving W' VL' VR' ζ)
    (hagree : ∀ᵐ ω ∂ν, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W' t ω = W t ω ∧
      (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω) (q : ℝ≥0) :
    nullAugmented (killedDrivingFiltration hX') ν q ≤ eventuallyMeasurableSpace (𝓖 q) (ae ν) := by
  have hXZ : IsMeasurableKilledDriving W VL VR ζ := isMeasurableKilledDriving_of_adaptedBefore hWa hVLa hVRa
  have hkZ := killedDrivingFiltration_le hWa hVLa hVRa hXZ
  refine sup_le (MeasurableSpace.generateFrom_le ?_) (MeasurableSpace.generateFrom_le ?_)
  · rintro _ ⟨r, hrq, B, hB, rfl⟩
    refine ⟨{ω | (r : ℝ≥0∞) < ζ ω ∧ (W r ω, fun i => VL i r ω, fun j => VR j r ω) ∈ B},
      hkZ q _ (MeasurableSpace.measurableSet_generateFrom ⟨r, hrq, B, hB, rfl⟩), ?_⟩
    filter_upwards [hagree] with ω hω
    change ((r : ℝ≥0∞) < ζ ω ∧ _ ∈ B) = ((r : ℝ≥0∞) < ζ ω ∧ _ ∈ B)
    by_cases hr : (r : ℝ≥0∞) < ζ ω
    · obtain ⟨h1, h2, h3⟩ := hω r hr
      have e2 : (fun i => VL' i r ω) = fun i => VL i r ω := funext h2
      have e3 : (fun j => VR' j r ω) = fun j => VR j r ω := funext h3
      rw [h1, e2, e3]
    · simp only [hr, false_and]
  · rintro s ⟨-, hs0⟩
    exact ⟨∅, @MeasurableSet.empty _ (𝓖 q), ae_eq_empty.2 hs0⟩

include hweak hWa hVLa hVRa in
/-- **The dyadic protected-kernel law for versions**, under one measure: if the identities hold at every dyadic time
for the test functions `ratTest p` on π-systems generating `𝓖`, then every version agreeing `ν`-almost surely, at every
time, with the processes is dyadically sampled with `X`. -/
theorem isDyadicSampled_of_agree_pi (hX : Measurable X) {S : ℝ≥0 → Set (Set Ω)}
    (hgen : ∀ q, 𝓖 q = MeasurableSpace.generateFrom (S q)) (hpi : ∀ q, IsPiSystem (S q))
    (huS : ∀ q, univ ∈ S q)
    (hall : ∀ (n k : ℕ) (p : RatIdx), ∀ A ∈ S (dyT n k),
      ∫ ω in A, (safeU W ζ univ (ratTest upperHalfPlaneOpens p) (dyT n k)).indicator
          (fun ω => Complex.exp (Complex.I * (X ω (ratTest upperHalfPlaneOpens p) : ℂ))) ω ∂ν =
        ∫ ω in A, (safeU W ζ univ (ratTest upperHalfPlaneOpens p) (dyT n k)).indicator
          (cfAt κ W (bheProc κ ρL ρR W VL VR) (ratTest upperHalfPlaneOpens p) 1 fun _ => dyT n k) ω ∂ν)
    {W' : ℝ≥0 → Ω → ℝ} {VL' : Fin nL → ℝ≥0 → Ω → ℝ} {VR' : Fin nR → ℝ≥0 → Ω → ℝ}
    (hX' : IsMeasurableKilledDriving W' VL' VR' ζ)
    (hagree : ∀ᵐ ω ∂ν, ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω) :
    IsDyadicSampled κ W' (bheProc κ ρL ρR W' VL' VR') ν hX' X := by
  intro ψ n k A hA hAav
  set q := dyT n k
  have hle := nullAugmented_le_of_agree hWa hVLa hVRa hX'
    (hagree.mono fun ω hω t _ => hω t) q
  obtain ⟨A', hA', hAA'⟩ := hle _ hA
  have hAm : MeasurableSet A := (nullAugmented (killedDrivingFiltration hX') ν).le q _ hA
  -- pathwise agreement of the avoidance events and of `cfAt`
  have hpath : ∀ᵐ ω ∂ν, (fun s : ℝ => W' s.toNNReal ω) = (fun s : ℝ => W s.toNNReal ω) ∧
      bheProc κ ρL ρR W' VL' VR' ω q = bheProc κ ρL ρR W VL VR ω q := by
    filter_upwards [hagree] with ω hω
    refine ⟨funext fun s => (hω _).1, ?_⟩
    obtain ⟨h1, h2, h3⟩ := hω q
    simp only [bheProc, h1, h2, h3]
  have hAav' : ∀ᵐ ω ∂ν, ω ∈ A → ω ∈ avoidSet W ζ ψ q := by
    filter_upwards [hpath] with ω hω hωA
    have h := hAav hωA
    simp only [avoidSet, mem_ofPred_eq] at h ⊢
    rw [← hω.1]
    exact h
  rw [setIntegral_cexp_eq_cfAt_of_pi hweak hWa hVLa hVRa hX q (hgen q) (hpi q) (huS q) (hall n k) ψ
    ⟨A', hA', hAA'⟩ hAav']
  refine setIntegral_congr_ae hAm ?_
  filter_upwards [hpath] with ω hω _
  simp only [cfAt]
  rw [hω.1, hω.2]

end One

/-! ### The `P`-side input and the transfer to the regular conditional law -/

section Transfer

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {N F : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens} {𝓗 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {ω : Ω}

/-- **`P`-side input (S): the conditional law of the field off the continuation hull at deterministic times.** On
every event `D ∈ 𝓗_q` that is almost surely contained in the live event `F` and in the avoidance event
`{q < ζ, supp ψ ∩ K_q = ∅}` of the continuation, `∫_D e^{i X(ψ)} dP = ∫_D cfAt_q(ψ) dP`, where
`cfAt_q(ψ) = exp(i ∫ 𝔥_q ψ − ½ E_q(ψ))` is the Gaussian characteristic functional with the coupling mean `𝔥_q` of the
continuation's current word and the Loewner–Green energy of its hull (Theorem 1.1's conditional-law clause at a
deterministic time, in the continuation's own coordinates). -/
def HasSafeLaw (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (P : Measure Ω) (𝓗 : Filtration ℝ≥0 mΩ) (F : Set Ω)
    (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (X : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) (D : Set Ω), MeasurableSet[𝓗 q] D →
    (∀ᵐ ω ∂P, ω ∈ D → ω ∈ F ∧ ω ∈ avoidSet W ζ ψ q) →
    ∫ ω in D, Complex.exp (Complex.I * (X ω ψ : ℂ)) ∂P =
      ∫ ω in D, cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q) ω ∂P

omit mΩ in
/-- Off `N`, on `F`, the modified continuation has the same avoidance events and the same `cfAt`. -/
theorem kW_path_eq (hωN : ω ∉ N) (hωF : ω ∈ F) :
    (fun s : ℝ => kW N F W VL VR s.toNNReal ω) = (fun s : ℝ => W s.toNNReal ω) :=
  funext fun _ => kW_eq hωN hωF _

omit mΩ in
theorem bheProc_k_eq (hωN : ω ∉ N) (hωF : ω ∈ F) (s : ℝ≥0) :
    bheProc κ ρL ρR (kW N F W VL VR) (kVL N F W VL VR) (kVR N F W VL VR) ω s = bheProc κ ρL ρR W VL VR ω s := by
  simp only [bheProc, kW_eq hωN hωF, kVL_eq hωN hωF, kVR_eq hωN hωF]

omit mΩ in
theorem mem_avoidSet_k_iff (hωN : ω ∉ N) (hωF : ω ∈ F) (ψ : ℂ → ℝ) (q : ℝ≥0) :
    ω ∈ avoidSet (kW N F W VL VR) ζ ψ q ↔ ω ∈ avoidSet W ζ ψ q := by
  simp only [avoidSet, mem_ofPred_eq, kW_path_eq hωN hωF]

omit mΩ in
theorem cfAt_k_eq (hωN : ω ∉ N) (hωF : ω ∈ F) (ψ : ℂ → ℝ) (q : ℝ≥0) :
    cfAt κ (kW N F W VL VR) (bheProc κ ρL ρR (kW N F W VL VR) (kVL N F W VL VR) (kVR N F W VL VR)) ψ 1
        (fun _ => q) ω = cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q) ω := by
  simp only [cfAt, kW_path_eq hωN hωF, bheProc_k_eq hωN hωF]

variable [StandardBorelSpace Ω] [IsProbabilityMeasure P]

/-- **The countably many identities hold under almost every conditional law** (transfer of `HasSafeLaw`). -/
theorem ae_forall_setIntegral_piClosure_eq_k (h𝒢 : 𝒢 ≤ 𝓗 0) (hF : MeasurableSet[𝒢] F)
    (hW : AdaptedBefore 𝓗 ζ W) (hVL : ∀ i, AdaptedBefore 𝓗 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓗 ζ (VR j))
    (hX : Measurable X) (hNm : MeasurableSet N) (hN0 : P N = 0) (hN : IsKGood N F ζ W VL VR)
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X) :
    ∀ᵐ ω₀ ∂P, ∀ (n k : ℕ) (p : RatIdx)
      (A : piClosure (dataGens N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR) (dyT n k))),
      ∫ ω, ((A : Set Ω) ∩ F).indicator ((safeU (kW N F W VL VR) ζ univ (ratTest upperHalfPlaneOpens p)
          (dyT n k)).indicator (fun ω => Complex.exp (Complex.I * (X ω (ratTest upperHalfPlaneOpens p) : ℂ)))) ω
          ∂(condExpKernel P 𝒢 ω₀) =
        ∫ ω, ((A : Set Ω) ∩ F).indicator ((safeU (kW N F W VL VR) ζ univ (ratTest upperHalfPlaneOpens p)
          (dyT n k)).indicator (cfAt κ (kW N F W VL VR)
            (bheProc κ ρL ρR (kW N F W VL VR) (kVL N F W VL VR) (kVR N F W VL VR))
            (ratTest upperHalfPlaneOpens p) 1 fun _ => dyT n k)) ω ∂(condExpKernel P 𝒢 ω₀) := by
  have hF0 : MeasurableSet[𝓗 0] F := h𝒢 _ hF
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hdm := dataMeas_k hNm hF0 hW hVL hVR
  have hNc : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  refine ae_all_iff.2 fun n => ae_all_iff.2 fun k => ae_all_iff.2 fun p => ?_
  set ψ := ratTest upperHalfPlaneOpens p
  set q := dyT n k
  set S := safeU (kW N F W VL VR) ζ univ ψ q with hSdef
  have hc : Countable (piClosure (dataGens N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR) q)) :=
    (countable_piClosure (countable_dataGens _ _ _ _ _)).to_subtype
  refine ae_all_iff.2 fun A => ?_
  have hAk : MeasurableSet[kF N F ζ W VL VR q] (A : Set Ω) := measurableSet_kF_of_mem_piClosure hdm A.2
  have hSk : MeasurableSet[kF N F ζ W VL VR q] S :=
    measurableSet_safeU_kF hdm hN univ MeasurableSet.univ ψ q
  have hAm : MeasurableSet (A : Set Ω) := (kF N F ζ W VL VR).le q _ hAk
  have hSm : MeasurableSet S := (kF N F ζ W VL VR).le q _ hSk
  have hFm : MeasurableSet F := h𝒢m _ hF
  have hXm : Measurable fun ω => X ω ψ := (LQGMetric.measurable_distOn_apply ψ).comp hX
  have hXi : Integrable (S.indicator fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ))) P :=
    (GFF.integrable_exp_I_mul hXm).indicator hSm
  have hYm := (measurable_Y_kF hdm hN κ ρL ρR ψ q).mono ((kF N F ζ W VL VR).le q) le_rfl
  have hYi : Integrable (S.indicator (cfAt κ (kW N F W VL VR)
      (bheProc κ ρL ρR (kW N F W VL VR) (kVL N F W VL VR) (kVR N F W VL VR)) ψ 1 fun _ => q)) P :=
    Integrable.of_bound hYm.aestronglyMeasurable 1 (Eventually.of_forall (norm_Y_le hN κ ρL ρR ψ q))
  refine ae_integral_condExpKernel_eq h𝒢m (hXi.indicator (hAm.inter hFm)) (hYi.indicator (hAm.inter hFm))
    fun B hB => ?_
  have hBm : MeasurableSet B := h𝒢m _ hB
  -- versions in the `P`-side filtration
  obtain ⟨A', hA', hAA'⟩ := exists_version_of_measurableSet_kF hF0 hW hVL hVR hAk
  obtain ⟨S', hS', hSS'⟩ := exists_version_of_measurableSet_kF hF0 hW hVL hVR hSk
  have hBq : MeasurableSet[𝓗 q] B := 𝓗.mono (zero_le (a := q)) _ (h𝒢 _ hB)
  have hFq : MeasurableSet[𝓗 q] F := 𝓗.mono (zero_le (a := q)) _ hF0
  set D := B ∩ ((A' ∩ F) ∩ S') with hDdef
  have hD : MeasurableSet[𝓗 q] D := hBq.inter ((hA'.inter hFq).inter hS')
  have hDeq : D =ᵐ[P] (B ∩ ((A : Set Ω) ∩ F) ∩ S : Set Ω) := by
    filter_upwards [hNc] with ω hωN
    have h1 := (diff_eq_diff_iff.1 hAA') ω hωN
    have h2 := (diff_eq_diff_iff.1 hSS') ω hωN
    simp only [hDdef, eq_iff_iff, mem_inter_iff, h1, h2]
    tauto
  have hDin : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ F ∧ ω ∈ avoidSet W ζ ψ q := by
    filter_upwards [hNc] with ω hωN hωD
    have hωS : ω ∈ S := ((diff_eq_diff_iff.1 hSS') ω hωN).2 hωD.2.2
    have hωF : ω ∈ F := hωD.2.1.2
    exact ⟨hωF, (mem_avoidSet_k_iff hωN hωF ψ q).1
      (safeU_subset_avoidSet_of_weak hN.isWeakPath univ ψ q hωS)⟩
  have key := hlaw ψ q D hD hDin
  rw [setIntegral_indicator (hAm.inter hFm), setIntegral_indicator (hAm.inter hFm),
    setIntegral_indicator hSm, setIntegral_indicator hSm, ← setIntegral_congr_set hDeq,
    ← setIntegral_congr_set hDeq, key]
  refine setIntegral_congr_ae ((𝓗.le q) _ hD) ?_
  filter_upwards [hNc] with ω hωN hωD
  exact (cfAt_k_eq hωN hωD.2.1.2 ψ q).symm

/-- **(S) under the regular conditional law.** For `P`-almost every `ω₀ ∈ F`, under `ν = condExpKernel P 𝒢 ω₀`,
every measurable version `(W', VL', VR')` of the modified continuation (equal to it `ν`-almost surely at every time)
is dyadically sampled with the field `X` (`IsDyadicSampled`: the protected-kernel law at the dyadic times on the
events of its own augmented driving filtration). -/
theorem ae_isDyadicSampled_k (h𝒢 : 𝒢 ≤ 𝓗 0) (hF : MeasurableSet[𝒢] F)
    (hW : AdaptedBefore 𝓗 ζ W) (hVL : ∀ i, AdaptedBefore 𝓗 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓗 ζ (VR j))
    (hX : Measurable X) (hNm : MeasurableSet N) (hN0 : P N = 0) (hN : IsKGood N F ζ W VL VR)
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
      (hX' : IsMeasurableKilledDriving W' VL' VR' ζ),
      (∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t, W' t ω = kW N F W VL VR t ω ∧
        (∀ i, VL' i t ω = kVL N F W VL VR i t ω) ∧ ∀ j, VR' j t ω = kVR N F W VL VR j t ω) →
      IsDyadicSampled κ W' (bheProc κ ρL ρR W' VL' VR') (condExpKernel P 𝒢 ω₀) hX' X := by
  have hF0 : MeasurableSet[𝓗 0] F := h𝒢 _ hF
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hdm := dataMeas_k hNm hF0 hW hVL hVR
  filter_upwards [ae_forall_setIntegral_piClosure_eq_k h𝒢 hF hW hVL hVR hX hNm hN0 hN hlaw,
    ae_ae_condExpKernel_mem (P := P) h𝒢m hF] with ω₀ htr hmem hω₀F W' VL' VR' hX' hag
  have hFν : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ F := hmem hω₀F
  refine isDyadicSampled_of_agree_pi (W := kW N F W VL VR) (VL := kVL N F W VL VR) (VR := kVR N F W VL VR)
    hN.isWeakPath (adaptedBefore_kW hdm hN) (adaptedBefore_kVL hdm hN) (adaptedBefore_kVR hdm hN) hX
    (S := fun q => piClosure (dataGens N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR) q)) (kF_eq hdm)
    (fun _ => isPiSystem_piClosure _) (fun _ => univ_mem_piClosure _) (fun n k p A hA => ?_) hX' hag
  have h := htr n k p ⟨A, hA⟩
  have hAF : ((A ∩ F : Set Ω) : Set Ω) =ᵐ[condExpKernel P 𝒢 ω₀] A := by
    filter_upwards [hFν] with ω hω
    simp only [mem_inter_iff, hω, and_true]
  have hAFm : MeasurableSet (A ∩ F) :=
    ((kF N F ζ W VL VR).le _ _ (measurableSet_kF_of_mem_piClosure hdm hA)).inter (h𝒢m _ hF)
  rw [integral_indicator hAFm, integral_indicator hAFm, setIntegral_congr_set hAF,
    setIntegral_congr_set hAF] at h
  exact h

end Transfer

end InteractingSLE.Restart.DomainMarkov.K2
