/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3LawJoint
import QuantumZipper.Proofs.GFF.K3.DisjointUnion

/-!
# Lemma GW3's conditional independence of the component fields

Packet PROVE-T14-GW7. Lemma GW3 (`source/spec/p625-671.md` L206, L226, pp. 636–637): "The zero-boundary fields in the
countably many selected components are conditionally independent. […] Marked union locality gives the zero-boundary
Green covariance and the conditional independence of the component fields."

This file proves the Gaussian step: if, under a law `ν`, the pairings of a field `X` with the test functions supported
in an open set `U ⊆ ℍ`, centred by a deterministic mean functional `M`, form a Gaussian process whose covariance is the
zero-boundary covariance of `U` (`zeroGFFTestCov U`, the dual Dirichlet form), then

* the covariance of `U` restricted to a piece `C` (open, with `U \ C` open) is that of `C`
  (`zeroGFFTestCov_eq_of_split`), so the zero-boundary GFF of `U` restricts to that of `C`
  (`isZBGFFProcess_restrict_of_split`);
* the covariance vanishes between test functions supported in a component `C` and in `U \ C`
  (`zeroGFFTestCov_eq_zero_of_split`), because the dual Dirichlet norm splits over the disjoint open pieces `C`,
  `U \ C` (QuantumZipper's `K3.dualNormSq_union_of_disjoint`) and a measure not charging a piece has dual norm zero
  there;
* the restrictions of `X` to pairwise disjoint such pieces are independent (`iIndepFun_restrict_of_cov`, from
  Mathlib's `IsGaussianProcess.iIndepFun_of_covariance_eq_zero`);
* fields read in conformal charts of the pieces (`IsChartTransport`, any lift coefficient) are independent
  (`iIndepFun_of_isChartTransport`), since each pairing of a transported field is a pairing of `X` with a test function
  supported in its piece plus a constant (`IsChartTransport.apply_eq`);
* in particular the fields of the components between the walks, read in their component charts, are independent
  (`iIndepFun_componentFields`) — the independence clause of `GW3Law.GW3FieldLawOneChartStatement`, given the
  Gaussian law on the complement of the walks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H zeroSpace dualNormSq dualCov testMeasPos testMeasNeg zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Theorem14

namespace GW3Joint

/-! ### The dual Dirichlet norm across a component -/

section DualNorm

/-- The dual norm only sees the integrals of the test functions. -/
theorem dualNormSq_congr_integral {D : Set ℂ} {μ μ' : Measure ℂ}
    (h : ∀ f ∈ zeroSpace D, ∫ x, f x ∂μ = ∫ x, f x ∂μ') :
    dualNormSq D (zeroSpace D) μ = dualNormSq D (zeroSpace D) μ' := by
  unfold dualNormSq
  refine iSup_congr fun f => iSup_congr fun hf => ?_
  rw [h f hf.1]

/-- The zero measure has dual norm zero. -/
theorem dualNormSq_zero_measure (D : Set ℂ) : dualNormSq D (zeroSpace D) 0 = 0 := by
  unfold dualNormSq
  simp

/-- A test function of `D` integrates to zero against a measure not charging `D`. -/
theorem integral_eq_zero_of_mem_zeroSpace {D : Set ℂ} {f : ℂ → ℝ} (hf : f ∈ zeroSpace D) {μ : Measure ℂ}
    (hμ : μ D = 0) : ∫ x, f x ∂μ = 0 := by
  refine integral_eq_zero_of_ae (ae_iff.2 (measure_mono_null (fun x hx => ?_) hμ))
  exact hf.2.2 (subset_tsupport f hx)

/-- Adding a finite measure that does not charge `D` does not change the integrals of the test functions of `D`. -/
theorem integral_add_measure_of_null {D : Set ℂ} {f : ℂ → ℝ} (hf : f ∈ zeroSpace D) {μ ν : Measure ℂ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hν : ν D = 0) : ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ := by
  have hc : Continuous f := hf.1.continuous
  rw [integral_add_measure (hc.integrable_of_hasCompactSupport hf.2.1) (hc.integrable_of_hasCompactSupport hf.2.1),
    integral_eq_zero_of_mem_zeroSpace hf hν, add_zero]

/-- **The dual norm is additive over a split of `U` into the open pieces `C` and `U \ C`**, for a measure `μ` not
charging `U \ C` and a measure `ν` not charging `C`. -/
theorem dualNormSq_add_of_split {U C : Set ℂ} (hC : IsOpen C) (hUC : IsOpen (U \ C)) (hCU : C ⊆ U)
    {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ (U \ C) = 0) (hν : ν C = 0) :
    dualNormSq U (zeroSpace U) (μ + ν) = dualNormSq U (zeroSpace U) μ + dualNormSq U (zeroSpace U) ν := by
  have hU : U = C ∪ (U \ C) := (union_sdiff_cancel hCU).symm
  have hd : Disjoint C (U \ C) := disjoint_sdiff_right
  have h1 : dualNormSq C (zeroSpace C) (μ + ν) = dualNormSq C (zeroSpace C) μ :=
    dualNormSq_congr_integral fun f hf => integral_add_measure_of_null hf hν
  have h2 : dualNormSq (U \ C) (zeroSpace (U \ C)) (μ + ν) = dualNormSq (U \ C) (zeroSpace (U \ C)) ν := by
    rw [add_comm]
    exact dualNormSq_congr_integral fun f hf => integral_add_measure_of_null hf hμ
  have h3 : dualNormSq (U \ C) (zeroSpace (U \ C)) μ = 0 := by
    rw [← dualNormSq_zero_measure (U \ C)]
    exact dualNormSq_congr_integral fun f hf => by
      rw [integral_eq_zero_of_mem_zeroSpace hf hμ, integral_zero_measure]
  have h4 : dualNormSq C (zeroSpace C) ν = 0 := by
    rw [← dualNormSq_zero_measure C]
    exact dualNormSq_congr_integral fun f hf => by
      rw [integral_eq_zero_of_mem_zeroSpace hf hν, integral_zero_measure]
  rw [hU, QuantumZipper.K3.dualNormSq_union_of_disjoint hC hUC hd,
    QuantumZipper.K3.dualNormSq_union_of_disjoint hC hUC hd μ,
    QuantumZipper.K3.dualNormSq_union_of_disjoint hC hUC hd ν, h1, h2, h3, h4, add_zero, zero_add]

/-- **The dual covariance vanishes across the split**, for measures of finite dual norm. -/
theorem dualCov_eq_zero_of_split {U C : Set ℂ} (hC : IsOpen C) (hUC : IsOpen (U \ C)) (hCU : C ⊆ U)
    {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ (U \ C) = 0) (hν : ν C = 0)
    (hμf : dualNormSq U (zeroSpace U) μ ≠ ⊤) (hνf : dualNormSq U (zeroSpace U) ν ≠ ⊤) :
    dualCov U (zeroSpace U) μ ν = 0 := by
  unfold dualCov
  rw [dualNormSq_add_of_split hC hUC hCU hμ hν, ENNReal.toReal_add hμf hνf]
  ring

/-- The measures `φ^± dz` of a continuous compactly supported `φ` with support in an open `U ⊆ ℍ` are finite and
have finite dual norm on `U`. -/
theorem testMeas_finite {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H) {φ : ℂ → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (IsFiniteMeasure (testMeasPos φ) ∧ dualNormSq U (zeroSpace U) (testMeasPos φ) ≠ ⊤) ∧
      (IsFiniteMeasure (testMeasNeg φ) ∧ dualNormSq U (zeroSpace U) (testMeasNeg φ) ≠ ⊤) := by
  have hsH := hφU.trans (hUH.trans QuantumZipper.K3.H_subset_Hbar_K3)
  have hp := QuantumZipper.K3.isAdmissibleH_testMeasPos_of hφc hφs hsH
  have hn := QuantumZipper.K3.isAdmissibleH_testMeasNeg_of hφc hφs hsH
  exact ⟨⟨hp.1, ((QuantumZipper.K3.dualNormSq_zeroSpace_mono hUo hUH).trans_lt
      (QuantumZipper.K3.isAdmissibleDual_H_of_isAdmissibleH hp).2.2).ne⟩,
    ⟨hn.1, ((QuantumZipper.K3.dualNormSq_zeroSpace_mono hUo hUH).trans_lt
      (QuantumZipper.K3.isAdmissibleDual_H_of_isAdmissibleH hn).2.2).ne⟩⟩

/-- **The zero-boundary covariance of `U` vanishes between a test function supported in the open piece `C` and one
supported in the open rest `U \ C`.** -/
theorem zeroGFFTestCov_eq_zero_of_split {U C : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H) (hC : IsOpen C)
    (hUC : IsOpen (U \ C)) (hCU : C ⊆ U) {φ ψ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφ : tsupport φ ⊆ C) (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ : tsupport ψ ⊆ U \ C) :
    zeroGFFTestCov U φ ψ = 0 := by
  obtain ⟨⟨hp₁, hp₂⟩, hn₁, hn₂⟩ := testMeas_finite hUo hUH hφc hφs (hφ.trans hCU)
  obtain ⟨⟨hq₁, hq₂⟩, hm₁, hm₂⟩ := testMeas_finite hUo hUH hψc hψs (hψ.trans sdiff_subset)
  have hφ0 : ∀ μ : Measure ℂ, μ (tsupport φ)ᶜ = 0 → μ (U \ C) = 0 := fun μ h0 =>
    measure_mono_null (fun z hz hzφ => hz.2 (hφ hzφ)) h0
  have hψ0 : ∀ μ : Measure ℂ, μ (tsupport ψ)ᶜ = 0 → μ C = 0 := fun μ h0 =>
    measure_mono_null (fun z hz hzψ => (hψ hzψ).2 hz) h0
  have e₁ := hφ0 _ (LQGMetric.testMeasPos_compl_tsupport φ)
  have e₂ := hφ0 _ (LQGMetric.testMeasNeg_compl_tsupport φ)
  have e₃ := hψ0 _ (LQGMetric.testMeasPos_compl_tsupport ψ)
  have e₄ := hψ0 _ (LQGMetric.testMeasNeg_compl_tsupport ψ)
  unfold zeroGFFTestCov
  rw [dualCov_eq_zero_of_split hC hUC hCU e₁ e₃ hp₂ hq₂, dualCov_eq_zero_of_split hC hUC hCU e₁ e₄ hp₂ hm₂,
    dualCov_eq_zero_of_split hC hUC hCU e₂ e₃ hn₂ hq₂, dualCov_eq_zero_of_split hC hUC hCU e₂ e₄ hn₂ hm₂]
  ring

/-- **The dual norm on `U` of a measure not charging `U \ C` is its dual norm on the open piece `C`.** -/
theorem dualNormSq_eq_of_split {U C : Set ℂ} (hC : IsOpen C) (hUC : IsOpen (U \ C)) (hCU : C ⊆ U)
    {μ : Measure ℂ} (hμ : μ (U \ C) = 0) :
    dualNormSq U (zeroSpace U) μ = dualNormSq C (zeroSpace C) μ := by
  have hU : U = C ∪ (U \ C) := (union_sdiff_cancel hCU).symm
  have h3 : dualNormSq (U \ C) (zeroSpace (U \ C)) μ = 0 := by
    rw [← dualNormSq_zero_measure (U \ C)]
    exact dualNormSq_congr_integral fun f hf => by
      rw [integral_eq_zero_of_mem_zeroSpace hf hμ, integral_zero_measure]
  rw [hU, QuantumZipper.K3.dualNormSq_union_of_disjoint hC hUC disjoint_sdiff_right μ, h3, add_zero]

/-- The dual covariance on `U` of measures not charging `U \ C` is their dual covariance on `C`. -/
theorem dualCov_eq_of_split {U C : Set ℂ} (hC : IsOpen C) (hUC : IsOpen (U \ C)) (hCU : C ⊆ U)
    {μ ν : Measure ℂ} (hμ : μ (U \ C) = 0) (hν : ν (U \ C) = 0) :
    dualCov U (zeroSpace U) μ ν = dualCov C (zeroSpace C) μ ν := by
  unfold dualCov
  rw [dualNormSq_eq_of_split hC hUC hCU (by rw [Measure.add_apply, hμ, hν, add_zero]),
    dualNormSq_eq_of_split hC hUC hCU hμ, dualNormSq_eq_of_split hC hUC hCU hν]

/-- **The zero-boundary covariance of `U` restricted to test functions supported in the open piece `C` (with
`U \ C` open) is the zero-boundary covariance of `C`** (the bilinear form of
`LocalSets.zeroGFFTestCov_eq_of_isClopen`). -/
theorem zeroGFFTestCov_eq_of_split {U C : Set ℂ} (hC : IsOpen C) (hUC : IsOpen (U \ C)) (hCU : C ⊆ U)
    {φ ψ : ℂ → ℝ} (hφ : tsupport φ ⊆ C) (hψ : tsupport ψ ⊆ C) :
    zeroGFFTestCov U φ ψ = zeroGFFTestCov C φ ψ := by
  have h0 : ∀ χ : ℂ → ℝ, tsupport χ ⊆ C → ∀ μ : Measure ℂ, μ (tsupport χ)ᶜ = 0 → μ (U \ C) = 0 :=
    fun χ hχ μ h0 => measure_mono_null (fun z hz hzχ => hz.2 (hχ hzχ)) h0
  have p₁ := h0 φ hφ _ (LQGMetric.testMeasPos_compl_tsupport φ)
  have n₁ := h0 φ hφ _ (LQGMetric.testMeasNeg_compl_tsupport φ)
  have p₂ := h0 ψ hψ _ (LQGMetric.testMeasPos_compl_tsupport ψ)
  have n₂ := h0 ψ hψ _ (LQGMetric.testMeasNeg_compl_tsupport ψ)
  unfold zeroGFFTestCov
  rw [dualCov_eq_of_split hC hUC hCU p₁ p₂, dualCov_eq_of_split hC hUC hCU p₁ n₂,
    dualCov_eq_of_split hC hUC hCU n₁ p₂, dualCov_eq_of_split hC hUC hCU n₁ n₂]

/-- **A zero-boundary GFF process on `U` (with mean `m`) restricts to one on an open piece `C` of `U` with `U \ C`
open** (for a field `h` on `ℍ` read through the inclusion of test functions). -/
theorem isZBGFFProcess_restrict_of_split {U C : TopologicalSpace.Opens ℂ} (hUH : U ≤ upperHalfPlaneOpens)
    (hCU : C ≤ U) (hUC : IsOpen ((U : Set ℂ) \ C)) {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {m : ℂ → ℝ}
    (hZ : LQGMetric.IsZBGFFProcess U
      (fun ψ ω => h ω (GFF.testIncl U upperHalfPlaneOpens ψ) - ∫ z, m z * ψ z) ν) :
    LQGMetric.IsZBGFFProcess C
      (fun ψ ω => h ω (GFF.testIncl C upperHalfPlaneOpens ψ) - ∫ z, m z * ψ z) ν := by
  have key : ∀ ψ : TestOn C,
      (fun ω => h ω (GFF.testIncl U upperHalfPlaneOpens (GFF.testIncl C U ψ)) -
        ∫ z, m z * (GFF.testIncl C U ψ : TestOn U) z) =
      fun ω => h ω (GFF.testIncl C upperHalfPlaneOpens ψ) - ∫ z, m z * ψ z := fun ψ => by
    rw [GFF.testIncl_testIncl' hCU hUH, GFF.coe_testIncl hCU]
  refine ⟨fun ψ => key ψ ▸ hZ.measurable _, ?_, fun ψ => key ψ ▸ hZ.centered _, fun ψ ψ' => ?_⟩
  · have hg := hZ.gaussian.comp_right (GFF.testIncl C U)
    have e : ((fun ψ ω => h ω (GFF.testIncl U upperHalfPlaneOpens ψ) - ∫ z, m z * ψ z) ∘
        (GFF.testIncl C U)) = fun ψ ω => h ω (GFF.testIncl C upperHalfPlaneOpens ψ) - ∫ z, m z * ψ z := by
      funext ψ
      exact key ψ
    rwa [e] at hg
  · rw [← key ψ, ← key ψ', hZ.covariance_eq, GFF.coe_testIncl hCU, GFF.coe_testIncl hCU]
    exact zeroGFFTestCov_eq_of_split C.isOpen hUC hCU ψ.tsupport_subset ψ'.tsupport_subset

end DualNorm

/-! ### Independence of the restrictions and of the transported fields -/

section Indep

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {U : Set ℂ} {X : Ω → DistOn upperHalfPlaneOpens}
  {M : TestOn upperHalfPlaneOpens → ℝ}

/-- **Gaussian restrictions to disjoint pieces are independent.** If the centred pairings `X(φ) − M(φ)` (`M` a
deterministic mean functional) with the test functions supported in the open `U ⊆ ℍ` form a Gaussian process with the
zero-boundary covariance of `U`, the centred restrictions of `X` to pairwise disjoint open pieces `C i ⊆ U` with open
complements `U \ C i` are independent. -/
theorem iIndepFun_restrict_of_cov (hUo : IsOpen U) (hUH : U ⊆ H)
    (hX : IsGaussianProcess
      (fun (φ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ U}) ω => X ω φ.1 - M φ.1) ν)
    (hXm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω φ)
    (hcov : ∀ φ ψ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ U → tsupport ψ ⊆ U →
      cov[fun ω => X ω φ - M φ, fun ω => X ω ψ - M ψ; ν] = zeroGFFTestCov U φ ψ)
    {ι : Type*} {C : ι → Set ℂ} (hCo : ∀ i, IsOpen (C i)) (hUC : ∀ i, IsOpen (U \ C i)) (hCU : ∀ i, C i ⊆ U)
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) :
    iIndepFun (fun i ω (φ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ C i}) => X ω φ.1 - M φ.1) ν := by
  have hX' : IsGaussianProcess
      (fun (p : (i : ι) × {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ C i}) ω => X ω p.2.1 - M p.2.1) ν :=
    hX.comp_right (fun (p : (i : ι) × {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ C i}) =>
      (⟨p.2.1, p.2.2.trans (hCU p.1)⟩ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ U}))
  refine hX'.iIndepFun_of_covariance_eq_zero (X := fun i
    (φ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ C i}) ω => X ω φ.1 - M φ.1)
    (fun i φ => ((hXm φ.1).sub_const _).aemeasurable)
    fun i j hij φ ψ => ?_
  rw [hcov _ _ (φ.2.trans (hCU i)) (ψ.2.trans (hCU j))]
  exact zeroGFFTestCov_eq_zero_of_split hUo hUH (hCo i) (hUC i) (hCU i) φ.1.continuous φ.1.hasCompactSupport φ.2
    ψ.1.continuous ψ.1.hasCompactSupport
    fun z hz => ⟨hCU j (ψ.2 hz), fun hz' => Set.disjoint_left.1 (hd hij) hz' (ψ.2 hz)⟩

/-- **Fields read in conformal charts of disjoint pieces are independent.** Under the hypotheses of
`iIndepFun_restrict_of_cov`, let `Y i` be `X` read in a conformal chart `c i` whose physical domain lies in `C i`
(`IsChartTransport (c i) 1 0 k`). Then the `Y i` are independent. -/
theorem iIndepFun_of_isChartTransport (hUo : IsOpen U) (hUH : U ⊆ H)
    (hX : IsGaussianProcess
      (fun (φ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ U}) ω => X ω φ.1 - M φ.1) ν)
    (hXm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω φ)
    (hcov : ∀ φ ψ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ U → tsupport ψ ⊆ U →
      cov[fun ω => X ω φ - M φ, fun ω => X ω ψ - M ψ; ν] = zeroGFFTestCov U φ ψ)
    {ι : Type*} {C : ι → Set ℂ} (hCo : ∀ i, IsOpen (C i)) (hUC : ∀ i, IsOpen (U \ C i)) (hCU : ∀ i, C i ⊆ U)
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) {c : ι → Chart} (hc : ∀ i, (c i).IsConformal)
    (hcC : ∀ i, (c i).2.1 '' H ⊆ C i) {k : ℝ} {Y : ι → Ω → DistOn upperHalfPlaneOpens}
    (hY : ∀ i ω, IsChartTransport (c i) 1 0 k (X ω) (Y i ω)) :
    iIndepFun Y ν := by
  have hind := iIndepFun_restrict_of_cov hUo hUH hX hXm hcov hCo hUC hCU hd
  rw [iIndepFun_iff_iIndep] at hind ⊢
  refine iIndep_of_iIndep_of_le hind fun i => ?_
  set m : MeasurableSpace Ω := MeasurableSpace.comap
    (fun ω (φ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ C i}) => X ω φ.1 - M φ.1) MeasurableSpace.pi
    with hm
  have hr : @Measurable Ω ({φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ C i} → ℝ) m MeasurableSpace.pi
      (fun ω (φ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ C i}) => X ω φ.1 - M φ.1) :=
    comap_measurable _
  have hmeas : @Measurable Ω _ m _ (Y i) := by
    refine (@LQGMetric.measurable_distOn_iff upperHalfPlaneOpens Ω m (Y i)).2 fun φ' => ?_
    have hsupp : tsupport (Chart.pushTest (hc i) φ') ⊆ C i := by
      have := Chart.tsupport_pushTest_subset (hc i) φ'
      rw [(hc i).coe_dom] at this
      exact this.trans (hcC i)
    have hX₁ : @Measurable Ω ℝ m _
        (fun ω => X ω (Chart.pushTest (hc i) φ') - M (Chart.pushTest (hc i) φ')) :=
      (measurable_pi_apply (⟨Chart.pushTest (hc i) φ', hsupp⟩ :
        {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ C i})).comp hr
    have he : (fun ω => Y i ω φ') = fun ω => 1 * (X ω (Chart.pushTest (hc i) φ') - M (Chart.pushTest (hc i) φ') +
        M (Chart.pushTest (hc i) φ')) + 0 * (∫ w, φ' w) + k * ∫ w, (c i).2.2 ((c i).2.1 w) * φ' w := by
      funext ω
      rw [sub_add_cancel]
      exact (hY i ω).apply_eq (hc i) φ'
    rw [he]
    exact (((hX₁.add_const _).const_mul 1).add_const _).add_const _
  exact hmeas.comap_le

end Indep

/-! ### The components between the walks -/

section Components

/-- The rest of an open set outside one of its connected components is open. -/
theorem isOpen_sdiff_connectedComponentIn {U : Set ℂ} (hU : IsOpen U) (z : ℂ) :
    IsOpen (U \ connectedComponentIn U z) := by
  refine isOpen_iff_forall_mem_open.2 fun w hw => ⟨connectedComponentIn U w, fun v hv => ⟨?_, fun hvz => ?_⟩,
    hU.connectedComponentIn, mem_connectedComponentIn hw.1⟩
  · exact connectedComponentIn_subset U w hv
  · have h1 : connectedComponentIn U z = connectedComponentIn U v := connectedComponentIn_eq hvz
    have h2 : connectedComponentIn U w = connectedComponentIn U v := connectedComponentIn_eq hv
    exact hw.2 (h1 ▸ h2 ▸ mem_connectedComponentIn hw.1)

/-- Two distinct connected components of a set are disjoint. -/
theorem disjoint_connectedComponentIn_of_ne {U : Set ℂ} {z w : ℂ}
    (hne : connectedComponentIn U z ≠ connectedComponentIn U w) :
    Disjoint (connectedComponentIn U z) (connectedComponentIn U w) := by
  refine Set.disjoint_left.2 fun v hvz hvw => hne ?_
  rw [connectedComponentIn_eq hvz, connectedComponentIn_eq hvw]

variable {R L : Set ℂ}

/-- A component between the walks is a connected component of `ℍ \ (R ∪ L)` (of one of its points). -/
theorem exists_eq_connectedComponentIn_of_mem_betweenComponents {C : Set ℂ} (hC : C ∈ betweenComponents R L) :
    ∃ z ∈ H \ (R ∪ L), C = connectedComponentIn (H \ (R ∪ L)) z := by
  obtain ⟨z, hz, -, -, rfl⟩ := hC
  exact ⟨z, hz, rfl⟩

/-- **Lemma GW3's conditional independence of the component fields** (the independence clause of
`GW3Law.GW3FieldLawOneChartStatement`), from the Gaussian law on the complement of the walks: if, under `ν`, the
pairings of `h` with the test functions supported in the open set `ℍ \ (R ∪ L)`, centred by a deterministic mean
functional `M`, form a Gaussian process with the zero-boundary covariance of `ℍ \ (R ∪ L)`, then the fields of the
components between the walks, read in component charts (any lift coefficient `k`), are independent. -/
theorem iIndepFun_componentFields (hUo : IsOpen (H \ (R ∪ L))) {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens}
    {M : TestOn upperHalfPlaneOpens → ℝ}
    (hX : IsGaussianProcess
      (fun (φ : {φ : TestOn upperHalfPlaneOpens // tsupport φ ⊆ H \ (R ∪ L)}) ω => h ω φ.1 - M φ.1) ν)
    (hXm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable fun ω => h ω φ)
    (hcov : ∀ φ ψ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (R ∪ L) → tsupport ψ ⊆ H \ (R ∪ L) →
      cov[fun ω => h ω φ - M φ, fun ω => h ω ψ - M ψ; ν] = zeroGFFTestCov (H \ (R ∪ L)) φ ψ)
    {cs : Set ℂ → Chart} (hcs : ∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) {k : ℝ}
    {hC : Set ℂ → Ω → DistOn upperHalfPlaneOpens}
    (htr : ∀ C ∈ betweenComponents R L, ∀ ω, IsChartTransport (cs C) 1 0 k (h ω) (hC C ω)) :
    iIndepFun (fun (C : betweenComponents R L) ω => hC C ω) ν := by
  have hcc : ∀ C : betweenComponents R L, ∃ z ∈ H \ (R ∪ L), C.1 = connectedComponentIn (H \ (R ∪ L)) z :=
    fun C => exists_eq_connectedComponentIn_of_mem_betweenComponents C.2
  choose z hz hCz using hcc
  have hCo : ∀ C : betweenComponents R L, IsOpen C.1 := fun C => hCz C ▸ hUo.connectedComponentIn
  have hCU : ∀ C : betweenComponents R L, C.1 ⊆ H \ (R ∪ L) := fun C =>
    hCz C ▸ connectedComponentIn_subset _ _
  have hUC : ∀ C : betweenComponents R L, IsOpen ((H \ (R ∪ L)) \ C.1) := fun C =>
    hCz C ▸ isOpen_sdiff_connectedComponentIn hUo (z C)
  have hd : Pairwise fun C C' : betweenComponents R L => Disjoint C.1 C'.1 := fun C C' hne => by
    show Disjoint C.1 C'.1
    rw [hCz C, hCz C']
    refine disjoint_connectedComponentIn_of_ne fun he => hne (Subtype.ext ?_)
    rw [hCz C, hCz C', he]
  refine iIndepFun_of_isChartTransport (C := fun C : betweenComponents R L => C.1)
    (c := fun C : betweenComponents R L => cs C.1) hUo sdiff_subset hX hXm hcov hCo hUC hCU hd
    (fun C => GW3Law.isConformal_of_isComponentChart (hcs C.1 C.2) (hCo C) ((hCU C).trans sdiff_subset))
    (fun C => (hcs C.1 C.2).2.2.1.image_subset) fun C ω => htr C.1 C.2 ω

end Components

end GW3Joint

end Theorem14

end InteractingSLE
