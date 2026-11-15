/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtDStep5
import InteractingSLE.Spec.Sec7.LocalExtKDens
import InteractingSLE.GFF.PushforwardLaw

/-!
# Random test functions: measurable covariances, conditional laws, and the source of a word

Packet PROVE-LOCEXT-O, tools for the Cameron–Martin tilt with a **random** source (Aux. lemma 55, step 5, at a restart:
the source `v_c` of the restart word `c`, which is measurable for the conditioning σ-algebra).

* **`measurable_zeroGFFTestCov_random`**: for a random open set `U ω ⊆ ℍ` whose test-family events are measurable and
  random test functions `ψ₁ ω`, `ψ₂ ω` measurable pointwise, `ω ↦ Cov_{U ω}(ψ₁ ω, ψ₂ ω)` is measurable (QuantumZipper's
  E3 with random measures: the dual norm is a supremum over the countable test family of pairings that are measurable
  in `ω`);
* **`IsCondZeroBoundaryGFF.condExp_cexp_random`**: a conditional zero-boundary GFF on `ℍ ∖ A ω` has the zero-boundary
  characteristic functional at every random test function measurable for the conditioning σ-algebra
  (`RandomTest.condExp_cexp_apply_ae_eq`);
* `isCovCauchy_srcTestW`, `tendsto_integral_srcTestW_mul_eq_recode`: for an admissible word `x`, the source test functions
  `srcTestW x k` are energy-Cauchy and `recodeShift x` has their Dirichlet pairings.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped ENNReal NNReal Laplacian

namespace InteractingSLE

namespace LocalExt

open QuantumZipper QuantumZipper.K3 LQGMetric LocalSets

/-! ### Measurability of the covariance at random test functions -/

section RandomCov

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A random test function measurable pointwise is jointly measurable in `(ω, z)` (it is continuous in `z`). -/
theorem measurable_uncurry_testOn {ψ : Ω → TestOn upperHalfPlaneOpens} (hψ : ∀ z, Measurable fun ω => ψ ω z) :
    Measurable fun p : Ω × ℂ => ψ p.1 p.2 := by
  have h := measurable_uncurry_of_continuous_of_measurable (u := fun (z : ℂ) (ω : Ω) => ψ ω z)
    (fun ω => (ψ ω).continuous) hψ
  exact h.comp measurable_swap

/-- The pairing of a fixed continuous compactly supported `g` with the positive part of a random test function. -/
theorem measurable_integral_testMeasPos_random {ψ : Ω → TestOn upperHalfPlaneOpens}
    (hψ : ∀ z, Measurable fun ω => ψ ω z) {g : ℂ → ℝ} (hg : Measurable g) :
    Measurable fun ω => ∫ x, g x ∂(testMeasPos (ψ ω)) := by
  have e : (fun ω => ∫ x, g x ∂(testMeasPos (ψ ω))) = fun ω => ∫ y, max (ψ ω y) 0 * g y := by
    funext ω
    exact integral_testMeasPos_K3 (ψ ω).continuous.measurable g
  rw [e]
  have hj : Measurable fun p : Ω × ℂ => max (ψ p.1 p.2) 0 * g p.2 :=
    ((measurable_uncurry_testOn hψ).max measurable_const).mul (hg.comp measurable_snd)
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- The pairing of a fixed continuous compactly supported `g` with the negative part of a random test function. -/
theorem measurable_integral_testMeasNeg_random {ψ : Ω → TestOn upperHalfPlaneOpens}
    (hψ : ∀ z, Measurable fun ω => ψ ω z) {g : ℂ → ℝ} (hg : Measurable g) :
    Measurable fun ω => ∫ x, g x ∂(testMeasNeg (ψ ω)) := by
  have e : (fun ω => ∫ x, g x ∂(testMeasNeg (ψ ω))) = fun ω => ∫ y, max (-ψ ω y) 0 * g y := by
    funext ω
    exact integral_testMeasNeg_K3 (ψ ω).continuous.measurable g
  rw [e]
  have hj : Measurable fun p : Ω × ℂ => max (-ψ p.1 p.2) 0 * g p.2 :=
    ((measurable_uncurry_testOn hψ).neg.max measurable_const).mul (hg.comp measurable_snd)
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem isGoodMeas_testMeasPos_testOn (ψ : TestOn upperHalfPlaneOpens) : IsGoodMeas (testMeasPos ψ) :=
  isGoodMeas_withDensity ψ.continuous ψ.hasCompactSupport

theorem isGoodMeas_testMeasNeg_testOn (ψ : TestOn upperHalfPlaneOpens) : IsGoodMeas (testMeasNeg ψ) :=
  isGoodMeas_withDensity (g := fun z => -ψ z) ψ.continuous.neg ψ.hasCompactSupport.neg

/-- **E3 for random measures.** For a random open set `U ω ⊆ ℍ` with measurable test-family events and a random good
measure `μ ω` whose pairings with the test family are measurable, the dual norm `‖μ ω‖²_{H⁻¹(U ω)}` is measurable. -/
theorem measurable_dualNormSq_random {U : Ω → Set ℂ} (hU : ∀ ω, IsOpen (U ω) ∧ U ω ⊆ H)
    (hE : ∀ j, MeasurableSet {ω | tsupport (testFamily j) ⊆ U ω}) {μ : Ω → Measure ℂ}
    (hμ : ∀ ω, IsGoodMeas (μ ω)) (hint : ∀ j, Measurable fun ω => ∫ x, testFamily j x ∂(μ ω)) :
    Measurable fun ω => dualNormSq (U ω) (zeroSpace (U ω)) (μ ω) := by
  classical
  have e : (fun ω => dualNormSq (U ω) (zeroSpace (U ω)) (μ ω)) = fun ω =>
      ⨆ j ∈ {j | tsupport (testFamily j) ⊆ U ω ∧ 0 < dirichletEnergyOn H (testFamily j)},
        ENNReal.ofReal ((∫ x, testFamily j x ∂(μ ω)) ^ 2 / dirichletEnergyOn H (testFamily j)) := by
    funext ω
    have := (hμ ω).1
    exact dualNormSq_eq_iSup_testFamily (hU ω).1 (hU ω).2 (hμ ω).2
  rw [e]
  refine Measurable.iSup fun j => ?_
  have e2 : (fun ω => ⨆ (_ : j ∈ {j | tsupport (testFamily j) ⊆ U ω ∧ 0 < dirichletEnergyOn H (testFamily j)}),
      ENNReal.ofReal ((∫ x, testFamily j x ∂(μ ω)) ^ 2 / dirichletEnergyOn H (testFamily j))) =
      fun ω => if ω ∈ {ω | tsupport (testFamily j) ⊆ U ω} ∧ 0 < dirichletEnergyOn H (testFamily j) then
        ENNReal.ofReal ((∫ x, testFamily j x ∂(μ ω)) ^ 2 / dirichletEnergyOn H (testFamily j)) else 0 := by
    funext ω
    split_ifs with h
    · simp only [mem_ofPred_eq] at h ⊢
      exact iSup_pos h
    · simp only [mem_ofPred_eq] at h ⊢
      exact iSup_eq_bot.2 fun hj => absurd hj h
  rw [e2]
  by_cases hB : 0 < dirichletEnergyOn H (testFamily j)
  · simp only [hB, and_true]
    exact Measurable.ite (hE j) (ENNReal.measurable_ofReal.comp (((hint j).pow_const 2).div_const _))
      measurable_const
  · simp only [hB, and_false]
    exact measurable_const

/-- **The covariance at random test functions is measurable.** -/
theorem measurable_zeroGFFTestCov_random {U : Ω → Set ℂ} (hU : ∀ ω, IsOpen (U ω) ∧ U ω ⊆ H)
    (hE : ∀ j, MeasurableSet {ω | tsupport (testFamily j) ⊆ U ω}) {ψ₁ ψ₂ : Ω → TestOn upperHalfPlaneOpens}
    (hψ₁ : ∀ z, Measurable fun ω => ψ₁ ω z) (hψ₂ : ∀ z, Measurable fun ω => ψ₂ ω z) :
    Measurable fun ω => zeroGFFTestCov (U ω) (ψ₁ ω) (ψ₂ ω) := by
  have htf : ∀ j, Measurable (testFamily j) := fun j => (testFamily_mem j).1.continuous.measurable
  have hint : ∀ j, ∀ (μ ν : Measure ℂ), IsGoodMeas μ → IsGoodMeas ν →
      ∫ x, testFamily j x ∂(μ + ν) = (∫ x, testFamily j x ∂μ) + ∫ x, testFamily j x ∂ν := by
    intro j μ ν hμ hν
    have := hμ.1
    have := hν.1
    have hc := (testFamily_mem j).1.continuous
    have hs := (testFamily_mem j).2.1
    exact integral_add_measure (hc.integrable_of_hasCompactSupport hs) (hc.integrable_of_hasCompactSupport hs)
  have hcov : ∀ {μ ν : Ω → Measure ℂ}, (∀ ω, IsGoodMeas (μ ω)) → (∀ ω, IsGoodMeas (ν ω)) →
      (∀ j, Measurable fun ω => ∫ x, testFamily j x ∂(μ ω)) →
      (∀ j, Measurable fun ω => ∫ x, testFamily j x ∂(ν ω)) →
      Measurable fun ω => dualCov (U ω) (zeroSpace (U ω)) (μ ω) (ν ω) := by
    intro μ ν hμ hν hμi hνi
    unfold dualCov
    have hsum : ∀ j, Measurable fun ω => ∫ x, testFamily j x ∂(μ ω + ν ω) := fun j => by
      simp_rw [fun ω => hint j (μ ω) (ν ω) (hμ ω) (hν ω)]
      exact (hμi j).add (hνi j)
    exact (((ENNReal.measurable_toReal.comp (measurable_dualNormSq_random hU hE (fun ω => (hμ ω).add (hν ω))
      hsum)).sub (ENNReal.measurable_toReal.comp (measurable_dualNormSq_random hU hE hμ hμi))).sub
      (ENNReal.measurable_toReal.comp (measurable_dualNormSq_random hU hE hν hνi))).div_const 2
  have hP1 := fun ω => isGoodMeas_testMeasPos_testOn (ψ₁ ω)
  have hN1 := fun ω => isGoodMeas_testMeasNeg_testOn (ψ₁ ω)
  have hP2 := fun ω => isGoodMeas_testMeasPos_testOn (ψ₂ ω)
  have hN2 := fun ω => isGoodMeas_testMeasNeg_testOn (ψ₂ ω)
  have iP1 := fun j => measurable_integral_testMeasPos_random hψ₁ (htf j)
  have iN1 := fun j => measurable_integral_testMeasNeg_random hψ₁ (htf j)
  have iP2 := fun j => measurable_integral_testMeasPos_random hψ₂ (htf j)
  have iN2 := fun j => measurable_integral_testMeasNeg_random hψ₂ (htf j)
  unfold zeroGFFTestCov
  exact (((hcov hP1 hP2 iP1 iP2).sub (hcov hP1 hN2 iP1 iN2)).sub (hcov hN1 hP2 iN1 iP2)).add
    (hcov hN1 hN2 iN1 iN2)

omit mΩ in
/-- The test-family events of the complement of a hitting-measurable random relatively closed set. -/
theorem measurableSet_testFamily_subset_compl {𝒢 : MeasurableSpace Ω} {A : Ω → Set ℂ}
    (hA : Measurable[𝒢, hittingSigma] A) (j : ℕ) :
    MeasurableSet[𝒢] {ω | tsupport (testFamily j) ⊆ H \ relClosureH (A ω)} := by
  have hj := testFamily_mem j
  have e : {ω | tsupport (testFamily j) ⊆ H \ relClosureH (A ω)} =
      A ⁻¹' {S : Set ℂ | Disjoint (tsupport (testFamily j)) (relClosureH S)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, subset_sdiff]
    exact ⟨fun h => h.2, fun h => ⟨hj.2.2, h⟩⟩
  rw [e]
  exact hA (measurableSet_disjoint_relClosureH hj.2.1.isCompact hj.2.2)

omit mΩ in
/-- **The covariance on the complement of a random hull at random test functions**, measurable for any σ-algebra
measuring the hull and the test functions. -/
theorem measurable_zeroGFFTestCov_compl_random {𝒢 : MeasurableSpace Ω} {A : Ω → Set ℂ}
    (hA : Measurable[𝒢, hittingSigma] A) (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    {ψ₁ ψ₂ : Ω → TestOn upperHalfPlaneOpens} (hψ₁ : ∀ z, Measurable[𝒢] fun ω => ψ₁ ω z)
    (hψ₂ : ∀ z, Measurable[𝒢] fun ω => ψ₂ ω z) :
    Measurable[𝒢] fun ω => zeroGFFTestCov (H \ A ω) (ψ₁ ω) (ψ₂ ω) := by
  have e : ∀ ω, H \ A ω = H \ relClosureH (A ω) := fun ω => by rw [relClosureH_eq (hAc ω).1 (hAc ω).2]
  simp_rw [e]
  exact @measurable_zeroGFFTestCov_random Ω 𝒢 (fun ω => H \ relClosureH (A ω))
    (fun ω => ⟨isOpen_H_diff_relClosureH _, sdiff_subset⟩) (measurableSet_testFamily_subset_compl hA) ψ₁ ψ₂
    hψ₁ hψ₂

end RandomCov

/-! ### Conditional zero-boundary laws at random test functions -/

section CondRandom

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **A conditional zero-boundary GFF at random test functions.** If, given `𝒢`, `X` is a zero-boundary GFF on
`ℍ ∖ A ω`, then for every test function `ψ ω` measurable for `𝒢` pointwise,
`E[e^{i X(ψ)} | 𝒢] = exp(−½ Cov_{ℍ∖A}(ψ, ψ))`. -/
theorem IsCondZeroBoundaryGFF.condExp_cexp_random (h𝒢 : 𝒢 ≤ mΩ) {A : Ω → Set ℂ}
    (hA : ∀ ω, IsOpen (H \ A ω)) {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X)
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) X) {ψ : Ω → TestOn upperHalfPlaneOpens}
    (hψ : ∀ z, Measurable[𝒢] fun ω => ψ ω z) :
    P[fun ω => Complex.exp (Complex.I * (X ω (ψ ω) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) (ψ ω) (ψ ω)) : ℝ) : ℂ) :=
  RandomTest.condExp_cexp_apply_ae_eq h𝒢 hX
    (Ψ := fun ω φ => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) φ φ) : ℝ) : ℂ))
    (fun ω => RandomTest.exists_zbExtLaw (U := ⟨H \ A ω, hA ω⟩) sdiff_subset) hcond hψ

end CondRandom

/-! ### The source of a word -/

section Word

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}

/-- **The source test functions of an admissible word are energy-Cauchy.** -/
theorem isCovCauchy_srcTestW {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) :
    IsCovCauchy (srcTestW κ ρL ρR r x) := by
  intro N n m hn hm
  rw [zeroGFFTestCov_H_eq_greenEnergy]
  have e : ⇑(srcTestW κ ρL ρR r x n - srcTestW κ ρL ρR r x m) = fun z =>
      vApproxW κ ρL ρR r x (pairSeqW κ ρL ρR r x n) z - vApproxW κ ρL ρR r x (pairSeqW κ ρL ρR r x m) z := by
    funext z
    change srcTestW κ ρL ρR r x n z - srcTestW κ ρL ρR r x m z = _
    rw [srcTestW_apply, srcTestW_apply]
  rw [e]
  exact (pairEnergyW_lt κ ρL ρR r hx ((strictMono_pairSeqW κ ρL ρR r x).monotone hn)
    ((strictMono_pairSeqW κ ρL ρR r x).monotone hm)).le

/-- The Dirichlet pairings of `f − q` of an admissible word are those of its source:
`(f − q)(−Δg/2π) = ∫ g v`. -/
theorem smoothDist_recodeShift_lapTest {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x)
    (U : Opens ℂ) (hU : U ≤ upperHalfPlaneOpens) (g : MarkovZB.zsSub (U : Set ℂ)) :
    SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (recodeShift κ x.1 x.2 ρL ρR r)
      (lapTest U g) = ∫ z, g.1 z * vSrc κ x.1 x.2 ρL ρR r z := by
  have hgc : Continuous g.1 := g.2.1.continuous
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support g.2.2.1
  have h1 := tendsto_integral_srcTest_mul_eq_recode (κ := κ) (ρL := ρL) (ρR := ρR) hx.1 hx.2 U hU g
  have h2 := tendsto_integral_mul_srcTest (κ := κ) (ρL := ρL) (ρR := ρR) hx.1 hx.2 hgc.continuousOn
    (C := C) fun z _ => (Real.norm_eq_abs _).symm.le.trans (hC z) |>.trans_eq' rfl
  refine tendsto_nhds_unique h1 (h2.congr fun k => ?_)
  exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)

/-- **The Dirichlet pairings of `f − q` are those of the source**, along the source test functions of an admissible
word. -/
theorem tendsto_integral_srcTestW_mul_eq_recode {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x)
    (U : Opens ℂ) (hU : U ≤ upperHalfPlaneOpens) (g : MarkovZB.zsSub (U : Set ℂ)) :
    Tendsto (fun k => ∫ z, srcTestW κ ρL ρR r x k z * g.1 z) atTop
      (𝓝 (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (recodeShift κ x.1 x.2 ρL ρR r)
        (lapTest U g))) := by
  have hgc : Continuous g.1 := g.2.1.continuous
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support g.2.2.1
  rw [smoothDist_recodeShift_lapTest hx U hU g]
  have h2 := tendsto_integral_mul_srcTestW (κ := κ) (ρL := ρL) (ρR := ρR) hx (u := g.1) hgc.continuousOn
    (C := C) fun z _ => (Real.norm_eq_abs _).symm.le.trans (hC z) |>.trans_eq' rfl
  refine h2.congr fun k => ?_
  exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)

end Word

end LocalExt

end InteractingSLE
