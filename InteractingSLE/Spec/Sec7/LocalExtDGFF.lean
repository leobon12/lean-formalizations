/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtDStep5
import InteractingSLE.Spec.Coupling.MartMeans2Lemma71
import InteractingSLE.Spec.Sec7.DeterminationMixture

/-!
# Step 6, the GFF clause: a linear random distribution with Gaussian characteristic functional is a zero-boundary GFF

Packet PROVE-LOCEXT-D, item 3 (the GFF clause (E3) of the extension in Aux. lemma 54, p. 246). A two-seed extension over
`(Ω, Q)` with field `h₀ ∘ fst` satisfies the frozen GFF conjunct exactly when `h₀ − 𝔥⁰` is a zero-boundary GFF process
under `Q`.

* **`isZBGFFProcess_of_integral_cexp_eq`**: if two linear random distributions `X − m` (under `Q`) and `X' − m'` (under
  `P`, a zero-boundary GFF process) have the same characteristic function `E[e^{i(X − m)(φ)}]` at every test function,
  then `X − m` is a zero-boundary GFF process under `Q`. By linearity, the characteristic function of every finite family
  `((X − m)(φ_i))_i` at `L` is that of the single pairing `(X − m)(Σ_i L(e_i) φ_i)`, so the finite-dimensional laws agree
  (`Measure.ext_of_charFunDual`), hence the path laws (`IsProjectiveLimit.unique`), and `isZBGFFProcess_of_hasLaw`
  applies;
* `integral_cexp_sub_bheAt_eq` / `integral_cexp_recode_sub_eq`: the time-0 characteristic functionals of the original
  field under `P` and of the recoded field under `Q`, both `e^{−E₀(φ)/2}` (the frozen kernels at `τ = 0`; `K₀ = ∅`);
* **`isZBGFFProcess_recode_srcMeasure`**: `h₀ − 𝔥⁰₀` is a zero-boundary GFF process under `Q`, for every bounded harmonic
  extension `𝔥⁰₀` of the two-seed time-0 data — the GFF conjunct of the two-seed extension.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace InteractingSLE

namespace LocalExt

open LQGMetric QuantumZipper

/-- **Equal one-dimensional characteristic functions of linear random distributions give a zero-boundary GFF.** -/
theorem isZBGFFProcess_of_integral_cexp_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {P : Measure Ω'} {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X)
    (m : DistOn upperHalfPlaneOpens) {X' : Ω' → DistOn upperHalfPlaneOpens} (m' : DistOn upperHalfPlaneOpens)
    (href : IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => X' ω φ - m' φ) P)
    (hcf : ∀ φ : TestOn upperHalfPlaneOpens, ∫ ω, Complex.exp (Complex.I * ((X ω φ - m φ : ℝ) : ℂ)) ∂Q =
      ∫ ω, Complex.exp (Complex.I * ((X' ω φ - m' φ : ℝ) : ℂ)) ∂P) :
    IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => X ω φ - m φ) Q := by
  classical
  have hP : IsProbabilityMeasure P := href.gaussian.isProbabilityMeasure
  set Y : TestOn upperHalfPlaneOpens → Ω → ℝ := fun φ ω => X ω φ - m φ with hYdef
  set Y' : TestOn upperHalfPlaneOpens → Ω' → ℝ := fun φ ω => X' ω φ - m' φ with hY'def
  have hYm : ∀ φ, Measurable (Y φ) := fun φ => (measurable_distOn_apply' hX φ).sub_const _
  have hm : Measurable (zbPath Y) := measurable_pi_iff.2 hYm
  have hm' : Measurable (zbPath Y') := measurable_pi_iff.2 href.measurable
  -- the pairing of a finite family with a linear form is the pairing with one test function
  have hlin : ∀ (I : Finset (TestOn upperHalfPlaneOpens)) (L : StrongDual ℝ (I → ℝ)),
      (∀ ω, L (I.restrict (zbPath Y ω)) = Y (∑ i : I, L (fun j => if i = j then 1 else 0) • (i : TestOn upperHalfPlaneOpens)) ω) ∧
      (∀ ω, L (I.restrict (zbPath Y' ω)) =
        Y' (∑ i : I, L (fun j => if i = j then 1 else 0) • (i : TestOn upperHalfPlaneOpens)) ω) := by
    intro I L
    have key : ∀ (T : DistOn upperHalfPlaneOpens) (c : DistOn upperHalfPlaneOpens),
        L (fun i : I => T i - c i) = T (∑ i : I, L (fun j => if i = j then 1 else 0) • (i : TestOn upperHalfPlaneOpens)) -
          c (∑ i : I, L (fun j => if i = j then 1 else 0) • (i : TestOn upperHalfPlaneOpens)) := by
      intro T c
      have e := LinearMap.pi_apply_eq_sum_univ (L : (I → ℝ) →ₗ[ℝ] ℝ) (fun i : I => T i - c i)
      rw [ContinuousLinearMap.coe_coe] at e
      rw [e, map_sum, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      ring
    exact ⟨fun ω => key (X ω) m, fun ω => key (X' ω) m'⟩
  have hfin : ∀ I : Finset (TestOn upperHalfPlaneOpens),
      (Q.map (zbPath Y)).map I.restrict = (P.map (zbPath Y')).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hm, Measure.map_map (Finset.measurable_restrict I) hm']
    refine Measure.ext_of_charFunDual (funext fun L => ?_)
    rw [charFunDual_apply, charFunDual_apply,
      integral_map ((Finset.measurable_restrict I).comp hm).aemeasurable (by fun_prop),
      integral_map ((Finset.measurable_restrict I).comp hm').aemeasurable (by fun_prop)]
    obtain ⟨h1, h2⟩ := hlin I L
    simp only [Function.comp_apply, h1, h2]
    have := hcf (∑ i : I, L (fun j => if i = j then 1 else 0) • (i : TestOn upperHalfPlaneOpens))
    simp only [mul_comm _ Complex.I]
    exact this
  have hlaw : Q.map (zbPath Y) = P.map (zbPath Y') :=
    IsProjectiveLimit.unique (P := fun I => (P.map (zbPath Y')).map I.restrict) hfin fun _ => rfl
  exact Determination.isZBGFFProcess_of_hasLaw href hYm ⟨hm.aemeasurable, hlaw⟩

/-! ### The time-0 characteristic functionals -/

section TimeZero

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

theorem integral_eq_of_condExp_ae_eq_const {Ω' : Type*} {m mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ') {f : Ω' → ℂ} {c : ℂ}
    (hc : μ[f | m] =ᵐ[μ] fun _ => c) : ∫ ω, f ω ∂μ = c := by
  rw [← integral_condExp hm, integral_congr_ae hc]
  simp

/-- On a good path with an admissible seed, the lifetime is positive and the hull at time `0` is empty. -/
theorem fwdHull_zero_of_isGoodPath {ω : Ω} (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    fwdHull (fun s : ℝ => W s.toNNReal ω) ((0 : ℝ≥0) : ℝ) = ∅ := by
  have hζ : 0 < ζ ω := lt_of_le_of_lt zero_le (localStopPath_lt hg.1 hF hr hseed hg.2)
  exact Coupling.MartMeans2.fwdHull_rpath_zero hg.continuousOn_W hζ

/-- The time-0 kernel of a coupling, integrated: `E[e^{i(h(φ) − ∫ 𝔥₀ φ)}] = e^{−E₀(φ)/2}`. -/
theorem integral_cexp_sub_bheAt_eq (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * ((h ω φ - ∫ z, bheAt κ ρL ρR xL xR z * φ z : ℝ) : ℂ)) ∂P =
      ((Real.exp (-(1 / 2) * loewnerGreenEnergy (fun _ => 0) 0 φ) : ℝ) : ℂ) := by
  have hP : IsProbabilityMeasure P := hC.1.1.isProbabilityMeasure'
  have hgood := ae_isGoodPath hC.1 hκ
  obtain ⟨hX', hker⟩ := hC.2.2.2
  have hτ : IsStoppingTime (drivingFiltration P hX') fun _ : Ω => ((0 : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const _ _
  have hτζ : ∀ᵐ ω ∂P, ((((0 : ℝ≥0) : WithTop ℝ≥0)) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hgood] with ω hg
    exact lt_of_le_of_lt zero_le (localStopPath_lt hg.1 hF hr hseed hg.2)
  obtain ⟨-, hK⟩ := hker _ hτ hτζ
  have hk := hK (fun ω => bheAt κ ρL ρR (fun i => VL i 0 ω - W 0 ω) (fun i => VR i 0 ω - W 0 ω))
    (fun ω => isBoundedHarmonicExtension_bheAt κ ρL ρR _ _) φ
  set c : ℂ := Complex.exp (Complex.I * ((∫ z, bheAt κ ρL ρR xL xR z * φ z : ℝ) : ℂ) -
    (((1 / 2 : ℝ) * loewnerGreenEnergy (fun _ => 0) 0 φ : ℝ) : ℂ)) with hcdef
  have hint : Integrable (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) P :=
    Integrable.of_bound (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_distOn_apply' hC.2.1 φ)))).aestronglyMeasurable 1 (ae_of_all _ fun ω => (norm_cexp_I_mul _).le)
  have hcond : P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | hτ.measurableSpace] =ᵐ[P] fun _ => c := by
    filter_upwards [hk, hgood] with ω hω hg
    have hdis : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω)
        ((((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) : ℝ)) := by
      rw [WithTop.untopD_coe, fwdHull_zero_of_isGoodPath hg hF hr hseed]
      exact disjoint_empty _
    rw [hω hdis, hcdef]
    have hpu := hg.isSLEPathUpTo
    have hw0 : W 0 ω = 0 := hpu.w_zero
    have hvL : (fun i => VL i 0 ω - W 0 ω) = xL := funext fun i => by rw [hpu.vL_zero i, hw0, sub_zero]
    have hvR : (fun i => VR i 0 ω - W 0 ω) = xR := funext fun i => by rw [hpu.vR_zero i, hw0, sub_zero]
    have hw0' : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by simpa using hw0
    simp only [WithTop.untopD_coe, NNReal.coe_zero]
    rw [hvL, hvR, Coupling.MartMeans2.loewnerGreenEnergy_zero_eq hw0' φ]
    congr 4
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
    · have hzH : z ∈ H := Coupling.tsupport_subset_H φ hz
      have hz0 : z ≠ 0 := fun h0 => by
        have : (0 : ℝ) < z.im := hzH
        rw [h0, Complex.zero_im] at this; exact lt_irrefl _ this
      rw [Coupling.MartMeans2.couplingMean_zero κ (w := fun s : ℝ => W s.toNNReal ω) hw0'
        (bheAt κ ρL ρR xL xR) hz0]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  have hI := integral_eq_of_condExp_ae_eq_const hτ.measurableSpace_le hcond
  have e : (fun ω => Complex.exp (Complex.I * ((h ω φ - ∫ z, bheAt κ ρL ρR xL xR z * φ z : ℝ) : ℂ))) =
      fun ω => Complex.exp (-(Complex.I * ((∫ z, bheAt κ ρL ρR xL xR z * φ z : ℝ) : ℂ))) *
        Complex.exp (Complex.I * (h ω φ : ℂ)) := by
    funext ω
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e, integral_const_mul, hI, hcdef, ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The merged seed positions at time `0` vanish on a good path. -/
theorem seedPos_zero_of_isGoodPath {ω : Ω} (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) :
    seedPosL xL W VL (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) ω = 0 ∧
      seedPosR xR W VR (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) ω = 0 := by
  have hpu := hg.isSLEPathUpTo
  have hw0 : W 0 ω = 0 := hpu.w_zero
  constructor
  · unfold seedPosL seedVal cposL
    split_ifs with hs
    · simp only [WithTop.untopD_coe]
      rw [hpu.vL_zero, hw0, sub_zero]
      exact hs.choose_spec
    · rfl
  · unfold seedPosR seedVal cposR
    split_ifs with hs
    · simp only [WithTop.untopD_coe]
      rw [hpu.vR_zero, hw0, sub_zero]
      exact hs.choose_spec
    · rfl

/-- The time-0 kernel of the recoded field under `Q`, integrated: `E_Q[e^{i(h₀(φ) − ∫ 𝔥⁰₀ φ)}] = e^{−E₀(φ)/2}`, for every
bounded harmonic extension `𝔥⁰₀` of the two-seed data at time `0`. -/
theorem integral_cexp_recode_sub_eq (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    {u₂ : ℂ → ℝ}
    (hu₂ : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL)
      (fun _ : Fin 1 => seedSumR xR ρR) LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₂)
    (φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * ((recode κ xL xR ρL ρR r (h ω) φ - ∫ z, u₂ z * φ z : ℝ) : ℂ))
        ∂(srcMeasure κ ρL ρR P hF hr h) =
      ((Real.exp (-(1 / 2) * loewnerGreenEnergy (fun _ => 0) 0 φ) : ℝ) : ℂ) := by
  have hP : IsProbabilityMeasure P := hC.1.1.isProbabilityMeasure'
  have hQ := isProbabilityMeasure_srcMeasure hκ hC hF hr hseed
  have hQP := srcMeasure_absolutelyContinuous (κ := κ) (ρL := ρL) (ρR := ρR) (P := P) (h := h) hF hr
  have hgood := hQP.ae_le (ae_isGoodPath hC.1 hκ)
  obtain ⟨hX', -⟩ := hC.2.2.2
  set τ : Ω → WithTop ℝ≥0 := fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0) with hτdef
  have hτ : IsStoppingTime (drivingFiltration P hX') τ := isStoppingTime_const _ _
  set u₂' : Ω → ℂ → ℝ := fun ω => Impl.forceExt κ (Ito.weightWord (fun _ : Fin 1 => seedSumL xL ρL)
    (fun _ : Fin 1 => seedSumR xR ρR)) (fun _ => seedPosL xL W VL τ ω) (fun _ => seedPosR xR W VR τ ω) with hu₂'def
  have hu₂' : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR)
        (fun _ => seedPosL xL W VL τ ω) (fun _ => seedPosR xR W VR τ ω))
      (forceJumpSet (fun _ : Fin 1 => seedPosL xL W VL τ ω) (fun _ : Fin 1 => seedPosR xR W VR τ ω)) (u₂' ω) :=
    fun ω => Impl.isBoundedHarmonicExtension_forceExt κ _ _ _
  have hk := condExp_recode_srcMeasure_eq_twoSeedKernel_of_pos hκ hC hF hr hseed hX' hτ
    (ae_of_all _ fun _ => zero_le) hu₂' φ
  set c : ℂ := Complex.exp (Complex.I * ((∫ z, u₂ z * φ z : ℝ) : ℂ) -
    (((1 / 2 : ℝ) * loewnerGreenEnergy (fun _ => 0) 0 φ : ℝ) : ℂ)) with hcdef
  have hcond : (srcMeasure κ ρL ρR P hF hr h)[fun ω => Complex.exp (Complex.I * (recode κ xL xR ρL ρR r (h ω) φ : ℂ)) |
      hτ.measurableSpace] =ᵐ[srcMeasure κ ρL ρR P hF hr h] fun _ => c := by
    filter_upwards [hk, hgood] with ω hω hg
    have hdis : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (((τ ω).untopD 0 : ℝ≥0) : ℝ)) := by
      rw [hτdef, WithTop.untopD_coe, fwdHull_zero_of_isGoodPath hg hF hr hseed]
      exact disjoint_empty _
    rw [hω hdis, hcdef]
    have hpu := hg.isSLEPathUpTo
    have hw0 : W 0 ω = 0 := hpu.w_zero
    have hw0' : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by simpa using hw0
    obtain ⟨hsL, hsR⟩ := seedPos_zero_of_isGoodPath (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) hg
    simp only [hτdef, WithTop.untopD_coe, NNReal.coe_zero]
    rw [Coupling.MartMeans2.loewnerGreenEnergy_zero_eq hw0' φ]
    congr 4
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
    · have hzH : z ∈ H := Coupling.tsupport_subset_H φ hz
      have hz0 : z ≠ 0 := fun h0 => by
        have : (0 : ℝ) < z.im := hzH
        rw [h0, Complex.zero_im] at this; exact lt_irrefl _ this
      rw [Coupling.MartMeans2.couplingMean_zero κ (w := fun s : ℝ => W s.toNNReal ω) hw0' (u₂' ω) hz0]
      -- `u₂' ω = u₂` on `ℍ`
      have h1 : Impl.IsBoundedHarmonicExtension (Impl.forceBoundaryData κ (Ito.weightWord
          (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR)) LP.twoSeedXL LP.twoSeedXR)
          (Impl.forceJumpSet (Ito.weightWord (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR))
            LP.twoSeedXL LP.twoSeedXR) (u₂' ω) := by
        have := hu₂' ω
        rw [hτdef] at this
        simp only [hsL, hsR] at this
        exact this
      have h2 : Impl.IsBoundedHarmonicExtension (Impl.forceBoundaryData κ (Ito.weightWord
          (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR)) LP.twoSeedXL LP.twoSeedXR)
          (Impl.forceJumpSet (Ito.weightWord (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR))
            LP.twoSeedXL LP.twoSeedXR) u₂ := hu₂
      rw [Impl.eqOn_of_isBoundedHarmonicExtension (Impl.forceJumpSet_finite _ _ _) h2 h1 hzH]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  have hI := integral_eq_of_condExp_ae_eq_const hτ.measurableSpace_le hcond
  have e : (fun ω => Complex.exp (Complex.I * ((recode κ xL xR ρL ρR r (h ω) φ - ∫ z, u₂ z * φ z : ℝ) : ℂ))) =
      fun ω => Complex.exp (-(Complex.I * ((∫ z, u₂ z * φ z : ℝ) : ℂ))) *
        Complex.exp (Complex.I * (recode κ xL xR ρL ρR r (h ω) φ : ℂ)) := by
    funext ω
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e, integral_const_mul, hI, hcdef, ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- **The GFF clause of the two-seed extension (E3)**: under `Q = srcMeasure`, `h₀ − 𝔥⁰₀` is a zero-boundary GFF process
on `ℍ`, for every bounded harmonic extension `𝔥⁰₀` of the two-seed data at time `0` (weights `(seedSumL, seedSumR)` at
the positions `LP.twoSeedXL = LP.twoSeedXR = 0`). -/
theorem isZBGFFProcess_recode_srcMeasure (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    {u₂ : ℂ → ℝ}
    (hu₂ : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL)
      (fun _ : Fin 1 => seedSumR xR ρR) LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₂) :
    IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => recode κ xL xR ρL ρR r (h ω) φ - ∫ z, u₂ z * φ z)
      (srcMeasure κ ρL ρR P hF hr h) := by
  have hQ := isProbabilityMeasure_srcMeasure hκ hC hF hr hseed
  have hu₂c : ContinuousOn u₂ H := continuousOn_of_isBoundedHarmonicExtension hu₂
  have hu₀ := isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR
  have hu₀c : ContinuousOn (bheAt κ ρL ρR xL xR) H := continuousOn_of_isBoundedHarmonicExtension hu₀
  have href := hC.2.2.1 (bheAt κ ρL ρR xL xR) hu₀
  have e₁ : ∀ (u : ℂ → ℝ), ContinuousOn u H → ∀ φ : TestOn upperHalfPlaneOpens,
      ∫ z, u z * φ z = SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u φ := fun u hu φ => by
    rw [SupercriticalConformalCovariance.GM24.smoothDist_apply hu]
    exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have eQ : (fun φ ω => recode κ xL xR ρL ρR r (h ω) φ - ∫ z, u₂ z * φ z) = fun φ ω =>
      recode κ xL xR ρL ρR r (h ω) φ - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₂ φ := by
    funext φ ω; rw [e₁ u₂ hu₂c φ]
  have eP : (fun φ ω => h ω φ - ∫ z, bheAt κ ρL ρR xL xR z * φ z) = fun φ ω =>
      h ω φ - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (bheAt κ ρL ρR xL xR) φ := by
    funext φ ω; rw [e₁ _ hu₀c φ]
  rw [eP] at href
  rw [eQ]
  refine isZBGFFProcess_of_integral_cexp_eq (X := fun ω => recode κ xL xR ρL ρR r (h ω))
    (measurable_recode.comp hC.2.1) _ _ href fun φ => ?_
  rw [← e₁ u₂ hu₂c φ, ← e₁ _ hu₀c φ, integral_cexp_recode_sub_eq hκ hC hF hr hseed hu₂ φ,
    integral_cexp_sub_bheAt_eq hκ hC hF hr hseed φ]

end TimeZero

end LocalExt

end InteractingSLE
