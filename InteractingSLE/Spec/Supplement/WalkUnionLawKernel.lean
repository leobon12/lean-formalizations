/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.PushforwardLaw
import InteractingSLE.Spec.Sec7.DeterminationMixture
import InteractingSLE.Spec.Supplement.WalkPastLaw

/-!
# A zero-boundary GFF on a random open set under the regular conditional law

Packet PROVE-T14-WALKLAW (generic tool for the kernel form of Lemma GW3's union law). The union law of the two walks
is obtained as a family of conditional characteristic functionals: for every test function `φ`, almost surely on the
event that `φ` is supported in the random open set `U ω`, the characteristic value of the field at `φ` under the regular
conditional law is Gaussian with mean `m ω (φ)` and the zero-boundary variance of `U ω`. This file turns such a family
into the statement used by `GW3Between.GW3UnionLawBetweenRegStatement`: for almost every `ω₀`, under
`condExpKernel P 𝒢 ω₀`, the field restricted to `U ω₀` minus `m ω₀` is a zero-boundary GFF process on `U ω₀`.

The proof follows PROVE-PUSHFWD's support-restricted step (`RandomTest.condExp_cexp_apply_ae_eq_of_subset`): the
kernel law of the field is identified on each of the countably many finite unions of basis sets inside `U ω₀`
(`RandomTest.ext_of_integral_cexp_rat` against the Gaussian reference law `RandomTest.exists_gaussExtLaw`), hence the
characteristic value is known at every test function supported in `U ω₀` (`RandomTest.exists_basisUnion`); one
dimensional characteristic values of a linear random distribution then determine the process
(`isZBGFFProcess_of_integral_cexp_eq_on`, PROVE-LOCALEXT-D's `isZBGFFProcess_of_integral_cexp_eq` on any open set).

## Main results

* `isZBGFFProcess_of_integral_cexp_eq_on`;
* `integral_cexp_zbLaw`: the characteristic values of the zero-boundary GFF law on an open set `V ⊆ ℍ`;
* **`ae_isZBGFFProcess_condExpKernel_of_integral`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (TestOn DistOn IsZBGFFProcess IsZeroBoundaryGFF zbPath)

namespace InteractingSLE

namespace Theorem14

namespace WalkLaw

/-! ### One-dimensional characteristic values determine a zero-boundary GFF process on an open set -/

section Proc

/-- **Equal one-dimensional characteristic functions of linear random distributions on `V` give a zero-boundary GFF
process on `V`** (PROVE-LOCALEXT-D's `LocalExt.isZBGFFProcess_of_integral_cexp_eq`, for any open set `V`). -/
theorem isZBGFFProcess_of_integral_cexp_eq_on {V : Opens ℂ} {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {Q : Measure Ω} [IsProbabilityMeasure Q] {P : Measure Ω'} {X : Ω → DistOn V}
    (hX : Measurable X) (m : DistOn V) {X' : Ω' → DistOn V} (m' : DistOn V)
    (href : IsZBGFFProcess V (fun φ ω => X' ω φ - m' φ) P)
    (hcf : ∀ φ : TestOn V, ∫ ω, Complex.exp (Complex.I * ((X ω φ - m φ : ℝ) : ℂ)) ∂Q =
      ∫ ω, Complex.exp (Complex.I * ((X' ω φ - m' φ : ℝ) : ℂ)) ∂P) :
    IsZBGFFProcess V (fun φ ω => X ω φ - m φ) Q := by
  classical
  have hP : IsProbabilityMeasure P := href.gaussian.isProbabilityMeasure
  set Y : TestOn V → Ω → ℝ := fun φ ω => X ω φ - m φ with hYdef
  set Y' : TestOn V → Ω' → ℝ := fun φ ω => X' ω φ - m' φ with hY'def
  have hYm : ∀ φ, Measurable (Y φ) := fun φ => ((LQGMetric.measurable_distOn_apply φ).comp hX).sub_const _
  have hm : Measurable (zbPath Y) := measurable_pi_iff.2 hYm
  have hm' : Measurable (zbPath Y') := measurable_pi_iff.2 href.measurable
  have hlin : ∀ (I : Finset (TestOn V)) (L : StrongDual ℝ (I → ℝ)),
      (∀ ω, L (I.restrict (zbPath Y ω)) = Y (∑ i : I, L (fun j => if i = j then 1 else 0) • (i : TestOn V)) ω) ∧
      (∀ ω, L (I.restrict (zbPath Y' ω)) =
        Y' (∑ i : I, L (fun j => if i = j then 1 else 0) • (i : TestOn V)) ω) := by
    intro I L
    have key : ∀ (T : DistOn V) (c : DistOn V),
        L (fun i : I => T i - c i) = T (∑ i : I, L (fun j => if i = j then 1 else 0) • (i : TestOn V)) -
          c (∑ i : I, L (fun j => if i = j then 1 else 0) • (i : TestOn V)) := by
      intro T c
      have e := LinearMap.pi_apply_eq_sum_univ (L : (I → ℝ) →ₗ[ℝ] ℝ) (fun i : I => T i - c i)
      rw [ContinuousLinearMap.coe_coe] at e
      rw [e, map_sum, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      ring
    exact ⟨fun ω => key (X ω) m, fun ω => key (X' ω) m'⟩
  have hfin : ∀ I : Finset (TestOn V),
      (Q.map (zbPath Y)).map I.restrict = (P.map (zbPath Y')).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hm, Measure.map_map (Finset.measurable_restrict I) hm']
    refine Measure.ext_of_charFunDual (funext fun L => ?_)
    rw [charFunDual_apply, charFunDual_apply,
      integral_map ((Finset.measurable_restrict I).comp hm).aemeasurable (by fun_prop),
      integral_map ((Finset.measurable_restrict I).comp hm').aemeasurable (by fun_prop)]
    obtain ⟨h1, h2⟩ := hlin I L
    simp only [Function.comp_apply, h1, h2]
    have := hcf (∑ i : I, L (fun j => if i = j then 1 else 0) • (i : TestOn V))
    simp only [mul_comm _ Complex.I]
    exact this
  have hlaw : Q.map (zbPath Y) = P.map (zbPath Y') :=
    IsProjectiveLimit.unique (P := fun I => (P.map (zbPath Y')).map I.restrict) hfin fun _ => rfl
  exact Determination.isZBGFFProcess_of_hasLaw href hYm ⟨hm.aemeasurable, hlaw⟩

/-- The characteristic values of the zero-boundary GFF law on an open `V ⊆ ℍ`. -/
theorem integral_cexp_zbLaw {V : Opens ℂ} (hV : (V : Set ℂ) ⊆ H) (φ : TestOn V) :
    ∫ g, Complex.exp (Complex.I * ((g φ - (0 : DistOn V) φ : ℝ) : ℂ)) ∂(Coupling.zbLaw V) =
      ((Real.exp (-(1 / 2) * zeroGFFTestCov V φ φ) : ℝ) : ℂ) := by
  have hZ := Coupling.isZeroBoundaryGFF_zbLaw hV
  have hproc := hZ.process
  have hGa : HasGaussianLaw (fun g : DistOn V => g φ) (Coupling.zbLaw V) :=
    hproc.gaussian.hasGaussianLaw_eval φ
  have hc : ∫ g, (fun g : DistOn V => g φ) g ∂(Coupling.zbLaw V) = 0 := hproc.centered φ
  have hcov : cov[fun g : DistOn V => g φ, fun g : DistOn V => g φ; Coupling.zbLaw V] =
      zeroGFFTestCov V φ φ := hproc.covariance_eq φ φ
  simp only [zero_apply, sub_zero]
  rw [GFF.integral_exp_I_mul_of_hasGaussianLaw hGa hc, ← covariance_self hGa.aemeasurable, hcov]

end Proc

/-! ### The kernel form -/

section Kernel

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- `exp(i (a − c)) = exp(i a) · exp(−i c)`. -/
theorem cexp_I_mul_sub (a c : ℝ) :
    Complex.exp (Complex.I * ((a - c : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (a : ℂ)) * Complex.exp (-(Complex.I * (c : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Gaussian law on `𝒟'(V)` with mean `∫ M · ψ` (`M` continuous on `V ⊆ ℍ`) and the zero-boundary covariance
of `V`. -/
theorem exists_gaussLawOn {V : Opens ℂ} (hV : (V : Set ℂ) ⊆ H) {M : ℂ → ℝ} (hM : ContinuousOn M V) :
    ∃ μ : Measure (DistOn V), IsProbabilityMeasure μ ∧
      ∀ ψ : TestOn V, ∫ u, Complex.exp (Complex.I * (u ψ : ℂ)) ∂μ =
        Complex.exp (Complex.I * ((∫ z, M z * ψ z : ℝ) : ℂ) - (((1 / 2 : ℝ) * zeroGFFTestCov V ψ ψ : ℝ) : ℂ)) := by
  set d : DistOn V := SupercriticalConformalCovariance.GM24.smoothDist V M with hd
  have hadd : Measurable fun u : DistOn V => u + d :=
    LQGMetric.measurable_distOn_iff.2 fun φ => (LQGMetric.measurable_distOn_apply φ).add_const _
  have hP : IsProbabilityMeasure (Coupling.zbLaw V) :=
    (Coupling.isZeroBoundaryGFF_zbLaw hV).process.gaussian.isProbabilityMeasure
  refine ⟨(Coupling.zbLaw V).map fun u => u + d, inferInstance, fun ψ => ?_⟩
  rw [integral_map hadd.aemeasurable
    (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply ψ)).aestronglyMeasurable]
  have e : ∀ u : DistOn V, Complex.exp (Complex.I * ((u + d) ψ : ℂ)) =
      Complex.exp (Complex.I * ((u ψ - (0 : DistOn V) ψ : ℝ) : ℂ)) * Complex.exp (Complex.I * (d ψ : ℂ)) :=
    fun u => by
      rw [← Complex.exp_add]
      congr 1
      change Complex.I * ((u ψ + d ψ : ℝ) : ℂ) = _
      simp only [zero_apply, sub_zero]
      push_cast
      ring
  simp_rw [e]
  rw [integral_mul_const, integral_cexp_zbLaw hV ψ, Complex.ofReal_exp, ← Complex.exp_add, hd,
    SupercriticalConformalCovariance.GM24.smoothDist_apply hM]
  congr 1
  simp_rw [mul_comm (ψ _) (M _)]
  push_cast
  ring

/-- **A zero-boundary GFF on a random open set under the regular conditional law.** Suppose that for every test
function `φ`, for almost every `ω₀` with `φ` supported in the open set `U ω₀ ⊆ ℍ`, the characteristic value of `X` at
`φ` under `condExpKernel P 𝒢 ω₀` is `exp(i ∫ M ω₀ · φ − ½ ‖φ‖²_{H⁻¹(U ω₀)})`. Then for almost every `ω₀` at which
`U ω₀` is open and `M ω₀` is continuous on it, under `condExpKernel P 𝒢 ω₀` the pairings of `X − M ω₀` with the test
functions of `U ω₀` form a zero-boundary GFF process on `U ω₀`. -/
theorem ae_isZBGFFProcess_condExpKernel_of_integral {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X)
    {U : Ω → Set ℂ} (hUH : ∀ ω, U ω ⊆ H) {M : Ω → ℂ → ℝ}
    (hcf : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω₀ ∂P, tsupport φ ⊆ U ω₀ →
      ∫ ω, Complex.exp (Complex.I * (X ω φ : ℂ)) ∂(condExpKernel P 𝒢 ω₀) =
        Complex.exp (Complex.I * ((∫ z, M ω₀ z * φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (U ω₀) φ φ : ℝ) : ℂ))) :
    ∀ᵐ ω₀ ∂P, ∀ hUo : IsOpen (U ω₀), ContinuousOn (M ω₀) (U ω₀) →
      IsZBGFFProcess ⟨U ω₀, hUo⟩
        (fun ψ ω => X ω (GFF.testIncl ⟨U ω₀, hUo⟩ upperHalfPlaneOpens ψ) - ∫ z, M ω₀ z * ψ z)
        (condExpKernel P 𝒢 ω₀) := by
  classical
  have : Countable RandomTest.basisFamilies := RandomTest.countable_basisFamilies.to_subtype
  have hall : ∀ᵐ ω₀ ∂P, ∀ p : RandomTest.basisFamilies × (Σ s : Finset (ℕ × ℕ), (s → ℚ)),
      tsupport (GFF.testIncl (RandomTest.basisUnion p.1.1) upperHalfPlaneOpens
        (∑ i : p.2.1, (p.2.2 i : ℝ) • LQGMetric.distGen (RandomTest.basisUnion p.1.1) i)) ⊆ U ω₀ →
      ∫ ω, Complex.exp (Complex.I * (X ω (GFF.testIncl (RandomTest.basisUnion p.1.1) upperHalfPlaneOpens
        (∑ i : p.2.1, (p.2.2 i : ℝ) • LQGMetric.distGen (RandomTest.basisUnion p.1.1) i)) : ℂ))
          ∂(condExpKernel P 𝒢 ω₀) =
        Complex.exp (Complex.I * ((∫ z, M ω₀ z * (GFF.testIncl (RandomTest.basisUnion p.1.1) upperHalfPlaneOpens
          (∑ i : p.2.1, (p.2.2 i : ℝ) • LQGMetric.distGen (RandomTest.basisUnion p.1.1) i)) z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (U ω₀)
            (GFF.testIncl (RandomTest.basisUnion p.1.1) upperHalfPlaneOpens
              (∑ i : p.2.1, (p.2.2 i : ℝ) • LQGMetric.distGen (RandomTest.basisUnion p.1.1) i))
            (GFF.testIncl (RandomTest.basisUnion p.1.1) upperHalfPlaneOpens
              (∑ i : p.2.1, (p.2.2 i : ℝ) • LQGMetric.distGen (RandomTest.basisUnion p.1.1) i)) : ℝ) : ℂ)) :=
    ae_all_iff.2 fun p => hcf _
  filter_upwards [hall] with ω₀ hω₀ hUo hMc
  set V : Opens ℂ := ⟨U ω₀, hUo⟩ with hVdef
  have hVH : (V : Set ℂ) ⊆ H := hUH ω₀
  have hle : V ≤ upperHalfPlaneOpens := fun z hz => hVH hz
  obtain ⟨μ, hμP, hμ⟩ := exists_gaussLawOn hVH hMc
  have hfX : ∀ φ : TestOn upperHalfPlaneOpens,
      AEStronglyMeasurable (fun u : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (u φ : ℂ)))
        ((condExpKernel P 𝒢 ω₀).map X) := fun φ =>
    (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply φ)).aestronglyMeasurable
  have hmap : ∀ (R D : Opens ℂ) (ν' : Measure (DistOn D)) (ψ : TestOn R),
      ∫ v, Complex.exp (Complex.I * (v ψ : ℂ)) ∂(ν'.map (GFF.restrictDist R)) =
        ∫ u, Complex.exp (Complex.I * (u (GFF.testIncl R D ψ) : ℂ)) ∂ν' := fun R D ν' ψ => by
    rw [integral_map (GFF.measurable_restrictDist R).aemeasurable
      (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply ψ)).aestronglyMeasurable]
    rfl
  -- the kernel law of `X` agrees with the reference on every basis union inside `V`
  have hB : ∀ F : RandomTest.basisFamilies, (RandomTest.basisUnion F.1 : Set ℂ) ⊆ U ω₀ →
      ((condExpKernel P 𝒢 ω₀).map X).map (GFF.restrictDist (RandomTest.basisUnion F.1)) =
        μ.map (GFF.restrictDist (RandomTest.basisUnion F.1)) := by
    intro F hFU
    have hleH : RandomTest.basisUnion F.1 ≤ upperHalfPlaneOpens := fun x hx => hUH ω₀ (hFU hx)
    have hleV : RandomTest.basisUnion F.1 ≤ V := fun x hx => hFU hx
    refine RandomTest.ext_of_integral_cexp_rat fun s q => ?_
    have hts : tsupport (GFF.testIncl (RandomTest.basisUnion F.1) upperHalfPlaneOpens
        (∑ i : s, (q i : ℝ) • LQGMetric.distGen (RandomTest.basisUnion F.1) i)) ⊆ U ω₀ := by
      rw [GFF.coe_testIncl hleH]
      exact (TestFunction.tsupport_subset _).trans hFU
    rw [hmap, hmap, integral_map hX.aemeasurable (hfX _), hω₀ ⟨F, ⟨s, q⟩⟩ hts, hμ,
      GFF.coe_testIncl hleH, GFF.coe_testIncl hleV]
    rfl
  -- the characteristic value at every test function of `V`
  have hC : ∀ ψ : TestOn V,
      ∫ ω, Complex.exp (Complex.I * (X ω (GFF.testIncl V upperHalfPlaneOpens ψ) : ℂ)) ∂(condExpKernel P 𝒢 ω₀) =
        Complex.exp (Complex.I * ((∫ z, M ω₀ z * ψ z : ℝ) : ℂ) - (((1 / 2 : ℝ) * zeroGFFTestCov V ψ ψ : ℝ) : ℂ)) := by
    intro ψ
    obtain ⟨F, hF, hψF, hFU⟩ := RandomTest.exists_basisUnion ψ.hasCompactSupport.isCompact hUo ψ.tsupport_subset
    have hleH : RandomTest.basisUnion F ≤ upperHalfPlaneOpens := fun x hx => hUH ω₀ (hFU hx)
    have hleV : RandomTest.basisUnion F ≤ V := fun x hx => hFU hx
    set TR : TestOn (RandomTest.basisUnion F) := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hψF⟩ with hTR
    have hTeH : GFF.testIncl (RandomTest.basisUnion F) upperHalfPlaneOpens TR =
        GFF.testIncl V upperHalfPlaneOpens ψ := by
      ext z
      rw [GFF.coe_testIncl hleH, GFF.coe_testIncl hle]
      rfl
    have hTeV : GFF.testIncl (RandomTest.basisUnion F) V TR = ψ := by
      ext z
      rw [GFF.coe_testIncl hleV]
      rfl
    have key := congrArg (fun μ' : Measure (DistOn (RandomTest.basisUnion F)) =>
      ∫ v, Complex.exp (Complex.I * (v TR : ℂ)) ∂μ') (hB ⟨F, hF⟩ hFU)
    simp only at key
    rw [hmap, hmap, hTeH, hTeV] at key
    rw [← integral_map hX.aemeasurable (hfX _), key, hμ]
  -- one-dimensional characteristic values on `V`
  have href : IsZBGFFProcess V (fun φ (g : DistOn V) => g φ - (0 : DistOn V) φ) (Coupling.zbLaw V) := by
    have hp := (Coupling.isZeroBoundaryGFF_zbLaw hVH).process
    simp only [zero_apply, sub_zero]
    exact hp
  have hres := isZBGFFProcess_of_integral_cexp_eq_on (Q := condExpKernel P 𝒢 ω₀)
    (X := fun ω => GFF.restrictDist V (X ω)) ((GFF.measurable_restrictDist V).comp hX)
    (SupercriticalConformalCovariance.GM24.smoothDist V (M ω₀)) (X' := id) 0 href (fun ψ => by
      show _ = ∫ g : DistOn V, Complex.exp (Complex.I * ((g ψ - (0 : DistOn V) ψ : ℝ) : ℂ)) ∂(Coupling.zbLaw V)
      rw [integral_cexp_zbLaw hVH ψ]
      simp only [GFF.restrictDist_apply, SupercriticalConformalCovariance.GM24.smoothDist_apply (B := V) hMc]
      simp_rw [cexp_I_mul_sub]
      rw [integral_mul_const, hC ψ, ← Complex.exp_add, Complex.ofReal_exp]
      congr 1
      simp_rw [mul_comm (ψ _) (M ω₀ _)]
      push_cast
      ring)
  have e : (fun φ ω => GFF.restrictDist V (X ω) φ - SupercriticalConformalCovariance.GM24.smoothDist V (M ω₀) φ) =
      fun ψ ω => X ω (GFF.testIncl V upperHalfPlaneOpens ψ) - ∫ z, M ω₀ z * ψ z := by
    funext ψ ω
    rw [GFF.restrictDist_apply, SupercriticalConformalCovariance.GM24.smoothDist_apply (B := V) hMc]
    simp_rw [mul_comm (ψ _) (M ω₀ _)]
  rw [e] at hres
  exact hres

end Kernel

end WalkLaw

end Theorem14

end InteractingSLE
