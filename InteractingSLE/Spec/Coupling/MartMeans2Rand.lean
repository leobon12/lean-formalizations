/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.PushforwardLaw

/-!
# Conditional characteristic functionals at random test functions: the event form with local laws

Packet PROVE-CPL-MART2, part (2), probabilistic tool. PROVE-PUSHFWD's
`RandomTest.condExp_cexp_apply_ae_eq_of_subset` evaluates a conditional characteristic functional at a `𝒢`-measurable
random test function `T` supported in a random open set `U ω`, assuming (i) `tsupport (T ω) ⊆ U ω` for **every** `ω`
and (ii) each `Ψ ω` is the characteristic functional of a probability law on `𝒟'(V)`. For the coupling transported by a
random chart both are too strong: the support condition `supp φ' ∩ K_τ = ∅` is a random event that need not be
`𝒢`-measurable, and the conditional mean `𝔥_τ ∘ fwd` is a function on `U ω` that need not extend to a distribution on
`V` (it is only locally integrable on `U ω`). Here:

* `condExp_cexp_apply_ae_eq_of_local`: the conclusion holds almost surely **on the event** `{tsupport (T ω) ⊆ U ω}`,
  and (ii) is needed only almost surely and only **locally**: for every open `R ⊆ U ω`, the restriction of `Ψ ω` to
  `𝒟(R)` is the characteristic functional of a probability law on `𝒟'(R)`;
* `exists_gaussLocalLaw`: such local laws exist for `Ψ(φ) = exp(i ∫ m φ − ½ ‖φ‖²_{H⁻¹(U)})` whenever `m` is locally
  integrable on `R ⊆ U ⊆ ℍ` (the zero-boundary GFF on `U`, restricted to `R`, shifted by `m`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Coupling

namespace MartMeans2

/-! ### The event form with local laws -/

section CondRandom

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Conditional characteristic functional at a random test function, event form with local laws.** Let `X` be a
random distribution on `V`, `U ω ⊆ V` random open sets and `Ψ ω` functionals on `𝒟(V)` such that, conditionally on
`𝒢`, `E[exp(i X(φ)) | 𝒢] = Ψ(ω, φ)` almost surely on `{tsupport φ ⊆ U ω}`, for every fixed `φ`. Suppose that almost
surely, for every open `R ⊆ U ω`, the restriction of `Ψ ω` to `𝒟(R)` is the characteristic functional of a
probability law on `𝒟'(R)`. Then for every `𝒢`-measurable random test function `T`, almost surely on
`{tsupport (T ω) ⊆ U ω}`, `E[exp(i X(T)) | 𝒢] = Ψ(ω, T ω)`. -/
theorem condExp_cexp_apply_ae_eq_of_local (h𝒢 : 𝒢 ≤ mΩ) {V : Opens ℂ} {X : Ω → DistOn V}
    (hX : Measurable X) {U : Ω → Set ℂ} (hUo : ∀ ω, IsOpen (U ω)) (hUV : ∀ ω, U ω ⊆ V)
    {Ψ : Ω → TestOn V → ℂ}
    (hΨ : ∀ᵐ ω ∂P, ∀ R : Opens ℂ, (R : Set ℂ) ⊆ U ω → ∃ μ : Measure (DistOn R), IsProbabilityMeasure μ ∧
      ∀ ψ : TestOn R, ∫ v, Complex.exp (Complex.I * (v ψ : ℂ)) ∂μ = Ψ ω (GFF.testIncl R V ψ))
    (hcond : ∀ φ : TestOn V, ∀ᵐ ω ∂P, tsupport φ ⊆ U ω →
      P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | 𝒢] ω = Ψ ω φ)
    {T : Ω → TestOn V} (hT : ∀ z, Measurable[𝒢] fun ω => T ω z) :
    ∀ᵐ ω ∂P, tsupport (T ω) ⊆ U ω →
      P[fun ω => Complex.exp (Complex.I * (X ω (T ω) : ℂ)) | 𝒢] ω = Ψ ω (T ω) := by
  classical
  have hid : Measurable[mΩ, 𝒢] (id : Ω → Ω) := measurable_id'' h𝒢
  set κ := @condDistrib Ω Ω (DistOn V) _ _ _ mΩ 𝒢 X id P _ with hκ
  have hcomap : MeasurableSpace.comap (id : Ω → Ω) 𝒢 = 𝒢 := MeasurableSpace.comap_id
  -- Step A: the kernel has the right characteristic values at each fixed test function
  have hA : ∀ φ : TestOn V, ∀ᵐ ω ∂P, tsupport φ ⊆ U ω →
      ∫ u, Complex.exp (Complex.I * (u φ : ℂ)) ∂(κ ω) = Ψ ω φ := by
    intro φ
    have hf : StronglyMeasurable fun u : DistOn V => Complex.exp (Complex.I * (u φ : ℂ)) :=
      (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply φ)).stronglyMeasurable
    have h1 := @condExp_ae_eq_integral_condDistrib Ω Ω (DistOn V) ℂ _ _ _ _ mΩ P _ id X 𝒢 _ _ hid
      hX.aemeasurable _ hf (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hX))
    rw [hcomap] at h1
    filter_upwards [h1, hcond φ] with ω h1ω h2ω hsupp
    rw [← h2ω hsupp, h1ω]
    rfl
  -- Step B: on each basis union inside `U ω`, the restricted kernel has the characteristic functional `Ψ ω`
  have hmap : ∀ (R : Opens ℂ) (ν : Measure (DistOn V)) (ψ : TestOn R),
      ∫ v, Complex.exp (Complex.I * (v ψ : ℂ)) ∂(ν.map (GFF.restrictDist R)) =
        ∫ u, Complex.exp (Complex.I * (u (GFF.testIncl R V ψ) : ℂ)) ∂ν := fun R ν ψ => by
    rw [integral_map (GFF.measurable_restrictDist R).aemeasurable
      (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply ψ)).aestronglyMeasurable]
    rfl
  have : Countable RandomTest.basisFamilies := RandomTest.countable_basisFamilies.to_subtype
  have hB : ∀ᵐ ω ∂P, ∀ F : RandomTest.basisFamilies, (RandomTest.basisUnion F.1 : Set ℂ) ⊆ U ω →
      ∀ ψ : TestOn (RandomTest.basisUnion F.1),
        ∫ v, Complex.exp (Complex.I * (v ψ : ℂ)) ∂((κ ω).map (GFF.restrictDist (RandomTest.basisUnion F.1))) =
          Ψ ω (GFF.testIncl (RandomTest.basisUnion F.1) V ψ) := by
    have hall : ∀ᵐ ω ∂P, ∀ p : RandomTest.basisFamilies × (Σ s : Finset (ℕ × ℕ), (s → ℚ)),
        tsupport (GFF.testIncl (RandomTest.basisUnion p.1.1) V
          (∑ i : p.2.1, (p.2.2 i : ℝ) • LQGMetric.distGen (RandomTest.basisUnion p.1.1) i)) ⊆ U ω →
        ∫ u, Complex.exp (Complex.I * (u (GFF.testIncl (RandomTest.basisUnion p.1.1) V
          (∑ i : p.2.1, (p.2.2 i : ℝ) • LQGMetric.distGen (RandomTest.basisUnion p.1.1) i)) : ℂ)) ∂(κ ω) =
          Ψ ω (GFF.testIncl (RandomTest.basisUnion p.1.1) V
            (∑ i : p.2.1, (p.2.2 i : ℝ) • LQGMetric.distGen (RandomTest.basisUnion p.1.1) i)) :=
      ae_all_iff.2 fun p => hA _
    filter_upwards [hall, hΨ] with ω hω hΨω F hFU ψ
    have hle : RandomTest.basisUnion F.1 ≤ V := fun x hx => hUV ω (hFU hx)
    obtain ⟨μ, hμP, hμ⟩ := hΨω (RandomTest.basisUnion F.1) hFU
    have heq : (κ ω).map (GFF.restrictDist (RandomTest.basisUnion F.1)) = μ := by
      refine RandomTest.ext_of_integral_cexp_rat fun s q => ?_
      have hts : tsupport (GFF.testIncl (RandomTest.basisUnion F.1) V
          (∑ i : s, (q i : ℝ) • LQGMetric.distGen (RandomTest.basisUnion F.1) i)) ⊆ U ω := by
        rw [GFF.coe_testIncl hle]
        exact (TestFunction.tsupport_subset _).trans hFU
      rw [hmap, hω ⟨F, ⟨s, q⟩⟩ hts, hμ]
    rw [heq, hμ]
  -- Step C: disintegration at the random test function
  have hjoint : Measurable[(𝒢.prod inferInstance), _] fun p : Ω × DistOn V => p.2 (T p.1) :=
    @RandomTest.measurable_apply_of_forall_measurable (Ω × DistOn V) (𝒢.prod inferInstance) V (fun p => p.2)
      (@measurable_snd Ω (DistOn V) 𝒢 _) (fun p => T p.1)
      (fun z => (hT z).comp (@measurable_fst Ω (DistOn V) 𝒢 _))
  have hf : StronglyMeasurable[(𝒢.prod inferInstance)]
      fun p : Ω × DistOn V => Complex.exp (Complex.I * (p.2 (T p.1) : ℂ)) :=
    (@GFF.measurable_exp_I_mul (Ω × DistOn V) (𝒢.prod inferInstance) _ hjoint).stronglyMeasurable
  have hTm : Measurable fun ω => X ω (T ω) :=
    RandomTest.measurable_apply_of_forall_measurable hX fun z => (hT z).mono h𝒢 le_rfl
  have h2 := @condExp_prod_ae_eq_integral_condDistrib Ω Ω (DistOn V) ℂ _ _ _ _ mΩ P _ id X 𝒢
    (fun p => Complex.exp (Complex.I * (p.2 (T p.1) : ℂ))) _ _ hid hX.aemeasurable hf
    (GFF.integrable_exp_I_mul hTm)
  rw [hcomap] at h2
  filter_upwards [h2, hB] with ω h2ω hBω hTU
  refine (show P[fun ω => Complex.exp (Complex.I * (X ω (T ω) : ℂ)) | 𝒢] ω =
    ∫ u, Complex.exp (Complex.I * (u (T ω) : ℂ)) ∂(κ ω) from h2ω).trans ?_
  obtain ⟨F, hF, hTF, hFU⟩ := RandomTest.exists_basisUnion (T ω).hasCompactSupport.isCompact (hUo ω) hTU
  have hle : RandomTest.basisUnion F ≤ V := fun x hx => hUV ω (hFU hx)
  set TR : TestOn (RandomTest.basisUnion F) := ⟨T ω, (T ω).contDiff, (T ω).hasCompactSupport, hTF⟩ with hTR
  have hTe : GFF.testIncl (RandomTest.basisUnion F) V TR = T ω := by
    ext z
    rw [GFF.coe_testIncl hle]
    rfl
  rw [← hTe, ← hmap, hBω ⟨F, hF⟩ hFU]

end CondRandom

/-! ### Local Gaussian laws -/

/-- **Local Gaussian laws** for the conditional law "mean `m` plus the zero-boundary GFF on `U`": for open
`R ⊆ U ⊆ ℍ` and `m` locally integrable on `R`, there is a probability law on `𝒟'(R)` with characteristic functional
`ψ ↦ exp(i ∫ m ψ − ½ ‖ψ‖²_{H⁻¹(U)})` (the zero-boundary GFF on `U` extended by zero, restricted to `R`, shifted by the
distribution `m` on `R`). -/
theorem exists_gaussLocalLaw {U R : Opens ℂ} (hU : (U : Set ℂ) ⊆ H) (hRU : (R : Set ℂ) ⊆ U)
    {m : ℂ → ℝ} (hm : LocallyIntegrableOn m R) :
    ∃ μ : Measure (DistOn R), IsProbabilityMeasure μ ∧ ∀ ψ : TestOn R,
      ∫ v, Complex.exp (Complex.I * (v ψ : ℂ)) ∂μ =
        Complex.exp (Complex.I * ((∫ z, m z * ψ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov U ψ ψ : ℝ) : ℂ)) := by
  obtain ⟨μ₀, hμ₀P, hμ₀⟩ := RandomTest.exists_zbExtLaw hU
  set D : DistOn R := Distribution.ofFun R m volume ⊤ with hD
  have hDψ : ∀ ψ : TestOn R, D ψ = ∫ z, m z * ψ z := fun ψ => by
    rw [hD, Distribution.ofFun_apply hm]
    simp only [smul_eq_mul, mul_comm]
  set F : DistOn upperHalfPlaneOpens → DistOn R := fun u => GFF.restrictDist R u + D with hF
  have hFm : Measurable F :=
    LQGMetric.measurable_distOn_iff.2 fun ψ =>
      ((LQGMetric.measurable_distOn_apply ψ).comp (GFF.measurable_restrictDist R)).add_const _
  refine ⟨μ₀.map F, (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).2 hμ₀P, fun ψ => ?_⟩
  rw [integral_map hFm.aemeasurable
    (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply ψ)).aestronglyMeasurable]
  have e : ∀ u : DistOn upperHalfPlaneOpens, Complex.exp (Complex.I * (F u ψ : ℂ)) =
      Complex.exp (Complex.I * (u (GFF.testIncl R upperHalfPlaneOpens ψ) : ℂ)) *
        Complex.exp (Complex.I * (D ψ : ℂ)) := fun u => by
    rw [← Complex.exp_add]
    congr 1
    change Complex.I * ((GFF.restrictDist R u ψ + D ψ : ℝ) : ℂ) = _
    rw [GFF.restrictDist_apply]
    push_cast
    ring
  simp_rw [e]
  have hcoe : ((GFF.testIncl R upperHalfPlaneOpens ψ : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = ψ :=
    GFF.coe_testIncl (fun x hx => hU (hRU hx)) ψ
  rw [integral_mul_const, hμ₀ _, hcoe, Complex.ofReal_exp, ← Complex.exp_add, hDψ]
  congr 1
  push_cast
  ring

end MartMeans2

end Coupling

end InteractingSLE
