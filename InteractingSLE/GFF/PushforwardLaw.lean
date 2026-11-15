/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.PushforwardMeas
import InteractingSLE.Frozen.Spec.IsCondZeroBoundaryGFF
import InteractingSLE.Spec.Coupling.ProtectedKernel
import SupercriticalConformalCovariance.ZBConformal.GFFLaw
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Probability.Kernel.CondDistrib
import LQGMetric.Field.StandardBorelRange

/-!
# The law of the field transported by a conformal chart

Packet PROVE-PUSHFWD. A zero-boundary GFF on the chart domain `U = inv '' ℍ`, written in the chart coordinate,
is a zero-boundary GFF on `ℍ` (conformal invariance; SupercriticalConformalCovariance's
`isZeroBoundaryGFF_distPullback` and `zeroGFFTestCov_conformal`), and a coupling field "GFF on `U` plus a mean"
transports to "GFF on `ℍ` plus the transported mean".

* `Chart.zeroGFFTestCov_pushTest` : `‖pushTest φ‖²_{H⁻¹(U)} = ‖φ‖²_{H⁻¹(ℍ)}` (with the bilinear form);
* `Chart.isZeroBoundaryGFF_pullField` : `h|_U` a zero-boundary GFF on `U` ⇒ `h ∘ inv` one on `ℍ`;
* `Chart.isZBGFFProcess_chartTransport` : the same with a mean `m` on `U`: `chartTransport h − (m ∘ inv + k lift ∘ inv)`
  is a zero-boundary GFF on `ℍ` (the frozen `IsGFFWithBoundaryData` form);
* `Chart.isCondZeroBoundaryGFF_pullField` : conditionally on `𝒢`, for a fixed chart;
* `Chart.isCondZeroBoundaryGFF_pullField_random` : conditionally on `𝒢`, for a `𝒢`-measurable **random** chart
  (the transported test function is then a random test function), through the regular conditional law of the field
  (Mathlib `condDistrib`) and its identification with the law of the zero-boundary GFF on `U_ω` extended by zero
  (`zbExtLaw`), using the countable family of rational combinations of LQGMetric's generating test functions
  (`ext_of_integral_cexp_rat`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace
open QuantumZipper (H isOpen_H zeroGFFTestCov)
open LQGMetric (TestOn DistOn IsZeroBoundaryGFF IsZBGFFProcess)
open SupercriticalConformalCovariance (IsConformalBijection confPushTest)

namespace InteractingSLE

namespace Chart

variable {c : Chart}

/-- **Conformal invariance of the covariance** in the chart coordinate. -/
theorem zeroGFFTestCov_pushTest (hc : c.IsConformal) (φ ψ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov (c.dom : Set ℂ) (pushTest hc φ) (pushTest hc ψ) = zeroGFFTestCov H φ ψ := by
  have e : ∀ χ : TestOn upperHalfPlaneOpens,
      ⇑(pushTest hc χ) = ⇑(confPushTest hc.isConformalBijection χ) := fun χ => by
    change ⇑(GFF.testIncl c.dom upperHalfPlaneOpens (confPushTest hc.isConformalBijection χ)) = _
    exact GFF.coe_testIncl hc.dom_le _
  rw [e, e]
  exact SupercriticalConformalCovariance.ZBConformal.zeroGFFTestCov_conformal hc.isConformalBijection φ ψ

section Law

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Conformal invariance of the zero-boundary GFF**: if `h|_U` is a zero-boundary GFF on the chart domain, then
`h ∘ inv` is a zero-boundary GFF on `ℍ`. -/
theorem isZeroBoundaryGFF_pullField (hc : c.IsConformal) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : IsZeroBoundaryGFF c.dom (fun ω => GFF.restrictDist c.dom (X ω)) P) :
    IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => pullField hc (X ω)) P :=
  SupercriticalConformalCovariance.ZBConformal.isZeroBoundaryGFF_distPullback hc.isConformalBijection hX

/-- **The transported coupling field.** If on the chart domain `h = m + (zero-boundary GFF on U)`, then
`chartTransport h = (m ∘ inv + k · lift ∘ inv) + (zero-boundary GFF on ℍ)`. -/
theorem isZBGFFProcess_chartTransport (hc : c.IsConformal)
    (hℓ : LocallyIntegrableOn (fun w => c.2.2 (c.2.1 w)) H) {h : Ω → DistOn upperHalfPlaneOpens}
    {m : ℂ → ℝ} (k : ℝ)
    (hX : IsZBGFFProcess c.dom
      (fun ψ ω => h ω (GFF.testIncl c.dom upperHalfPlaneOpens ψ) - ∫ z, m z * ψ z) P) :
    IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => chartTransport hc 1 0 k (h ω) φ -
      ((∫ w, m (c.2.1 w) * φ w) + k * ∫ w, c.2.2 (c.2.1 w) * φ w)) P := by
  have h' := SupercriticalConformalCovariance.ZBConformal.isZBGFFProcess_pullProcess
    hc.isConformalBijection hX
  convert h' using 2 with φ
  funext ω
  change _ = h ω (pushTest hc φ) - ∫ z, m z * (confPushTest hc.isConformalBijection φ) z
  rw [SupercriticalConformalCovariance.ZBConformal.integral_mul_confPushTest, chartTransport_apply hc hℓ]
  ring

/-- **Conditional version, fixed chart**: conditionally on `𝒢`, a zero-boundary GFF on the chart domain (extended
by zero) written in the chart coordinate is a zero-boundary GFF on `ℍ`. -/
theorem isCondZeroBoundaryGFF_pullField (hc : c.IsConformal)
    {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : IsCondZeroBoundaryGFF P 𝒢 (fun _ => (c.dom : Set ℂ)) X) :
    IsCondZeroBoundaryGFF P 𝒢 (fun _ => H) (fun ω => pullField hc (X ω)) := by
  intro φ
  have h := hX (pushTest hc φ)
  simp only [pullField_apply]
  simp only [zeroGFFTestCov_pushTest hc φ φ] at h
  exact h

/-- The coupling-field form of `isCondZeroBoundaryGFF_pullField`: if `h − M` is conditionally a zero-boundary GFF
on the chart domain, the transports of `h` and of the mean `M` differ by a conditional zero-boundary GFF on `ℍ`. -/
theorem isCondZeroBoundaryGFF_chartTransport_sub (hc : c.IsConformal)
    {h M : Ω → DistOn upperHalfPlaneOpens} (a k : ℝ)
    (hX : IsCondZeroBoundaryGFF P 𝒢 (fun _ => (c.dom : Set ℂ)) fun ω => h ω - M ω) :
    IsCondZeroBoundaryGFF P 𝒢 (fun _ => H)
      fun ω => chartTransport hc 1 a k (h ω) - chartTransport hc 1 a k (M ω) := by
  have e : ∀ ω, chartTransport hc 1 a k (h ω) - chartTransport hc 1 a k (M ω) =
      pullField hc (h ω - M ω) := fun ω => by
    rw [chartTransport_sub, one_smul]
  simp_rw [e]
  exact isCondZeroBoundaryGFF_pullField hc hX

end Law

end Chart

/-! ### Identifying a law on `𝒟'(V)` from countably many characteristic values -/

namespace RandomTest

open LQGMetric (distGen)

/-- **Two finite measures on `𝒟'(V)` agree as soon as their characteristic functionals agree on the rational
combinations of the generating family** `φ_j = distGen V j` (countably many test functions). As
`Coupling.ext_of_integral_cexp`, with the characteristic functions of the finite-dimensional marginals extended
from rational to real arguments by continuity. -/
theorem ext_of_integral_cexp_rat {V : Opens ℂ} {μ ν : Measure (DistOn V)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ (s : Finset (ℕ × ℕ)) (q : s → ℚ),
      ∫ g, Complex.exp (Complex.I * (g (∑ i : s, (q i : ℝ) • distGen V i) : ℂ)) ∂μ =
        ∫ g, Complex.exp (Complex.I * (g (∑ i : s, (q i : ℝ) • distGen V i) : ℂ)) ∂ν) : μ = ν := by
  classical
  have huniv : μ univ = ν univ := by
    have h0 := h ∅ (fun _ => 0)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, map_zero, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, integral_const, Complex.real_smul, mul_one] at h0
    have h0' : μ.real univ = ν.real univ := by exact_mod_cast h0
    rw [Measure.real, Measure.real] at h0'
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h0'
  refine ext_of_generate_finite (Coupling.genCylinders V) (Coupling.distOn_eq_generateFrom_genCylinders V)
    (Coupling.isPiSystem_genCylinders V) ?_ huniv
  rintro _ ⟨C, hC, rfl⟩
  rw [mem_measurableCylinders] at hC
  obtain ⟨s, Sx, hSx, rfl⟩ := hC
  set pr : DistOn V → EuclideanSpace ℝ s := fun T => WithLp.toLp 2 (fun i : s => T (distGen V i))
    with hprdef
  have hpr : Measurable pr := (WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.2 fun i => LQGMetric.measurable_distOn_apply _)
  have hmS : MeasurableSet {y : EuclideanSpace ℝ s | y.ofLp ∈ Sx} :=
    (WithLp.measurable_ofLp 2 _) hSx
  have hset : Coupling.genPairs V ⁻¹' cylinder s Sx = pr ⁻¹' {y | y.ofLp ∈ Sx} := by
    ext T
    simp only [pr, cylinder, mem_preimage, mem_ofPred_eq]
    rfl
  have hrat : ∀ q : s → ℚ, charFun (μ.map pr) (WithLp.toLp 2 fun i => (q i : ℝ)) =
      charFun (ν.map pr) (WithLp.toLp 2 fun i => (q i : ℝ)) := by
    intro q
    rw [charFun_apply, charFun_apply, integral_map hpr.aemeasurable (by fun_prop),
      integral_map hpr.aemeasurable (by fun_prop)]
    simp_rw [hprdef, Coupling.inner_toLp_pairings, mul_comm _ Complex.I]
    exact h s q
  have hdense : DenseRange fun q : s → ℚ => (WithLp.toLp 2 fun i => (q i : ℝ) : EuclideanSpace ℝ s) := by
    have h1 : DenseRange (Pi.map fun (_ : s) (r : ℚ) => (r : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    exact (WithLp.toLp_surjective 2).denseRange.comp h1 (PiLp.continuous_toLp 2 _)
  have hchar : charFun (μ.map pr) = charFun (ν.map pr) :=
    continuous_charFun.ext_on hdense continuous_charFun (by rintro _ ⟨q, rfl⟩; exact hrat q)
  rw [hset, ← Measure.map_apply hpr hmS, ← Measure.map_apply hpr hmS, Measure.ext_of_charFun hchar]

/-- **The law of the zero-boundary GFF on `U ⊆ ℍ` extended by zero to `ℍ`**: a probability measure on `𝒟'(ℍ)` with
characteristic functional `φ ↦ exp(−½ ‖φ‖²_{H⁻¹(U)})` (the zero-boundary part of the Markov decomposition of a
zero-boundary GFF on `ℍ` along `U`, `GFF.exists_markovMap_upperHalfPlane`). -/
theorem exists_zbExtLaw {U : Opens ℂ} (hU : (U : Set ℂ) ⊆ H) :
    ∃ μ : Measure (DistOn upperHalfPlaneOpens), IsProbabilityMeasure μ ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∫ u, Complex.exp (Complex.I * (u φ : ℂ)) ∂μ =
        ((Real.exp (-(1 / 2) * zeroGFFTestCov U φ φ) : ℝ) : ℂ) := by
  obtain ⟨G, hGm, hG⟩ := GFF.exists_markovMap_of_subset_H (D := upperHalfPlaneOpens) hU subset_rfl
  have hZ := Coupling.isZeroBoundaryGFF_zbLaw (D := upperHalfPlaneOpens) subset_rfl
  have hd := hG (P := Coupling.zbLaw upperHalfPlaneOpens) (h := id) hZ
  refine ⟨(Coupling.zbLaw upperHalfPlaneOpens).map G, inferInstance,
    fun φ => ?_⟩
  rw [integral_map hGm.aemeasurable
    (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply φ)).aestronglyMeasurable]
  have hGa : HasGaussianLaw (fun u => G u φ) (Coupling.zbLaw upperHalfPlaneOpens) :=
    hd.isZBGFFExtOn.gaussian.hasGaussianLaw_eval φ
  have hcov : cov[fun u => G u φ, fun u => G u φ; Coupling.zbLaw upperHalfPlaneOpens] =
      zeroGFFTestCov U φ φ := hd.isZBGFFExtOn.covariance_eq' φ φ
  rw [GFF.integral_exp_I_mul_of_hasGaussianLaw hGa (hd.isZBGFFExtOn.centered φ),
    ← covariance_self hGa.aemeasurable, hcov]

/-- The Gaussian law on `𝒟'(ℍ)` with mean `m` and the covariance of the zero-boundary GFF on `U` (extended by
zero): characteristic functional `φ ↦ exp(i m(φ) − ½ ‖φ‖²_{H⁻¹(U)})`. -/
theorem exists_gaussExtLaw {U : Opens ℂ} (hU : (U : Set ℂ) ⊆ H) (m : DistOn upperHalfPlaneOpens) :
    ∃ μ : Measure (DistOn upperHalfPlaneOpens), IsProbabilityMeasure μ ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∫ u, Complex.exp (Complex.I * (u φ : ℂ)) ∂μ =
        Complex.exp (Complex.I * (m φ : ℂ) - (((1 / 2 : ℝ) * zeroGFFTestCov U φ φ : ℝ) : ℂ)) := by
  obtain ⟨μ₀, hμ₀P, hμ₀⟩ := exists_zbExtLaw hU
  have hadd : Measurable fun u : DistOn upperHalfPlaneOpens => u + m :=
    LQGMetric.measurable_distOn_iff.2 fun φ => (LQGMetric.measurable_distOn_apply φ).add_const _
  refine ⟨μ₀.map fun u => u + m, inferInstance, fun φ => ?_⟩
  rw [integral_map hadd.aemeasurable
    (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply φ)).aestronglyMeasurable]
  have e : ∀ u : DistOn upperHalfPlaneOpens, Complex.exp (Complex.I * ((u + m) φ : ℂ)) =
      Complex.exp (Complex.I * (u φ : ℂ)) * Complex.exp (Complex.I * (m φ : ℂ)) := fun u => by
    rw [← Complex.exp_add]
    congr 1
    change Complex.I * ((u φ + m φ : ℝ) : ℂ) = _
    push_cast
    ring
  simp_rw [e]
  rw [integral_mul_const, hμ₀ φ, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

section CondRandom

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Conditional characteristic functional at a random test function.** Suppose that, conditionally on `𝒢 ≤ 𝓕`,
the characteristic functional of the random distribution `X` is `Ψ ω` for every fixed test function, and that each
`Ψ ω` is the characteristic functional of some probability law. Then the same holds at every `𝒢`-measurable random
test function `T`: `E[exp(i X(T)) | 𝒢] = Ψ(ω, T ω)`.

Proof: the regular conditional law `κ` of `X` given `𝒢` (Mathlib `condDistrib`, `𝒟'(V)` being standard Borel) has
characteristic functional `Ψ ω` at the countably many rational combinations of the generating test functions for
almost every `ω`, hence is the law with characteristic functional `Ψ ω` (`ext_of_integral_cexp_rat`); and
`E[exp(i X(T)) | 𝒢] = ∫ exp(i u(T ω)) κ(ω, du)` since `(ω, u) ↦ u(T ω)` is jointly measurable
(`measurable_apply_of_forall_measurable` on `Ω × 𝒟'(V)`). -/
theorem condExp_cexp_apply_ae_eq (h𝒢 : 𝒢 ≤ mΩ) {V : Opens ℂ} {X : Ω → DistOn V} (hX : Measurable X)
    {Ψ : Ω → TestOn V → ℂ}
    (hΨ : ∀ ω, ∃ μ : Measure (DistOn V), IsProbabilityMeasure μ ∧
      ∀ φ, ∫ u, Complex.exp (Complex.I * (u φ : ℂ)) ∂μ = Ψ ω φ)
    (hcond : ∀ φ : TestOn V,
      P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | 𝒢] =ᵐ[P] fun ω => Ψ ω φ)
    {T : Ω → TestOn V} (hT : ∀ z, Measurable[𝒢] fun ω => T ω z) :
    P[fun ω => Complex.exp (Complex.I * (X ω (T ω) : ℂ)) | 𝒢] =ᵐ[P] fun ω => Ψ ω (T ω) := by
  classical
  choose μ hμP hμ using hΨ
  have hid : Measurable[mΩ, 𝒢] (id : Ω → Ω) := measurable_id'' h𝒢
  set κ := @condDistrib Ω Ω (DistOn V) _ _ _ mΩ 𝒢 X id P _ with hκ
  have hcomap : MeasurableSpace.comap (id : Ω → Ω) 𝒢 = 𝒢 := MeasurableSpace.comap_id
  -- Step A: the kernel has the right characteristic values at each fixed test function
  have hA : ∀ φ : TestOn V, ∀ᵐ ω ∂P, ∫ u, Complex.exp (Complex.I * (u φ : ℂ)) ∂(κ ω) = Ψ ω φ := by
    intro φ
    have hf : StronglyMeasurable fun u : DistOn V => Complex.exp (Complex.I * (u φ : ℂ)) :=
      (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply φ)).stronglyMeasurable
    have h1 := @condExp_ae_eq_integral_condDistrib Ω Ω (DistOn V) ℂ _ _ _ _ mΩ P _ id X 𝒢 _ _ hid
      hX.aemeasurable _ hf (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hX))
    rw [hcomap] at h1
    filter_upwards [h1, hcond φ] with ω h1ω h2ω
    rw [← h2ω, h1ω]
    rfl
  -- Step B: countably many test functions identify the kernel
  have hB : ∀ᵐ ω ∂P, κ ω = μ ω := by
    have hall : ∀ᵐ ω ∂P, ∀ p : Σ s : Finset (ℕ × ℕ), (s → ℚ),
        ∫ u, Complex.exp (Complex.I * (u (∑ i : p.1, (p.2 i : ℝ) • LQGMetric.distGen V i) : ℂ)) ∂(κ ω) =
          Ψ ω (∑ i : p.1, (p.2 i : ℝ) • LQGMetric.distGen V i) :=
      ae_all_iff.2 fun p => hA _
    filter_upwards [hall] with ω hω
    exact ext_of_integral_cexp_rat fun s q => (hω ⟨s, q⟩).trans (hμ ω _).symm
  -- Step C: disintegration at the random test function
  have hjoint : Measurable[(𝒢.prod inferInstance), _] fun p : Ω × DistOn V => p.2 (T p.1) :=
    @measurable_apply_of_forall_measurable (Ω × DistOn V) (𝒢.prod inferInstance) V (fun p => p.2)
      (@measurable_snd Ω (DistOn V) 𝒢 _) (fun p => T p.1)
      (fun z => (hT z).comp (@measurable_fst Ω (DistOn V) 𝒢 _))
  have hf : StronglyMeasurable[(𝒢.prod inferInstance)]
      fun p : Ω × DistOn V => Complex.exp (Complex.I * (p.2 (T p.1) : ℂ)) :=
    (@GFF.measurable_exp_I_mul (Ω × DistOn V) (𝒢.prod inferInstance) _ hjoint).stronglyMeasurable
  have hTm : Measurable fun ω => X ω (T ω) :=
    measurable_apply_of_forall_measurable hX fun z => (hT z).mono h𝒢 le_rfl
  have h2 := @condExp_prod_ae_eq_integral_condDistrib Ω Ω (DistOn V) ℂ _ _ _ _ mΩ P _ id X 𝒢
    (fun p => Complex.exp (Complex.I * (p.2 (T p.1) : ℂ))) _ _ hid hX.aemeasurable hf
    (GFF.integrable_exp_I_mul hTm)
  rw [hcomap] at h2
  filter_upwards [h2, hB] with ω h2ω hBω
  refine (show P[fun ω => Complex.exp (Complex.I * (X ω (T ω) : ℂ)) | 𝒢] ω =
    ∫ u, Complex.exp (Complex.I * (u (T ω) : ℂ)) ∂(κ ω) from h2ω).trans ?_
  rw [hBω, hμ ω]

/-! #### The support-restricted version -/

/-- Finite unions of members of the countable basis of `ℂ`, as open sets. -/
def basisUnion (F : Set (Set ℂ)) : Opens ℂ :=
  ⟨⋃ b ∈ F ∩ TopologicalSpace.countableBasis ℂ, b,
    isOpen_biUnion fun _ hb => TopologicalSpace.isOpen_of_mem_countableBasis hb.2⟩

/-- The countable index set: finite families of basis sets. -/
def basisFamilies : Set (Set (Set ℂ)) :=
  {F | F.Finite ∧ F ⊆ TopologicalSpace.countableBasis ℂ}

theorem countable_basisFamilies : basisFamilies.Countable :=
  Set.countable_ofPred_finite_subset (TopologicalSpace.countable_countableBasis ℂ)

/-- Every compact subset of an open set lies in a finite union of basis sets inside the open set. -/
theorem exists_basisUnion {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ F ∈ basisFamilies, K ⊆ basisUnion F ∧ (basisUnion F : Set ℂ) ⊆ U := by
  set b := {s ∈ TopologicalSpace.countableBasis ℂ | s ⊆ U} with hb
  have hcov : K ⊆ ⋃ s ∈ b, id s := by
    intro x hx
    obtain ⟨s, hs, hxs, hsU⟩ := (TopologicalSpace.isBasis_countableBasis ℂ).exists_subset_of_mem_open
      (hKU hx) hU
    exact mem_biUnion (show s ∈ b from ⟨hs, hsU⟩) hxs
  obtain ⟨b', hb'b, hfin, hKb'⟩ := hK.elim_finite_subcover_image
    (fun s hs => TopologicalSpace.isOpen_of_mem_countableBasis hs.1) hcov
  have he : (basisUnion b' : Set ℂ) = ⋃ s ∈ b', s := by
    change (⋃ s ∈ b' ∩ TopologicalSpace.countableBasis ℂ, s) = _
    rw [inter_eq_left.2 fun s hs => (hb'b hs).1]
  refine ⟨b', ⟨hfin, fun s hs => (hb'b hs).1⟩, ?_, ?_⟩
  · rw [he]; exact hKb'
  · rw [he]; exact iUnion₂_subset fun s hs => (hb'b hs).2

/-- **Conditional characteristic functional at a random test function, support-restricted form.** As
`condExp_cexp_apply_ae_eq`, when the conditional characteristic functional is known only for the test functions
supported in a random open set `U ω` (the form of the frozen coupling off the hull), and the random test function
is supported in `U ω`. The kernel is identified on each of the countably many open sets `basisUnion F ⊆ U ω`. -/
theorem condExp_cexp_apply_ae_eq_of_subset (h𝒢 : 𝒢 ≤ mΩ) {V : Opens ℂ} {X : Ω → DistOn V}
    (hX : Measurable X) {U : Ω → Set ℂ} (hUo : ∀ ω, IsOpen (U ω)) (hUV : ∀ ω, U ω ⊆ V)
    {Ψ : Ω → TestOn V → ℂ}
    (hΨ : ∀ ω, ∃ μ : Measure (DistOn V), IsProbabilityMeasure μ ∧
      ∀ φ : TestOn V, tsupport φ ⊆ U ω → ∫ u, Complex.exp (Complex.I * (u φ : ℂ)) ∂μ = Ψ ω φ)
    (hcond : ∀ φ : TestOn V, ∀ᵐ ω ∂P, tsupport φ ⊆ U ω →
      P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | 𝒢] ω = Ψ ω φ)
    {T : Ω → TestOn V} (hT : ∀ z, Measurable[𝒢] fun ω => T ω z) (hTU : ∀ ω, tsupport (T ω) ⊆ U ω) :
    P[fun ω => Complex.exp (Complex.I * (X ω (T ω) : ℂ)) | 𝒢] =ᵐ[P] fun ω => Ψ ω (T ω) := by
  classical
  choose μ hμP hμ using hΨ
  have hid : Measurable[mΩ, 𝒢] (id : Ω → Ω) := measurable_id'' h𝒢
  set κ := @condDistrib Ω Ω (DistOn V) _ _ _ mΩ 𝒢 X id P _ with hκ
  have hcomap : MeasurableSpace.comap (id : Ω → Ω) 𝒢 = 𝒢 := MeasurableSpace.comap_id
  -- Step A
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
  -- Step B: the restrictions to the sets `basisUnion F ⊆ U ω` are identified
  have hmap : ∀ (R : Opens ℂ) (ν : Measure (DistOn V)) (ψ : TestOn R),
      ∫ v, Complex.exp (Complex.I * (v ψ : ℂ)) ∂(ν.map (GFF.restrictDist R)) =
        ∫ u, Complex.exp (Complex.I * (u (GFF.testIncl R V ψ) : ℂ)) ∂ν := fun R ν ψ => by
    rw [integral_map (GFF.measurable_restrictDist R).aemeasurable
      (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply ψ)).aestronglyMeasurable]
    rfl
  have : Countable basisFamilies := countable_basisFamilies.to_subtype
  have hB : ∀ᵐ ω ∂P, ∀ F : basisFamilies, (basisUnion F.1 : Set ℂ) ⊆ U ω →
      (κ ω).map (GFF.restrictDist (basisUnion F.1)) = (μ ω).map (GFF.restrictDist (basisUnion F.1)) := by
    have hall : ∀ᵐ ω ∂P, ∀ p : basisFamilies × (Σ s : Finset (ℕ × ℕ), (s → ℚ)),
        tsupport (GFF.testIncl (basisUnion p.1.1) V
          (∑ i : p.2.1, (p.2.2 i : ℝ) • LQGMetric.distGen (basisUnion p.1.1) i)) ⊆ U ω →
        ∫ u, Complex.exp (Complex.I * (u (GFF.testIncl (basisUnion p.1.1) V
          (∑ i : p.2.1, (p.2.2 i : ℝ) • LQGMetric.distGen (basisUnion p.1.1) i)) : ℂ)) ∂(κ ω) =
          Ψ ω (GFF.testIncl (basisUnion p.1.1) V
            (∑ i : p.2.1, (p.2.2 i : ℝ) • LQGMetric.distGen (basisUnion p.1.1) i)) :=
      ae_all_iff.2 fun p => hA _
    filter_upwards [hall] with ω hω F hFU
    have hle : basisUnion F.1 ≤ V := fun x hx => hUV ω (hFU hx)
    refine ext_of_integral_cexp_rat fun s q => ?_
    have hts : tsupport (GFF.testIncl (basisUnion F.1) V
        (∑ i : s, (q i : ℝ) • LQGMetric.distGen (basisUnion F.1) i)) ⊆ U ω := by
      rw [GFF.coe_testIncl hle]
      exact (TestFunction.tsupport_subset _).trans hFU
    rw [hmap, hmap, hω ⟨F, ⟨s, q⟩⟩ hts, hμ ω _ hts]
  -- Step C
  have hjoint : Measurable[(𝒢.prod inferInstance), _] fun p : Ω × DistOn V => p.2 (T p.1) :=
    @measurable_apply_of_forall_measurable (Ω × DistOn V) (𝒢.prod inferInstance) V (fun p => p.2)
      (@measurable_snd Ω (DistOn V) 𝒢 _) (fun p => T p.1)
      (fun z => (hT z).comp (@measurable_fst Ω (DistOn V) 𝒢 _))
  have hf : StronglyMeasurable[(𝒢.prod inferInstance)]
      fun p : Ω × DistOn V => Complex.exp (Complex.I * (p.2 (T p.1) : ℂ)) :=
    (@GFF.measurable_exp_I_mul (Ω × DistOn V) (𝒢.prod inferInstance) _ hjoint).stronglyMeasurable
  have hTm : Measurable fun ω => X ω (T ω) :=
    measurable_apply_of_forall_measurable hX fun z => (hT z).mono h𝒢 le_rfl
  have h2 := @condExp_prod_ae_eq_integral_condDistrib Ω Ω (DistOn V) ℂ _ _ _ _ mΩ P _ id X 𝒢
    (fun p => Complex.exp (Complex.I * (p.2 (T p.1) : ℂ))) _ _ hid hX.aemeasurable hf
    (GFF.integrable_exp_I_mul hTm)
  rw [hcomap] at h2
  filter_upwards [h2, hB] with ω h2ω hBω
  refine (show P[fun ω => Complex.exp (Complex.I * (X ω (T ω) : ℂ)) | 𝒢] ω =
    ∫ u, Complex.exp (Complex.I * (u (T ω) : ℂ)) ∂(κ ω) from h2ω).trans ?_
  obtain ⟨F, hF, hTF, hFU⟩ := exists_basisUnion (T ω).hasCompactSupport.isCompact (hUo ω) (hTU ω)
  have hle : basisUnion F ≤ V := fun x hx => hUV ω (hFU hx)
  set TR : TestOn (basisUnion F) := ⟨T ω, (T ω).contDiff, (T ω).hasCompactSupport, hTF⟩ with hTR
  have hTe : GFF.testIncl (basisUnion F) V TR = T ω := by
    ext z
    rw [GFF.coe_testIncl hle]
    rfl
  rw [← hTe, ← hmap, hBω ⟨F, hF⟩ hFU, hmap, hTe, hμ ω _ (hTU ω)]

end CondRandom

end RandomTest

namespace Chart

section CondRandomChart

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Conditional law of the field transported by a `𝒢`-measurable random chart.** If, conditionally on `𝒢`, `X` is
a zero-boundary GFF on the random chart domain `U_ω` (extended by zero), and the chart is `𝒢`-measurable (domain
events and forward maps on them), then `ω ↦ X ω ∘ inv_ω` is, conditionally on `𝒢`, a zero-boundary GFF on `ℍ`. -/
theorem isCondZeroBoundaryGFF_pullField_random (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X)
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => ((c ω).dom : Set ℂ)) X) :
    IsCondZeroBoundaryGFF P 𝒢 (fun _ => H) (fun ω => pullField (hc ω) (X ω)) := by
  intro φ
  have hT : ∀ z, Measurable[𝒢] fun ω => pushTest (hc ω) φ z := fun z =>
    @measurable_pushTest_apply Ω 𝒢 c hc hdom hfwd φ z
  have h := RandomTest.condExp_cexp_apply_ae_eq h𝒢 hX
    (Ψ := fun ω φ => ((Real.exp (-(1 / 2) * zeroGFFTestCov ((c ω).dom : Set ℂ) φ φ) : ℝ) : ℂ))
    (fun ω => RandomTest.exists_zbExtLaw (hc ω).dom_subset) hcond hT
  simp only [pullField_apply]
  refine h.trans (Eventually.of_forall fun ω => ?_)
  simp only [zeroGFFTestCov_pushTest (hc ω) φ φ]

/-- The coupling-field form: if `h − M` is conditionally a zero-boundary GFF on the random chart domain, then the
transports of `h` and of the mean `M` by the random chart differ by a conditional zero-boundary GFF on `ℍ`. -/
theorem isCondZeroBoundaryGFF_chartTransport_sub_random (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hM : Measurable M) (a k : ℝ)
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => ((c ω).dom : Set ℂ)) fun ω => h ω - M ω) :
    IsCondZeroBoundaryGFF P 𝒢 (fun _ => H)
      fun ω => chartTransport (hc ω) 1 a k (h ω) - chartTransport (hc ω) 1 a k (M ω) := by
  have e : ∀ ω, chartTransport (hc ω) 1 a k (h ω) - chartTransport (hc ω) 1 a k (M ω) =
      pullField (hc ω) (h ω - M ω) := fun ω => by
    rw [chartTransport_sub, one_smul]
  simp_rw [e]
  have hsub : Measurable fun ω => h ω - M ω :=
    LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).comp hh).sub ((LQGMetric.measurable_distOn_apply φ).comp hM)
  exact isCondZeroBoundaryGFF_pullField_random h𝒢 hc hdom hfwd hsub hcond

/-- **Conditional law of the transported coupling field, support-restricted form.** If, conditionally on `𝒢`,
`h` has the characteristic functional `exp(i M(φ) − ½ ‖φ‖²_{H⁻¹(U_ω)})` for the test functions supported in the
random chart domain `U_ω` (the form of the frozen optional hull coupling off the hull, with `U_ω = ℍ \ K_τ`), and
the chart is `𝒢`-measurable, then `h ∘ inv_ω` has, conditionally on `𝒢`, the characteristic functional
`exp(i (M ∘ inv_ω)(φ') − ½ ‖φ'‖²_{H⁻¹(ℍ)})` for **every** test function `φ'` on `ℍ`. -/
theorem condExp_cexp_pullField_random_of_subset (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ (c ω).dom →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).dom : Set ℂ) φ φ : ℝ) : ℂ)))
    (φ : TestOn upperHalfPlaneOpens) :
    P[fun ω => Complex.exp (Complex.I * (pullField (hc ω) (h ω) φ : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * (pullField (hc ω) (M ω) φ : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov H φ φ : ℝ) : ℂ)) := by
  have hT : ∀ z, Measurable[𝒢] fun ω => pushTest (hc ω) φ z := fun z =>
    @measurable_pushTest_apply Ω 𝒢 c hc hdom hfwd φ z
  have key := RandomTest.condExp_cexp_apply_ae_eq_of_subset h𝒢 hh (U := fun ω => ((c ω).dom : Set ℂ))
    (fun ω => (c ω).dom.isOpen) (fun ω => (hc ω).dom_subset)
    (Ψ := fun ω φ => Complex.exp (Complex.I * (M ω φ : ℂ) -
      (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).dom : Set ℂ) φ φ : ℝ) : ℂ)))
    (fun ω => by
      obtain ⟨μ, hμP, hμ⟩ := RandomTest.exists_gaussExtLaw (hc ω).dom_subset (M ω)
      exact ⟨μ, hμP, fun φ _ => hμ φ⟩) hcond hT (fun ω => tsupport_pushTest_subset (hc ω) φ)
  simp only [pullField_apply]
  refine key.trans (Eventually.of_forall fun ω => ?_)
  simp only [zeroGFFTestCov_pushTest (hc ω) φ φ]

end CondRandomChart

end Chart

end InteractingSLE
