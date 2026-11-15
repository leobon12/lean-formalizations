/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4CLocFac
import InteractingSLE.Spec.Restart.ChartGauss
import InteractingSLE.Spec.Coupling.WholeField8Local
import InteractingSLE.GFF.PushforwardLaw

/-!
# Gaussian kernels under a regular conditional law

Packet PROVE-GW4-CLOC (generic measure-theoretic tools for the conditional component transfer).

* `countablyGenerated_hittingSigma`: the hitting σ-algebra on `Set ℂ` is countably generated (avoidance of an open
  `U ⊆ ℍ` is avoidance of the countably many basic open sets inside `U`);
* **`ae_ae_condExp_eq_of_le`** (the tower step): if `m ≤ m' ≤ mΩ` with `m'` countably generated and
  `P[f | m'] = Y` with `Y` `m'`-measurable, then for `P`-almost every `ω₀` the same identity holds under the regular
  conditional law `condExpKernel P m ω₀`;
* **`ae_condExp_cexp_eq_rangeKerCF_of_ratComb`** (the law step): if, under a probability measure on a standard Borel
  space, the conditional characteristic functional of a random distribution given `m'` is the Gaussian functional
  `rangeKerCF (M ω) (D ω)` at the countably many rational combinations of the generating tests, it is that functional
  at every test (the conditional law is the law of `M ω` plus the zero-boundary GFF of `D ω`, by
  `Restart.ext_of_integral_cexp_ratComb`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW4Fix.CLoc

open LocalSets WholeField

/-! ### The hitting σ-algebra is countably generated -/

theorem countablyGenerated_hittingSigma : @MeasurableSpace.CountablyGenerated (Set ℂ) hittingSigma := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis ℂ
  refine @MeasurableSpace.CountablyGenerated.mk (Set ℂ) hittingSigma
    ⟨(fun b : Set ℂ => {A : Set ℂ | (A ∩ b).Nonempty}) '' {b ∈ B | b ⊆ H},
    (hBc.mono fun _ hb => hb.1).image _, ?_⟩
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (MeasurableSpace.generateFrom_le ?_)
  · rintro _ ⟨U, hU, hUH, rfl⟩
    have he : {A : Set ℂ | (A ∩ U).Nonempty} =
        ⋃ b ∈ {b ∈ B | b ⊆ U}, {A : Set ℂ | (A ∩ b).Nonempty} := by
      ext A
      simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
      constructor
      · rintro ⟨z, hzA, hzU⟩
        obtain ⟨b, hb, hzb, hbU⟩ := hB.exists_subset_of_mem_open hzU hU
        exact ⟨b, ⟨hb, hbU⟩, z, hzA, hzb⟩
      · rintro ⟨b, ⟨-, hbU⟩, z, hzA, hzb⟩
        exact ⟨z, hzA, hbU hzb⟩
    rw [he]
    refine MeasurableSet.biUnion (hBc.mono fun _ hb => hb.1) fun b hb => ?_
    exact MeasurableSpace.measurableSet_generateFrom ⟨b, ⟨hb.1, hb.2.trans hUH⟩, rfl⟩
  · rintro _ ⟨b, ⟨hb, hbH⟩, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨b, hB.isOpen hb, hbH, rfl⟩

/-! ### The tower step -/

section Tower

variable {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The tower step.** For `m ≤ m' ≤ mΩ` with `m'` countably generated, a conditional expectation identity given
`m'` under `P` holds, for `P`-almost every `ω₀`, under the regular conditional law `condExpKernel P m ω₀`. -/
theorem ae_ae_condExp_eq_of_le (hm : m ≤ m') (hm' : m' ≤ mΩ)
    (hcg : @MeasurableSpace.CountablyGenerated Ω m') {f : Ω → ℂ} (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ ω, ‖f ω‖ ≤ C) {Y : Ω → ℂ} (hY : P[f | m'] =ᵐ[P] Y) :
    ∀ᵐ ω₀ ∂P, (condExpKernel P m ω₀)[f | m'] =ᵐ[condExpKernel P m ω₀] Y := by
  have hint : ∀ (μ : Measure Ω) [IsFiniteMeasure μ], Integrable f μ := fun μ _ =>
    Integrable.of_bound hfm.aestronglyMeasurable C (Eventually.of_forall hfb)
  have hPk : ∀ᵐ x ∂P, P[f | m'] x = ∫ y, f y ∂(condExpKernel P m' x) :=
    condExp_ae_eq_integral_condExpKernel hm' (hint P)
  have hPY : ∀ᵐ x ∂P, Y x = ∫ y, f y ∂(condExpKernel P m' x) := by
    filter_upwards [hPk, hY] with x h1 h2
    rw [← h2, h1]
  filter_upwards [KernelTower.ae_ae_condExpKernel_condExpKernel_eq hm hm' hcg,
    KernelTower.ae_ae_condExpKernel_of_ae (hm.trans hm') hPY] with ω₀ hk hY'
  filter_upwards [condExp_ae_eq_integral_condExpKernel hm' (hint (condExpKernel P m ω₀)), hk, hY']
    with x h1 h2 h3
  rw [h1, h2, h3]

end Tower

/-! ### The law step -/

section Law

variable {Ω : Type*} {m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {Q : Measure Ω} [IsProbabilityMeasure Q]

/-- The Gaussian functional `rangeKerCF M D` is the characteristic functional of a probability law on `𝒟'(ℍ)`: the
law of `M` plus the zero-boundary GFF on `D` extended by zero. -/
theorem exists_law_rangeKerCF (M : DistOn upperHalfPlaneOpens) {D : Set ℂ} (hDo : IsOpen D) (hDH : D ⊆ H) :
    ∃ μ : Measure (DistOn upperHalfPlaneOpens), IsProbabilityMeasure μ ∧
      ∀ φ : TestOn upperHalfPlaneOpens,
        ∫ T, Complex.exp (Complex.I * (T φ : ℂ)) ∂μ = rangeKerCF M D φ := by
  obtain ⟨μ₀, hμ₀, hchar⟩ := RandomTest.exists_zbExtLaw (U := ⟨D, hDo⟩) hDH
  have hmeas : Measurable fun T : DistOn upperHalfPlaneOpens => T + M :=
    LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).add measurable_const)
  have := hμ₀
  simp only [Opens.coe_mk] at hchar
  refine ⟨μ₀.map fun T => T + M, inferInstance, fun φ => ?_⟩
  rw [integral_map hmeas.aemeasurable
    (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply φ)).aestronglyMeasurable]
  have he : ∀ T : DistOn upperHalfPlaneOpens, Complex.exp (Complex.I * ((T + M) φ : ℂ)) =
      Complex.exp (Complex.I * (M φ : ℂ)) * Complex.exp (Complex.I * (T φ : ℂ)) := fun T => by
    rw [← Complex.exp_add, add_apply]
    push_cast
    ring_nf
  simp_rw [he]
  rw [integral_const_mul, hchar φ, rangeKerCF, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The law step.** If the conditional characteristic functional of `Xf` given `m'` is the Gaussian functional
`rangeKerCF (M ω) (D ω)` at the rational combinations of the generating tests, it is that functional at every
test. -/
theorem ae_condExp_cexp_eq_rangeKerCF_of_ratComb (hm' : m' ≤ mΩ) {Xf : Ω → DistOn upperHalfPlaneOpens}
    (hXf : Measurable Xf) {M : Ω → DistOn upperHalfPlaneOpens} {D : Ω → Set ℂ}
    (hD : ∀ᵐ ω ∂Q, IsOpen (D ω) ∧ D ω ⊆ H)
    (hk : ∀ k : Restart.RatComb,
      Q[fun ω => Complex.exp (Complex.I * (Xf ω (Restart.ratComb upperHalfPlaneOpens k) : ℂ)) | m'] =ᵐ[Q]
        fun ω => rangeKerCF (M ω) (D ω) (Restart.ratComb upperHalfPlaneOpens k))
    (φ : TestOn upperHalfPlaneOpens) :
    Q[fun ω => Complex.exp (Complex.I * (Xf ω φ : ℂ)) | m'] =ᵐ[Q]
      fun ω => rangeKerCF (M ω) (D ω) φ := by
  have hfm : ∀ ψ : TestOn upperHalfPlaneOpens,
      Measurable fun ω => Complex.exp (Complex.I * (Xf ω ψ : ℂ)) := fun ψ =>
    GFF.measurable_exp_I_mul ((LQGMetric.measurable_distOn_apply ψ).comp hXf)
  have hint : ∀ ψ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Complex.exp (Complex.I * (Xf ω ψ : ℂ))) Q := fun ψ =>
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply ψ).comp hXf)
  have hker : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ x ∂Q,
      Q[fun ω => Complex.exp (Complex.I * (Xf ω ψ : ℂ)) | m'] x =
        ∫ y, Complex.exp (Complex.I * (Xf y ψ : ℂ)) ∂(condExpKernel Q m' x) := fun ψ =>
    condExp_ae_eq_integral_condExpKernel hm' (hint ψ)
  have hall : ∀ᵐ x ∂Q, ∀ k : Restart.RatComb,
      ∫ y, Complex.exp (Complex.I * (Xf y (Restart.ratComb upperHalfPlaneOpens k) : ℂ))
        ∂(condExpKernel Q m' x) = rangeKerCF (M x) (D x) (Restart.ratComb upperHalfPlaneOpens k) := by
    refine ae_all_iff.2 fun k => ?_
    filter_upwards [hker (Restart.ratComb upperHalfPlaneOpens k), hk k] with x h1 h2
    rw [← h1, h2]
  filter_upwards [hall, hker φ, hD] with x hx h1 ⟨hDo, hDH⟩
  rw [h1]
  obtain ⟨μ, hμ, hμc⟩ := exists_law_rangeKerCF (M x) hDo hDH
  have hmap : (condExpKernel Q m' x).map Xf = μ := by
    refine Restart.ext_of_integral_cexp_ratComb fun k => ?_
    rw [integral_map hXf.aemeasurable
      (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply _)).aestronglyMeasurable,
      hx k, hμc]
  have := congrArg (fun ν : Measure (DistOn upperHalfPlaneOpens) =>
    ∫ T, Complex.exp (Complex.I * (T φ : ℂ)) ∂ν) hmap
  rw [integral_map hXf.aemeasurable
    (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply _)).aestronglyMeasurable,
    hμc] at this
  exact this

end Law

end InteractingSLE.Theorem14.GW4Fix.CLoc
