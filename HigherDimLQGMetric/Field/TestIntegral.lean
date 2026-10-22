import HigherDimLQGMetric.Field.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Integrals of continuous families of test functions commute with distributions

Packet F1 (basic sphere-average layer). Port of LQGMetric's
`lqg_metric/LQGMetric/Field/CircleAvgIntegral.lean`
(`Jet`, `jet`, `exists_jet_factor`, `exists_testIntegral`) from `ℂ` to `Rd d` (ruling M10), and
from interval integrals `∫_a^b … dθ` to integrals against a finite measure `μ` on a compact,
second-countable parameter space `X` (for the sphere averages, `X` is the unit sphere).

For a compact `K ⊆ ℝ^d` and a continuous family `F : X → 𝓓_K(ℝ^d, ℝ)`, the pointwise integral
`y ↦ ∫ F x y dμ(x)` is again an element `I` of `𝓓_K`, and every continuous linear functional `T`
on `𝓓_K` satisfies `T I = ∫ T (F x) dμ(x)` (`exists_testIntegral`).

This is the standard fact that a distribution commutes with integrals of test functions depending
continuously on a parameter (Hörmander, *The Analysis of Linear Partial Differential Operators I*,
Thm 2.1.3). Proof as in the 2D layer: a continuous functional on the Fréchet space `𝓓_K` is
bounded by finitely many of its seminorms (`Seminorm.bound_of_continuous`), hence factors through
the Banach space of finite jets `Jet d s` (Hahn–Banach, `exists_extension_norm_eq`), where Bochner
integrals commute with continuous functionals; the derivatives of `I` are computed by
differentiation under the integral sign (`hasFDerivAt_integral_of_dominated_of_fderiv_le`, the
bound coming from the compactness of `X`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped Distributions BoundedContinuousFunction

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

namespace TestIntegral

variable {d : ℕ}

/-- The Banach space of finite jets indexed by `s` (a `def`, so that only its normed
structure is seen by instance search). -/
def Jet (d : ℕ) (s : Finset ℕ) : Type :=
  ∀ i : s, Rd d →ᵇ (ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => Rd d) ℝ)

instance (s : Finset ℕ) : NormedAddCommGroup (Jet d s) := Pi.normedAddCommGroup
instance (s : Finset ℕ) : NormedSpace ℝ (Jet d s) := Pi.normedSpace
instance (s : Finset ℕ) : CompleteSpace (Jet d s) :=
  inferInstanceAs
    (CompleteSpace (∀ i : s, Rd d →ᵇ (ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => Rd d) ℝ)))

/-- The `i`-th component of a jet. -/
def jetProj (s : Finset ℕ) (i : s) :
    Jet d s →L[ℝ] Rd d →ᵇ (ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => Rd d) ℝ) :=
  ContinuousLinearMap.proj (R := ℝ)
    (φ := fun i : s => Rd d →ᵇ (ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => Rd d) ℝ)) i

theorem norm_jetProj_le (s : Finset ℕ) (v : Jet d s) (i : s) : ‖jetProj s i v‖ ≤ ‖v‖ :=
  norm_le_pi_norm (G := fun i : s =>
    Rd d →ᵇ (ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => Rd d) ℝ)) v i

variable {K : Compacts (Rd d)}

/-- The jet map `φ ↦ (D^i φ)_{i ∈ s}`. -/
def jet (K : Compacts (Rd d)) (s : Finset ℕ) : 𝓓^{⊤}_{K}(Rd d, ℝ) →L[ℝ] Jet d s :=
  ContinuousLinearMap.pi
    (φ := fun i : s => Rd d →ᵇ (ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => Rd d) ℝ))
    fun i => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ)

theorem jet_apply (s : Finset ℕ) (φ : 𝓓^{⊤}_{K}(Rd d, ℝ)) (i : s) (y : Rd d) :
    jetProj s i (jet K s φ) y = iteratedFDeriv ℝ (i : ℕ) φ y := by
  change (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ) φ) y = _
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]

/-- Every continuous linear functional on `𝓓_K` factors through a finite jet space. -/
theorem exists_jet_factor (T : 𝓓^{⊤}_{K}(Rd d, ℝ) →L[ℝ] ℝ) :
    ∃ (s : Finset ℕ) (S : StrongDual ℝ (Jet d s)), ∀ φ, T φ = S (jet K s φ) := by
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ (Rd d) ℝ ⊤ K)
    ((normSeminorm ℝ ℝ).comp T.toLinearMap) (continuous_norm.comp T.continuous)
  have hbound : ∀ φ, ‖T φ‖ ≤ (C : ℝ) * ‖jet K s φ‖ := by
    intro φ
    have h1 := hle φ
    simp only [Seminorm.comp_apply, coe_normSeminorm, smul_apply,
      NNReal.smul_def, smul_eq_mul] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ C.2)
    refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_
    rw [ContDiffMapSupportedIn.seminorm_apply]
    exact norm_jetProj_le s (jet K s φ) ⟨i, hi⟩
  let J := (jet K s).toLinearMap
  have hker : LinearMap.ker J ≤ LinearMap.ker T.toLinearMap := by
    intro φ hφ
    simp only [LinearMap.mem_ker] at hφ ⊢
    have := hbound φ
    rw [show jet K s φ = 0 from hφ] at this
    simpa using this
  let f₀ : LinearMap.range J →ₗ[ℝ] ℝ :=
    ((LinearMap.ker J).liftQ T.toLinearMap hker).comp J.quotKerEquivRange.symm.toLinearMap
  have hf₀ : ∀ φ, f₀ ⟨J φ, LinearMap.mem_range_self J φ⟩ = T φ := by
    intro φ
    simp only [f₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let f : StrongDual ℝ (LinearMap.range J) := f₀.mkContinuous C (by
    rintro ⟨v, φ, rfl⟩
    rw [hf₀]
    exact hbound φ)
  obtain ⟨S, hS, -⟩ := exists_extension_norm_eq (LinearMap.range J) f
  refine ⟨s, S, fun φ => ?_⟩
  have := hS ⟨J φ, LinearMap.mem_range_self J φ⟩
  rw [← hf₀ φ]
  exact this.symm

/-! ## Integrals of continuous families -/

section Family

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  (F : X → 𝓓^{⊤}_{K}(Rd d, ℝ))

/-- `∫ D^i (F x) y dμ(x)`. -/
def intDeriv (i : ℕ) (y : Rd d) : ContinuousMultilinearMap ℝ (fun _ : Fin i => Rd d) ℝ :=
  ∫ x, iteratedFDeriv ℝ i (F x) y ∂μ

variable {F}

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem continuous_iteratedFDeriv_family (hF : Continuous F) (i : ℕ) (y : Rd d) :
    Continuous fun x => iteratedFDeriv ℝ i (F x) y := by
  have := ((BoundedContinuousFunction.evalCLM ℝ y).continuous.comp
    ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous.comp hF))
  refine this.congr fun x => ?_
  simp

omit [SecondCountableTopology X] in
theorem integrable_of_continuous_compact {E : Type*} [NormedAddCommGroup E] {g : X → E}
    (hg : Continuous g) : Integrable g μ :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [IsFiniteMeasure μ] in
theorem integral_comp_lie {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] (e : E ≃ₗᵢ[ℝ] G) (f : X → E) :
    ∫ x, e (f x) ∂μ = e (∫ x, f x ∂μ) :=
  e.toLinearIsometry.integral_comp_comm f

theorem hasFDerivAt_intDeriv (hF : Continuous F) (i : ℕ) (y₀ : Rd d) :
    HasFDerivAt (intDeriv μ F i) (∫ x, fderiv ℝ (iteratedFDeriv ℝ i (F x)) y₀ ∂μ) y₀ := by
  set e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Rd d) ℝ
  have hF' : ∀ x y, fderiv ℝ (iteratedFDeriv ℝ i (F x)) y =
      e (iteratedFDeriv ℝ (i + 1) (F x) y) := by
    intro x y
    rw [fderiv_iteratedFDeriv]
    rfl
  have hcont : Continuous fun x => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i + 1) (F x) :=
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i + 1)).continuous.comp hF
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun x => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i + 1) (F x)) hcont.continuousOn
  change HasFDerivAt (fun y => ∫ x, iteratedFDeriv ℝ i (F x) y ∂μ) _ y₀
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => B)
    (F' := fun y x => fderiv ℝ (iteratedFDeriv ℝ i (F x)) y) (s := univ) Filter.univ_mem
  · exact Eventually.of_forall fun y =>
      (continuous_iteratedFDeriv_family hF i y).aestronglyMeasurable
  · exact integrable_of_continuous_compact μ (continuous_iteratedFDeriv_family hF i y₀)
  · simp_rw [hF']
    exact (e.continuous.comp (continuous_iteratedFDeriv_family hF (i + 1) y₀)).aestronglyMeasurable
  · refine Eventually.of_forall fun x y _ => ?_
    rw [norm_fderiv_iteratedFDeriv]
    refine le_trans ?_ (hB x (mem_univ x))
    have := (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i + 1) (F x)).norm_coe_le_norm y
    simpa [ContDiffMapSupportedIn.structureMapCLM_top_apply] using this
  · exact integrable_const B
  · refine Eventually.of_forall fun x y _ => ?_
    have hlt : ((i : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast ENat.natCast_lt_top i
    exact (((F x).contDiff.differentiable_iteratedFDeriv hlt).differentiableAt).hasFDerivAt

theorem iteratedFDeriv_intFun (hF : Continuous F) (i : ℕ) :
    iteratedFDeriv ℝ i (fun y => ∫ x, F x y ∂μ) = intDeriv μ F i := by
  induction i with
  | zero =>
    funext y
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [intDeriv, Function.comp_apply]
    rw [← integral_comp_lie μ (E := ℝ) (G := ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Rd d) ℝ)
      (continuousMultilinearCurryFin0 ℝ (Rd d) ℝ).symm (fun x => F x y)]
    congr 1
  | succ i ih =>
    funext y
    rw [iteratedFDeriv_succ_eq_comp_left, ih, Function.comp_apply,
      (hasFDerivAt_intDeriv μ hF i y).fderiv]
    set e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Rd d) ℝ
    have hF' : ∀ x, fderiv ℝ (iteratedFDeriv ℝ i (F x)) y =
        e (iteratedFDeriv ℝ (i + 1) (F x) y) := by
      intro x
      rw [fderiv_iteratedFDeriv]
      rfl
    simp_rw [hF']
    rw [integral_comp_lie μ (E := ContinuousMultilinearMap ℝ (fun _ : Fin (i + 1) => Rd d) ℝ)
      (G := Rd d →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin i => Rd d) ℝ) e
      (fun x => iteratedFDeriv ℝ (i + 1) (F x) y), LinearIsometryEquiv.symm_apply_apply]
    rfl

/-- **Integral of a continuous family in `𝓓_K`.** The pointwise integral is in `𝓓_K` and every
continuous linear functional commutes with the integral. -/
theorem exists_testIntegral (hF : Continuous F) :
    ∃ I : 𝓓^{⊤}_{K}(Rd d, ℝ), (∀ y, I y = ∫ x, F x y ∂μ) ∧
      ∀ T : 𝓓^{⊤}_{K}(Rd d, ℝ) →L[ℝ] ℝ, T I = ∫ x, T (F x) ∂μ := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ x, F x y ∂μ) := by
    refine contDiff_of_differentiable_iteratedFDeriv fun m _ => ?_
    rw [iteratedFDeriv_intFun μ hF m]
    exact fun y => (hasFDerivAt_intDeriv μ hF m y).differentiableAt
  have hsupp : Function.support (fun y => ∫ x, F x y ∂μ) ⊆ K := by
    intro y hy
    by_contra hK
    apply hy
    simp only
    rw [integral_congr_ae (g := fun _ => (0 : ℝ))
      (Eventually.of_forall fun x => (F x).zero_on_compl hK)]
    simp
  set I := ContDiffMapSupportedIn.of_support_subset hcd hsupp
  refine ⟨I, fun y => rfl, fun T => ?_⟩
  obtain ⟨s, S, hS⟩ := exists_jet_factor T
  have hjc : Continuous fun x => jet K s (F x) := (jet K s).continuous.comp hF
  have hji : Integrable (fun x => jet K s (F x)) μ := integrable_of_continuous_compact μ hjc
  have key : ∀ (i : s) (y : Rd d),
      jetProj s i (jet K s I) y = jetProj s i (∫ x, jet K s (F x) ∂μ) y := by
    intro i y
    have hev := ((BoundedContinuousFunction.evalCLM ℝ y).comp
      (jetProj s i)).integral_comp_comm hji
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      BoundedContinuousFunction.evalCLM_apply] at hev
    rw [← hev, jet_apply]
    simp_rw [jet_apply]
    exact congrFun (iteratedFDeriv_intFun μ hF (i : ℕ)) y
  have hjet : jet K s I = ∫ x, jet K s (F x) ∂μ :=
    funext fun i => BoundedContinuousFunction.ext (key i)
  rw [hS, hjet, ← S.integral_comp_comm hji]
  simp_rw [← hS]

end Family

end TestIntegral

end HigherDimLQGMetric
