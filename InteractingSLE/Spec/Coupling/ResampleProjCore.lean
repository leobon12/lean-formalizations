import InteractingSLE.Spec.Coupling.ResampleBridge
import InteractingSLE.Spec.Coupling.Assembly11B
import InteractingSLE.GFF.LocalSets.GermLaw

/-!
# Projection independence by Gaussian resampling: the measure-level core (Theorem 1.1)

Packet PROVE-T11-PROJ (Astra §1, "Finite families: Gaussian resampling supplies compatibility", pp. 5–6, (1.9)).
For an open `V ⊆ ℍ` let `G` be a Borel version of the projection onto `H(V)` (Proposition 3.1,
`LocalSets.exists_markovMap`) and `c = 𝔥₀` the time-zero harmonic mean. The **resampling** of a field law `μ` at `V`
is the law of `x − G(x − c) + G(y)` with `x ~ μ` and an independent zero-boundary GFF `y`: the projection of the
centred field onto `H(V)` is replaced by a fresh one.

Everything is stated for finite measures `μ ≪ fieldLaw0 u₀` on `𝒟'(ℍ)` (the field laws of the stages of the finite-family
construction), and characteristic functionals are tested on the Dirichlet directions `−Δf/2π`, `f ∈ C_c^∞(V)`:

* `IsProjIndepMeasure V μ` : `∫ e^{i x(−Δf/2π + Ξ)} dμ = exp(−‖∇f‖²/2 − ⟪∇f, covVec_V Ξ⟫) ∫ e^{i x(Ξ)} dμ`;
* `isProjIndepMeasure_fieldLaw0` : the base case (direct Gaussian computation);
* `IsProjIndepMeasure.mono` : nesting `U ⊆ V`;
* `exists_tendsto_ae_projMap` : `x(−Δf_n/2π) → G(x − c)(Φ)` almost surely under `fieldLaw0 u₀` along Dirichlet
  approximations `∇f_n → covVec_V Φ`;
* `integral_cexp_resample` : the characteristic functional of the resampled law;
* `integral_cexp_resample_eq_of_shift` : resampling does not change the characteristic functional at `Ξ` if `μ` has
  the Gaussian shift rule in the directions `Ξ − Δf/2π` (`IsProjShiftMeasure`); in particular a projection-independent
  law is resampling invariant (`resample_eq_of_isProjIndepMeasure`);
* `isProjIndepMeasure_resample` : every resampled law is projection-independent at `V`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

namespace InteractingSLE

namespace Coupling

open LQGMetric LQGMetric.MarkovZB GFF LocalSets QuantumZipper.K3 QuantumZipper.Thm11Asm

/-! ### The Gaussian factor and the two projection rules -/

section Defs

/-- The Gaussian factor `exp(−‖∇f‖²/2 − ⟪∇f, covVec_V Ξ⟫)` of projection independence at `V`. -/
def projFactor (V : Opens ℂ) (f : zsSub (V : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) : ℂ :=
  Complex.exp (((-(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 -
    ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ξ⟫ : ℝ) : ℂ))

/-- **Projection independence of a field law at `V`**, free of projection versions: every Dirichlet direction
`−Δf/2π`, `f ∈ C_c^∞(V)`, enters the characteristic functional with the Gaussian factor of `H(V)`. -/
def IsProjIndepMeasure (V : Opens ℂ) (μ : Measure (DistOn upperHalfPlaneOpens)) : Prop :=
  ∀ (f : zsSub (V : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens),
    ∫ x, Complex.exp (Complex.I * (x (lapTest V f + Ξ) : ℂ)) ∂μ =
      projFactor V f Ξ * ∫ x, Complex.exp (Complex.I * (x Ξ : ℂ)) ∂μ

/-- **The Gaussian shift rule at one test function `Ξ`**: removing a Dirichlet direction `−Δf/2π`, `f ∈ C_c^∞(V)`,
from `Ξ` multiplies the characteristic functional by `exp(−‖∇f‖²/2 + ⟪∇f, covVec_V Ξ⟫)`. -/
def IsProjShiftMeasure (V : Opens ℂ) (μ : Measure (DistOn upperHalfPlaneOpens))
    (Ξ : TestOn upperHalfPlaneOpens) : Prop :=
  ∀ f : zsSub (V : Set ℂ),
    ∫ x, Complex.exp (Complex.I * (x (Ξ - lapTest V f) : ℂ)) ∂μ =
      Complex.exp (((-(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 +
        ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ξ⟫ : ℝ) : ℂ)) *
        ∫ x, Complex.exp (Complex.I * (x Ξ : ℂ)) ∂μ

end Defs

/-! ### Gram-vector algebra -/

section Gram

variable {V : Opens ℂ}

theorem covVec_lapTest_self (hVH : (V : Set ℂ) ⊆ H) (f : zsSub (V : Set ℂ)) :
    covVec (V : Set ℂ) (lapTest V f) = gradFeat (V : Set ℂ) f.1 :=
  covVec_lapTest (show V ≤ upperHalfPlaneOpens from hVH) V.isOpen hVH subset_rfl f

/-- `‖covVec_D(−Δf/2π + Ξ)‖² = ‖∇f‖² + 2⟪∇f, covVec_V Ξ⟫ + ‖covVec_D Ξ‖²` for `f ∈ C_c^∞(V)`, `V ⊆ D ⊆ ℍ`. -/
theorem norm_covVec_lapTest_add_sq {D : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) (hVD : (V : Set ℂ) ⊆ D)
    (f : zsSub (V : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ‖covVec D ⇑(lapTest V f + Ξ)‖ ^ 2 = ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 +
      2 * ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ξ⟫ + ‖covVec D Ξ‖ ^ 2 := by
  have hVH : V ≤ upperHalfPlaneOpens := fun z hz => hDH (hVD hz)
  rw [covVec_add hD hDH, covVec_lapTest hVH hD hDH hVD f, norm_add_sq_real,
    norm_gradFeat_eq hVD f.2, inner_gradFeat_covVec_eq V.isOpen hD hDH hVD f.2]

/-- `‖covVec_D(Ξ − Δf/2π)‖² = ‖covVec_D Ξ‖² − 2⟪∇f, covVec_V Ξ⟫ + ‖∇f‖²`. -/
theorem norm_covVec_sub_lapTest_sq {D : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) (hVD : (V : Set ℂ) ⊆ D)
    (f : zsSub (V : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ‖covVec D ⇑(Ξ - lapTest V f)‖ ^ 2 = ‖covVec D Ξ‖ ^ 2 -
      2 * ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ξ⟫ + ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 := by
  have hVH : V ≤ upperHalfPlaneOpens := fun z hz => hDH (hVD hz)
  rw [covVec_sub hD hDH, covVec_lapTest hVH hD hDH hVD f, norm_sub_sq_real,
    norm_gradFeat_eq hVD f.2, real_inner_comm, inner_gradFeat_covVec_eq V.isOpen hD hDH hVD f.2]

/-- The projection factor in the direction `Ξ − Δf/2π` is the inverse of the shift factor. -/
theorem projFactor_sub_lapTest (hVH : (V : Set ℂ) ⊆ H) (f : zsSub (V : Set ℂ))
    (Ξ : TestOn upperHalfPlaneOpens) :
    projFactor V f (Ξ - lapTest V f) = Complex.exp (((1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 -
      ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ξ⟫ : ℝ) : ℂ) := by
  rw [projFactor, covVec_sub V.isOpen hVH, covVec_lapTest_self hVH, inner_sub_right,
    real_inner_self_eq_norm_sq]
  congr 2
  ring

end Gram

/-! ### The two rules -/

section Rules

variable {V : Opens ℂ}

/-- Projection independence gives the shift rule at every test function. -/
theorem IsProjIndepMeasure.isProjShiftMeasure {μ : Measure (DistOn upperHalfPlaneOpens)}
    (hVH : (V : Set ℂ) ⊆ H) (h : IsProjIndepMeasure V μ) (Ξ : TestOn upperHalfPlaneOpens) :
    IsProjShiftMeasure V μ Ξ := by
  intro f
  have h1 := h f (Ξ - lapTest V f)
  rw [add_sub_cancel, projFactor_sub_lapTest hVH] at h1
  rw [h1, ← mul_assoc, ← Complex.exp_add, ← Complex.ofReal_add]
  have : -(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 +
      ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ξ⟫ +
      ((1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 - ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ξ⟫) =
      0 := by ring
  rw [this, Complex.ofReal_zero, Complex.exp_zero, one_mul]

/-- **Nesting**: projection independence at `V` implies it at every open `U ⊆ V`. -/
theorem IsProjIndepMeasure.mono {μ : Measure (DistOn upperHalfPlaneOpens)} {U : Opens ℂ}
    (hVH : (V : Set ℂ) ⊆ H) (hUV : U ≤ V) (h : IsProjIndepMeasure V μ) : IsProjIndepMeasure U μ := by
  intro f Ξ
  have hUV' : (U : Set ℂ) ⊆ V := hUV
  set f' : zsSub (V : Set ℂ) := zsSubIncl hUV' f with hf'
  have hf1 : f'.1 = f.1 := rfl
  have hL : lapTest V f' = lapTest U f := by
    ext z
    rw [coe_lapTest (show V ≤ upperHalfPlaneOpens from hVH),
      coe_lapTest (show U ≤ upperHalfPlaneOpens from fun z hz => hVH (hUV hz))]
    rfl
  have hc : projFactor V f' Ξ = projFactor U f Ξ := by
    rw [projFactor, projFactor, hf1, norm_gradFeat_eq hUV' f.2,
      inner_gradFeat_covVec_eq U.isOpen V.isOpen hVH hUV' f.2]
  rw [← hL, ← hc]
  exact h f' Ξ

end Rules

/-! ### The time-zero field law and the Markov map -/

section FieldLaw

variable {V : Opens ℂ} {u₀ : ℂ → ℝ}

/-- The time-zero harmonic mean `𝔥₀ = u₀` as a distribution on `ℍ` (the mean of `fieldLaw0 u₀`). -/
abbrev meanH (u₀ : ℂ → ℝ) : DistOn upperHalfPlaneOpens :=
  Distribution.ofFun upperHalfPlaneOpens u₀ volume ⊤

theorem restrictDist_upperHalfPlane (g : DistOn upperHalfPlaneOpens) :
    restrictDist upperHalfPlaneOpens g = g := by
  ext φ
  rw [restrictDist_apply]
  congr 1
  ext z
  rw [coe_testIncl le_rfl]

theorem fieldLaw0_eq_map (u₀ : ℂ → ℝ) :
    fieldLaw0 u₀ = (zbLaw upperHalfPlaneOpens).map fun g => g + meanH u₀ := by
  rw [fieldLaw0, gaussLaw]
  simp_rw [restrictDist_upperHalfPlane]

/-- A harmonic mean annihilates the Dirichlet directions. -/
theorem meanH_apply_lapTest (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hVH : (V : Set ℂ) ⊆ H)
    (f : zsSub (V : Set ℂ)) : meanH u₀ (lapTest V f) = 0 := by
  have hc : ContinuousOn u₀ H := fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt
  rw [meanH, Distribution.ofFun_apply (hc.locallyIntegrableOn upperHalfPlaneOpens.isOpen.measurableSet),
    coe_lapTest (show V ≤ upperHalfPlaneOpens from hVH)]
  simp only [smul_eq_mul]
  simp_rw [mul_comm (cmTest (zsTest f.2) _)]
  exact HarmLoc.integral_mul_cmTest_of_harmonic isOpen_H hu₀ (zsTest f.2) (f.2.2.2.trans hVH)

/-- Almost-sure statements under `zbLaw` about `g + 𝔥₀` hold under `fieldLaw0`. -/
theorem ae_fieldLaw0_of_ae_zbLaw {p : DistOn upperHalfPlaneOpens → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ g ∂zbLaw upperHalfPlaneOpens, p (g + meanH u₀)) : ∀ᵐ x ∂fieldLaw0 u₀, p x := by
  rw [fieldLaw0_eq_map]
  exact (ae_map_iff (measurable_add_distOnConst _).aemeasurable hp).2 h

/-- A Borel version of the projection onto `H(V)` for the law `zbLaw ℍ` (Proposition 3.1). -/
theorem exists_markovMap_zbLaw (V : Opens ℂ) (hVH : (V : Set ℂ) ⊆ H) :
    ∃ G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens, Measurable G ∧
      GFF.IsMarkovDecomposition V upperHalfPlaneOpens id G (zbLaw upperHalfPlaneOpens) := by
  obtain ⟨G, hGm, hG⟩ := LocalSets.exists_markovMap V hVH
  exact ⟨G, hGm, hG (isZeroBoundaryGFF_zbLaw (D := upperHalfPlaneOpens) subset_rfl)⟩

variable {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hGm : Measurable G)
  (hGd : GFF.IsMarkovDecomposition V upperHalfPlaneOpens id G (zbLaw upperHalfPlaneOpens))
include hGm hGd

/-- **The projection as an almost-sure limit of Dirichlet pairings** under `zbLaw`, along a subsequence of a
Dirichlet approximation `∇f_n → covVec_V Φ`. -/
theorem exists_tendsto_ae_zbLaw (hVH : (V : Set ℂ) ⊆ H) (Φ : TestOn upperHalfPlaneOpens) :
    ∃ f : ℕ → zsSub (V : Set ℂ),
      Tendsto (fun n => gradFeat (V : Set ℂ) (f n).1) atTop (𝓝 (covVec (V : Set ℂ) Φ)) ∧
      ∀ᵐ g ∂zbLaw upperHalfPlaneOpens, Tendsto (fun n => g (lapTest V (f n))) atTop (𝓝 (G g Φ)) := by
  have hVH' : V ≤ upperHalfPlaneOpens := hVH
  obtain ⟨f, hf, hlim⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hVH' hGd Φ
  have hint : ∀ n, Integrable (fun g : DistOn upperHalfPlaneOpens => (G g Φ - g (lapTest V (f n))) ^ 2)
      (zbLaw upperHalfPlaneOpens) := fun n =>
    (memLp_two_iff_integrable_sq (((measurable_distOn_apply Φ).comp hGm).sub
      (measurable_distOn_apply _)).aestronglyMeasurable).1 (memLp_markov_sub_lapTest hVH' hGd Φ (f n))
  obtain ⟨ns, hns, hae⟩ := exists_seq_tendsto_ae_of_tendsto_integral_sq (P := zbLaw upperHalfPlaneOpens)
    (f := fun g => G g Φ) (F := fun n g => g (lapTest V (f n)))
    (fun n => (measurable_distOn_apply _).aestronglyMeasurable)
    ((measurable_distOn_apply Φ).comp hGm).aestronglyMeasurable hint hlim
  exact ⟨fun i => f (ns i), hf.comp hns.tendsto_atTop, hae⟩

omit hGm in
/-- The harmonic part `g − G g` annihilates the Dirichlet directions of `V`, `zbLaw`-almost surely. -/
theorem ae_apply_lapTest_eq_zbLaw (hVH : (V : Set ℂ) ⊆ H) (f : zsSub (V : Set ℂ)) :
    ∀ᵐ g ∂zbLaw upperHalfPlaneOpens, g (lapTest V f) = G g (lapTest V f) := by
  have hVH' : V ≤ upperHalfPlaneOpens := hVH
  filter_upwards [ae_isHarmonicDistOn_of_isMarkovDecomposition hVH' hGd] with g hg
  have h0 := LocalSets.IsHarmonicDistOn.apply_lapTest_eq_zero V.isOpen hg hVH' subset_rfl f
  rw [sub_apply] at h0
  exact sub_eq_zero.1 h0

/-- The characteristic functional of the projection: `∫ e^{i G(g)(Φ)} d zbLaw = exp(−‖covVec_V Φ‖²/2)`. -/
theorem integral_cexp_markovMap (hVH : (V : Set ℂ) ⊆ H) (Φ : TestOn upperHalfPlaneOpens) :
    ∫ g, Complex.exp (Complex.I * (G g Φ : ℂ)) ∂zbLaw upperHalfPlaneOpens =
      ((Real.exp (-(1 / 2) * ‖covVec (V : Set ℂ) Φ‖ ^ 2) : ℝ) : ℂ) := by
  have hVH' : V ≤ upperHalfPlaneOpens := hVH
  have hX := hGd.isZBGFFExtOn
  have hm : AEMeasurable (fun g => G g Φ) (zbLaw upperHalfPlaneOpens) :=
    ((measurable_distOn_apply Φ).comp hGm).aemeasurable
  rw [GFF.integral_exp_I_mul_of_hasGaussianLaw (hX.gaussian.hasGaussianLaw_eval Φ) (hX.centered Φ),
    variance_of_integral_eq_zero hm (hX.centered Φ)]
  have := integral_sq_of_isZBGFFExtOn hVH' hX Φ
  rw [this]

/-- **The projection as an almost-sure limit under every `μ ≪ fieldLaw0 u₀`.** -/
theorem exists_tendsto_ae_projMap (hVH : (V : Set ℂ) ⊆ H) (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (Φ : TestOn upperHalfPlaneOpens) :
    ∃ f : ℕ → zsSub (V : Set ℂ),
      Tendsto (fun n => gradFeat (V : Set ℂ) (f n).1) atTop (𝓝 (covVec (V : Set ℂ) Φ)) ∧
      ∀ μ : Measure (DistOn upperHalfPlaneOpens), μ ≪ fieldLaw0 u₀ →
        ∀ᵐ x ∂μ, Tendsto (fun n => x (lapTest V (f n))) atTop (𝓝 (G (x - meanH u₀) Φ)) := by
  obtain ⟨f, hf, hae⟩ := exists_tendsto_ae_zbLaw hGm hGd hVH Φ
  refine ⟨f, hf, fun μ hμ => hμ.ae_le ?_⟩
  have hmeas : ∀ n, Measurable fun x : DistOn upperHalfPlaneOpens =>
      x (lapTest V (f n)) - G (x - meanH u₀) Φ := fun n =>
    (measurable_distOn_apply _).sub ((measurable_distOn_apply Φ).comp (hGm.comp
      (measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).sub_const _)))
  have hset : MeasurableSet {x : DistOn upperHalfPlaneOpens |
      Tendsto (fun n => x (lapTest V (f n)) - G (x - meanH u₀) Φ) atTop (𝓝 0)} :=
    measurableSet_tendsto (𝓝 0) hmeas
  have h := ae_fieldLaw0_of_ae_zbLaw (u₀ := u₀) hset (by
    filter_upwards [hae] with g hg
    simp only [add_sub_cancel_right]
    have e : ∀ n, (g + meanH u₀) (lapTest V (f n)) = g (lapTest V (f n)) := fun n => by
      rw [add_apply, meanH_apply_lapTest hu₀ hVH, add_zero]
    simp_rw [e]
    exact tendsto_sub_nhds_zero_iff.2 hg)
  filter_upwards [h] with x hx
  exact tendsto_sub_nhds_zero_iff.1 hx

/-- **The harmonic part annihilates the Dirichlet directions under every `μ ≪ fieldLaw0 u₀`.** -/
theorem ae_apply_lapTest_eq_projMap (hVH : (V : Set ℂ) ⊆ H) (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (f : zsSub (V : Set ℂ)) {μ : Measure (DistOn upperHalfPlaneOpens)} (hμ : μ ≪ fieldLaw0 u₀) :
    ∀ᵐ x ∂μ, x (lapTest V f) = G (x - meanH u₀) (lapTest V f) := by
  refine hμ.ae_le (ae_fieldLaw0_of_ae_zbLaw ?_ ?_)
  · exact measurableSet_eq_fun (measurable_distOn_apply _) ((measurable_distOn_apply _).comp (hGm.comp
      (measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).sub_const _)))
  · filter_upwards [ae_apply_lapTest_eq_zbLaw hGd hVH f] with g hg
    simp only [add_sub_cancel_right]
    rw [add_apply, meanH_apply_lapTest hu₀ hVH, add_zero]
    exact hg

end FieldLaw

/-! ### Field laws integrated over an event -/

section SecMeas

variable {Ω X : Type*} [MeasurableSpace X] {mΩ : MeasurableSpace Ω}

/-- The field law integrated over an event `A`: `B ↦ ∫_A η(ω, B) dP(ω)`. -/
def secMeas (P : Measure Ω) (A : Set Ω) (η : Kernel Ω X) : Measure X :=
  ((P.restrict A) ⊗ₘ η).map Prod.snd

variable {P : Measure Ω} [IsFiniteMeasure P]

theorem secMeas_apply {η : Kernel Ω X} [IsMarkovKernel η] {A : Set Ω} (hA : MeasurableSet A) {B : Set X}
    (hB : MeasurableSet B) : secMeas P A η B = (P ⊗ₘ η) (A ×ˢ B) := by
  rw [secMeas, Measure.map_apply measurable_snd hB, show (Prod.snd ⁻¹' B : Set (Ω × X)) = univ ×ˢ B by
      ext; simp, Measure.compProd_apply_prod MeasurableSet.univ hB,
    Measure.compProd_apply_prod hA hB, Measure.restrict_univ]

instance isFiniteMeasure_secMeas {η : Kernel Ω X} [IsMarkovKernel η] {A : Set Ω} :
    IsFiniteMeasure (secMeas P A η) := by
  rw [secMeas]; infer_instance

theorem lintegral_secMeas {η : Kernel Ω X} [IsMarkovKernel η] {A : Set Ω} {F : X → ℝ≥0∞}
    (hF : Measurable F) : ∫⁻ x, F x ∂secMeas P A η = ∫⁻ ω in A, ∫⁻ x, F x ∂η ω ∂P := by
  rw [secMeas, lintegral_map hF measurable_snd]
  exact Measure.lintegral_compProd (f := fun p : Ω × X => F p.2) (hF.comp measurable_snd)

theorem integral_secMeas {η : Kernel Ω X} [IsMarkovKernel η] {A : Set Ω} {F : X → ℂ} (hF : Measurable F)
    (hb : ∀ x, ‖F x‖ ≤ 1) : ∫ x, F x ∂secMeas P A η = ∫ ω in A, ∫ x, F x ∂η ω ∂P := by
  rw [secMeas, integral_map measurable_snd.aemeasurable hF.aestronglyMeasurable, Measure.integral_compProd]
  exact Integrable.of_bound (hF.comp measurable_snd).aestronglyMeasurable 1
    (Eventually.of_forall fun p => hb p.2)

theorem secMeas_mono {η : Kernel Ω X} [IsMarkovKernel η] {A A' : Set Ω} (hA : MeasurableSet A)
    (hA' : MeasurableSet A') (h : A ⊆ A') : secMeas P A η ≤ secMeas P A' η :=
  Measure.le_iff.2 fun B hB => by
    rw [secMeas_apply hA hB, secMeas_apply hA' hB]
    exact measure_mono (prod_mono h subset_rfl)

theorem secMeas_map {Y : Type*} [MeasurableSpace Y] {η : Kernel Ω X} [IsMarkovKernel η] {A : Set Ω}
    (hA : MeasurableSet A) {f : X → Y} (hf : Measurable f) :
    secMeas P A (η.map f) = (secMeas P A η).map f := by
  have := Kernel.IsMarkovKernel.map η hf
  ext B hB
  rw [secMeas_apply hA hB, Measure.map_apply hf hB, secMeas_apply hA (hf hB),
    compProd_map_apply_prod hf hA hB]

theorem secMeas_const {μ : Measure X} [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) :
    secMeas P A (Kernel.const Ω μ) = P A • μ := by
  ext B hB
  rw [secMeas_apply hA hB, Measure.compProd_apply_prod hA hB]
  simp [Kernel.const_apply, lintegral_const, mul_comm]

end SecMeas

section SecMeasRect

variable {Ω X : Type*} [MeasurableSpace X]

/-- Agreement on rectangles is equality of the integrated laws. -/
theorem RectAgree.secMeas_eq {𝒜 mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) {P : Measure Ω} [IsFiniteMeasure P]
    {E : Set Ω} {κ₁ κ₂ : Kernel Ω X} [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] (h : RectAgree 𝒜 P E κ₁ κ₂)
    {A : Set Ω} (hA : MeasurableSet[𝒜] A) (hAE : A ⊆ E) : secMeas P A κ₁ = secMeas P A κ₂ :=
  Measure.ext fun B hB => by
    rw [secMeas_apply (h𝒜 A hA) hB, secMeas_apply (h𝒜 A hA) hB]
    exact h A hA hAE B hB

end SecMeasRect

/-! ### Resampling the projection onto `H(V)` -/

section Resample

variable {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}

/-- The resampling map `(x, y) ↦ x − G(x − c) + G(y)`. -/
def resampleMap (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (c : DistOn upperHalfPlaneOpens)
    (p : DistOn upperHalfPlaneOpens × DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  p.1 - G (p.1 - c) + G p.2

theorem measurable_resampleMap (hGm : Measurable G) (c : DistOn upperHalfPlaneOpens) :
    Measurable (resampleMap G c) := by
  refine measurable_distOn_iff.2 fun φ => ?_
  show Measurable fun p : DistOn upperHalfPlaneOpens × DistOn upperHalfPlaneOpens =>
    p.1 φ - G (p.1 - c) φ + G p.2 φ
  exact (((measurable_distOn_apply φ).comp measurable_fst).sub
    ((measurable_distOn_apply φ).comp (hGm.comp ((measurable_sub_distOnConst c).comp measurable_fst)))).add
    ((measurable_distOn_apply φ).comp (hGm.comp measurable_snd))

/-- **The resampled law**: `x − G(x − c) + G(y)` with `x ~ μ` and an independent `y ~ zbLaw ℍ`. -/
def resample (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (c : DistOn upperHalfPlaneOpens)
    (μ : Measure (DistOn upperHalfPlaneOpens)) : Measure (DistOn upperHalfPlaneOpens) :=
  (μ.prod (zbLaw upperHalfPlaneOpens)).map (resampleMap G c)

instance isFiniteMeasure_resample (c : DistOn upperHalfPlaneOpens) (μ : Measure (DistOn upperHalfPlaneOpens))
    [IsFiniteMeasure μ] : IsFiniteMeasure (resample G c μ) := by
  rw [resample]; infer_instance

/-- The characteristic functional of the resampled law. -/
theorem integral_cexp_resample (hGm : Measurable G) (c : DistOn upperHalfPlaneOpens)
    (μ : Measure (DistOn upperHalfPlaneOpens)) [IsFiniteMeasure μ] (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ z, Complex.exp (Complex.I * (z Ξ : ℂ)) ∂resample G c μ =
      (∫ x, Complex.exp (Complex.I * ((x Ξ - G (x - c) Ξ : ℝ) : ℂ)) ∂μ) *
        ∫ y, Complex.exp (Complex.I * (G y Ξ : ℂ)) ∂zbLaw upperHalfPlaneOpens := by
  rw [resample, integral_map (measurable_resampleMap hGm c).aemeasurable
    (measurable_exp_I_mul (measurable_distOn_apply Ξ)).aestronglyMeasurable, ← integral_prod_mul]
  congr 1
  funext p
  rw [← Complex.exp_add]
  congr 1
  simp only [resampleMap, add_apply, sub_apply]
  push_cast
  ring

/-- The resampling kernel `ω ↦ resample G c (η ω)`. -/
def resampleKernel {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (c : DistOn upperHalfPlaneOpens)
    (η : Kernel Ω (DistOn upperHalfPlaneOpens)) : Kernel Ω (DistOn upperHalfPlaneOpens) :=
  (η ×ₖ Kernel.const Ω (zbLaw upperHalfPlaneOpens)).map (resampleMap G c)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem resampleKernel_apply (hGm : Measurable G) (c : DistOn upperHalfPlaneOpens)
    (η : Kernel Ω (DistOn upperHalfPlaneOpens)) [IsSFiniteKernel η] (ω : Ω) :
    resampleKernel G c η ω = resample G c (η ω) := by
  rw [resampleKernel, Kernel.map_apply _ (measurable_resampleMap hGm c), Kernel.prod_apply,
    Kernel.const_apply, resample]

theorem isMarkovKernel_resampleKernel (hGm : Measurable G) (c : DistOn upperHalfPlaneOpens)
    (η : Kernel Ω (DistOn upperHalfPlaneOpens)) [IsMarkovKernel η] :
    IsMarkovKernel (resampleKernel G c η) := by
  rw [resampleKernel]
  exact Kernel.IsMarkovKernel.map _ (measurable_resampleMap hGm c)

end Resample

/-! ### The three resampling facts -/

section Main

variable {V : Opens ℂ} {u₀ : ℂ → ℝ} {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}

/-- **Base case**: the time-zero field law `𝔥₀ + h⁰` is projection-independent at every open `V ⊆ ℍ`. -/
theorem isProjIndepMeasure_fieldLaw0 (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hVH : (V : Set ℂ) ⊆ H) :
    IsProjIndepMeasure V (fieldLaw0 u₀) := by
  intro f Ξ
  rw [fieldLaw0, integral_cexp_gaussLaw le_rfl subset_rfl, integral_cexp_gaussLaw le_rfl subset_rfl,
    map_add, show Distribution.ofFun upperHalfPlaneOpens u₀ volume ⊤ = meanH u₀ from rfl,
    meanH_apply_lapTest hu₀ hVH, zero_add,
    zeroGFFTestCov_eq_inner_covVec upperHalfPlaneOpens.isOpen subset_rfl,
    zeroGFFTestCov_eq_inner_covVec upperHalfPlaneOpens.isOpen subset_rfl, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq,
    norm_covVec_lapTest_add_sq upperHalfPlaneOpens.isOpen subset_rfl hVH, projFactor, ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable (hGm : Measurable G)
  (hGd : GFF.IsMarkovDecomposition V upperHalfPlaneOpens id G (zbLaw upperHalfPlaneOpens))
include hGm hGd

/-- **Resampling preserves the characteristic functional at `Ξ` under the shift rule at `Ξ`.** -/
theorem integral_cexp_resample_eq_of_shift (hVH : (V : Set ℂ) ⊆ H)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) {μ : Measure (DistOn upperHalfPlaneOpens)} [IsFiniteMeasure μ]
    (hμ : μ ≪ fieldLaw0 u₀) {Ξ : TestOn upperHalfPlaneOpens} (hshift : IsProjShiftMeasure V μ Ξ) :
    ∫ z, Complex.exp (Complex.I * (z Ξ : ℂ)) ∂resample G (meanH u₀) μ =
      ∫ x, Complex.exp (Complex.I * (x Ξ : ℂ)) ∂μ := by
  obtain ⟨f, hf, hae⟩ := exists_tendsto_ae_projMap hGm hGd hVH hu₀ Ξ
  have hc : Continuous fun t : ℝ => Complex.exp (Complex.I * (t : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  -- the shifted characteristic functionals converge to that of the harmonic part
  have hlim1 : Tendsto (fun n => ∫ x, Complex.exp (Complex.I * (x (Ξ - lapTest V (f n)) : ℂ)) ∂μ) atTop
      (𝓝 (∫ x, Complex.exp (Complex.I * ((x Ξ - G (x - meanH u₀) Ξ : ℝ) : ℂ)) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => (measurable_exp_I_mul (measurable_distOn_apply _)).aestronglyMeasurable)
      (integrable_const 1) (fun n => ae_of_all _ fun x => (Complex.norm_exp_I_mul_ofReal _).le) ?_
    filter_upwards [hae μ hμ] with x hx
    have e : ∀ n, x (Ξ - lapTest V (f n)) = x Ξ - x (lapTest V (f n)) := fun n => map_sub x _ _
    simp_rw [e]
    exact (hc.tendsto _).comp (tendsto_const_nhds.sub hx)
  -- and, by the shift rule, to `exp(‖covVec_V Ξ‖²/2)` times the characteristic functional
  have hlim2 : Tendsto (fun n => ∫ x, Complex.exp (Complex.I * (x (Ξ - lapTest V (f n)) : ℂ)) ∂μ) atTop
      (𝓝 (Complex.exp (((1 / 2) * ‖covVec (V : Set ℂ) Ξ‖ ^ 2 : ℝ) : ℂ) *
        ∫ x, Complex.exp (Complex.I * (x Ξ : ℂ)) ∂μ)) := by
    simp_rw [hshift (f _)]
    refine Tendsto.mul_const _ ?_
    have h1 : Tendsto (fun n => -(1 / 2) * ‖gradFeat (V : Set ℂ) (f n).1‖ ^ 2 +
        ⟪gradFeat (V : Set ℂ) (f n).1, covVec (V : Set ℂ) Ξ⟫) atTop
        (𝓝 (-(1 / 2) * ‖covVec (V : Set ℂ) Ξ‖ ^ 2 + ⟪covVec (V : Set ℂ) Ξ, covVec (V : Set ℂ) Ξ⟫)) :=
      ((hf.norm.pow 2).const_mul _).add (hf.inner tendsto_const_nhds)
    rw [real_inner_self_eq_norm_sq] at h1
    have h2 : -(1 / 2) * ‖covVec (V : Set ℂ) Ξ‖ ^ 2 + ‖covVec (V : Set ℂ) Ξ‖ ^ 2 =
        (1 / 2) * ‖covVec (V : Set ℂ) Ξ‖ ^ 2 := by ring
    rw [h2] at h1
    exact (Complex.continuous_exp.comp Complex.continuous_ofReal).continuousAt.tendsto.comp h1
  have heq := tendsto_nhds_unique hlim1 hlim2
  rw [integral_cexp_resample hGm, heq, integral_cexp_markovMap hGm hGd hVH, Complex.ofReal_exp,
    mul_comm, ← mul_assoc, ← Complex.exp_add]
  have h0 : ((-(1 / 2) * ‖covVec (V : Set ℂ) Ξ‖ ^ 2 : ℝ) : ℂ) +
      (((1 / 2) * ‖covVec (V : Set ℂ) Ξ‖ ^ 2 : ℝ) : ℂ) = 0 := by push_cast; ring
  rw [h0, Complex.exp_zero, one_mul]

/-- **Resampling a projection-independent law changes nothing.** -/
theorem resample_eq_of_isProjIndepMeasure (hVH : (V : Set ℂ) ⊆ H)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) {μ : Measure (DistOn upperHalfPlaneOpens)} [IsFiniteMeasure μ]
    (hμ : μ ≪ fieldLaw0 u₀) (h : IsProjIndepMeasure V μ) : resample G (meanH u₀) μ = μ :=
  ext_of_integral_cexp fun Ξ =>
    integral_cexp_resample_eq_of_shift hGm hGd hVH hu₀ hμ (h.isProjShiftMeasure hVH Ξ)

/-- **Every resampled law is projection-independent at `V`.** -/
theorem isProjIndepMeasure_resample (hVH : (V : Set ℂ) ⊆ H)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) {μ : Measure (DistOn upperHalfPlaneOpens)} [IsFiniteMeasure μ]
    (hμ : μ ≪ fieldLaw0 u₀) : IsProjIndepMeasure V (resample G (meanH u₀) μ) := by
  intro f Ξ
  rw [integral_cexp_resample hGm, integral_cexp_resample hGm, integral_cexp_markovMap hGm hGd hVH,
    integral_cexp_markovMap hGm hGd hVH]
  have h1 : ∫ x, Complex.exp (Complex.I * ((x (lapTest V f + Ξ) - G (x - meanH u₀) (lapTest V f + Ξ) : ℝ) : ℂ))
      ∂μ = ∫ x, Complex.exp (Complex.I * ((x Ξ - G (x - meanH u₀) Ξ : ℝ) : ℂ)) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_apply_lapTest_eq_projMap hGm hGd hVH hu₀ f hμ] with x hx
    rw [map_add x, map_add (G (x - meanH u₀)), hx]
    congr 3
    ring
  rw [h1, norm_covVec_lapTest_add_sq V.isOpen hVH subset_rfl, projFactor, Complex.ofReal_exp,
    Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Main

/-! ### Resampling kernels and integrated laws -/

section KernelLevel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}

/-- The integrated law of the resampling kernel is the resampling of the integrated law. -/
theorem secMeas_resampleKernel (hGm : Measurable G) (c : DistOn upperHalfPlaneOpens)
    (η : Kernel Ω (DistOn upperHalfPlaneOpens)) [IsMarkovKernel η] {A : Set Ω} (hA : MeasurableSet A) :
    secMeas P A (resampleKernel G c η) = resample G c (secMeas P A η) := by
  have := isMarkovKernel_resampleKernel hGm c η
  have hR := measurable_resampleMap hGm c
  ext B hB
  have hRB : MeasurableSet (resampleMap G c ⁻¹' B) := hR hB
  rw [secMeas_apply hA hB, Measure.compProd_apply_prod hA hB, resample, Measure.map_apply hR hB,
    Measure.prod_apply hRB, lintegral_secMeas (measurable_measure_prodMk_left hRB)]
  refine setLIntegral_congr_fun hA fun ω _ => ?_
  rw [resampleKernel_apply hGm, resample, Measure.map_apply hR hB, Measure.prod_apply hRB]

end KernelLevel

end Coupling

end InteractingSLE
