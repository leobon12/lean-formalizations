import InteractingSLE.Spec.Coupling.TestMean
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import InteractingSLE.GFF.LocalSets.GreenBound
import LQGMetric.Field.ZeroBoundaryLaw

/-!
# Lemma 3.11: one stopping time, one test function

Packet PROVE-T11-L311 (Specification §3.3, `source/spec/p049-096.md#lem-3.11`, L569–L586; graph node
`SPEC.lem-3.11`). Fix `U ⋐ ℍ` and a finite stopping time `τ < τ_U ∧ T_*`. The field `h_{U,τ}` is sampled by taking
the driving history up to `τ`, a zero-boundary GFF `h⁰` on `ℍ ∖ K_τ`, and restricting `𝔥_τ + h⁰` to `U`. For a test
function `φ` supported in `U` this means: conditionally on `𝓕_τ`, the pairing `(h_{U,τ}, φ)` is Gaussian with mean
`(𝔥_τ, φ)` and variance `E_τ(φ)` (the frozen `loewnerGreenEnergy`, the variance of `(h⁰ ∘ f_τ, φ)`; this is the form
in which the frozen `IsOptionalHullCoupling` states the conditional law). The lemma: `(h_{U,τ}, φ) =d (h, φ)` with
`h = h̃ + 𝔥₀`, `h̃` a zero-boundary GFF on `ℍ`.

Here the stopping time is a *protected* stop `σ` of the null-augmented filtration (`IsTestProtected`: `supp φ` stays
at height `≥ δ` up to `σ`, coordinates bounded, `σ ≤ N`); the source's proof uses exactly this ("Optional stopping
at these protected-domain stops is therefore valid", L552). The passage from protected stops to an arbitrary
`τ < τ_U ∧ T_*` is the localization recorded in the handoff.

## Main results

* `greenEnergy0_eq_zeroGFFTestCov`: `E₀(φ) = ∬ φ G_ℍ φ` is the variance `‖φ‖²_{H⁻¹(ℍ)}` of the zero-boundary GFF;
* `map_eval_eq_gaussianReal_of_isZBGFFProcess`: for `h` with `h − 𝔥₀` a zero-boundary GFF on `ℍ` (the frozen
  form), `(h, φ) ∼ N((𝔥₀, φ), ‖φ‖²_{H⁻¹(ℍ)})`;
* **`map_eq_gaussianReal_of_condExp_testMean`** (Lemma 3.11, protected stops): a variable `Y` whose conditional
  characteristic function given `𝓕_σ` is `exp(iθ (𝔥_σ, φ) − θ² E_σ(φ)/2)` has the law `N((𝔥₀, φ), ‖φ‖²_{H⁻¹(ℍ)})`;
* `map_eq_map_eval_of_condExp_testMean`: hence `Y =d (h, φ)` for every such `h` on any probability space.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

open Ito

/-- A compactly supported function with support in `ℍ` vanishes below some positive height. -/
theorem exists_pos_forall_im_lt {φ : ℂ → ℝ} (hφs : HasCompactSupport φ) (hφH : tsupport φ ⊆ H) :
    ∃ δ > 0, ∀ a : ℂ, a.im < δ → φ a = 0 := by
  rcases (tsupport φ).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun a _ => eq_zero_of_notMem_tsupport' (by rw [he]; exact notMem_empty a)⟩
  · obtain ⟨z₀, hz₀, hmin⟩ := hφs.isCompact.exists_isMinOn hne Complex.continuous_im.continuousOn
    refine ⟨z₀.im, hφH hz₀, fun a ha => eq_zero_of_notMem_tsupport' fun h => ?_⟩
    exact absurd (hmin h) (not_le.2 ha)

/-- `E₀(φ) = ∬ φ(y) G_ℍ(y, z) φ(z)` is the dual Dirichlet norm `‖φ‖²_{H⁻¹(ℍ)}` (the covariance of the zero-boundary
GFF on `ℍ`, LQGMetric's Green representation). -/
theorem greenEnergy0_eq_zeroGFFTestCov (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    greenEnergy0 φ = zeroGFFTestCov upperHalfPlaneOpens φ φ := by
  have hφc : Continuous φ := φ.continuous
  have hφs : HasCompactSupport φ := φ.hasCompactSupport
  have hφH : tsupport φ ⊆ H := φ.tsupport_subset
  obtain ⟨δ, hδ, hρδ⟩ := exists_pos_forall_im_lt hφs hφH
  have hg := LQGMetric.zeroGFFTestCov_eq_green (V := upperHalfPlaneOpens) subset_rfl
    GFF.isConformalOnto_id_H φ φ
  simp only [id] at hg
  rw [hg, greenEnergy0]
  have hint : Integrable (fun p : ℂ × ℂ => φ p.1 * greenH p.1 p.2 * φ p.2)
      ((volume : Measure ℂ).prod volume) := by
    refine Integrable.mono' (FieldMart.integrable_rho_rho_greenH hφc hφs hδ hρδ)
      ((((hφc.measurable.comp measurable_fst).mul measurable_greenH).mul
        (hφc.measurable.comp measurable_snd)).aestronglyMeasurable) ?_
    filter_upwards [FieldMart.ae_ne_diag] with p hp
    by_cases h1 : p.1 ∈ tsupport φ
    · by_cases h2 : p.2 ∈ tsupport φ
      · have g0 : 0 ≤ greenH p.1 p.2 := greenH_nonneg (show (0 : ℝ) ≤ p.1.im from (hφH h1).le)
          (show (0 : ℝ) ≤ p.2.im from (hφH h2).le) hp
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg g0]
        exact le_of_eq (by ring)
      · simp [eq_zero_of_notMem_tsupport' h2]
    · simp [eq_zero_of_notMem_tsupport' h1]
  rw [← integral_prod _ hint]
  congr 1; funext p; ring

/-- The one-dimensional law of `h = h̃ + 𝔥₀` (frozen form: `h − 𝔥₀` is a zero-boundary GFF process on `ℍ`):
`(h, φ) ∼ N((𝔥₀, φ), ‖φ‖²_{H⁻¹(ℍ)})`. -/
theorem map_eval_eq_gaussianReal_of_isZBGFFProcess {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {h : Ω' → LQGMetric.DistOn upperHalfPlaneOpens}
    {u₀ : ℂ → ℝ}
    (hh : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P')
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    P'.map (fun ω => h ω φ) =
      gaussianReal (∫ z, u₀ z * φ z) (zeroGFFTestCov upperHalfPlaneOpens φ φ).toNNReal := by
  set m : ℝ := ∫ z, u₀ z * φ z
  have hG : HasGaussianLaw (fun ω => h ω φ - m) P' := hh.gaussian.hasGaussianLaw_eval φ
  have hvar : Var[fun ω => h ω φ - m; P'] = zeroGFFTestCov upperHalfPlaneOpens φ φ := by
    rw [← covariance_self hG.aemeasurable]; exact hh.covariance_eq φ φ
  have hmap := hG.map_eq_gaussianReal
  rw [hh.centered φ, hvar] at hmap
  have e : (fun ω => h ω φ) = (fun x => x + m) ∘ fun ω => h ω φ - m := by
    funext ω; simp
  rw [e, ← Measure.map_map (measurable_add_const m) (hh.measurable φ), hmap,
    gaussianReal_map_add_const, zero_add]

section Lemma311

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {σ : Ω → ℝ≥0} {δ R N : ℝ}

/-- **Lemma 3.11 at a protected stop.** Let `(W, V, B, ζ)` be an integrated `SLE_κ(ρ)` evolution, `φ` a test
function on `ℍ`, and `σ` a stopping time of the null-augmented filtration protecting `supp φ`. If, conditionally on
`𝓕_σ`, `Y` is Gaussian with mean `(𝔥_σ, φ)` and variance `E_σ(φ)` (the sampled field `𝔥_σ + h⁰ ∘ f_σ` tested
against `φ`), then `Y ∼ N((𝔥₀, φ), ‖φ‖²_{H⁻¹(ℍ)})`, the law of `(h̃ + 𝔥₀, φ)`. -/
theorem map_eq_gaussianReal_of_condExp_testMean
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens)
    (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hσp : ∀ᵐ ω ∂P, IsTestProtected W VL VR B ζ φ σ δ R N ω) (hδ : 0 < δ)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {Y : Ω → ℝ} (hY : Measurable Y)
    (hcond : ∀ θ : ℝ, P[fun ω => Complex.exp (Complex.I * θ * Y ω) | hσ.measurableSpace] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * θ *
        ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (σ ω) (u ω (σ ω)) z * φ z : ℝ) : ℂ) -
        θ ^ 2 * ((loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (σ ω) φ : ℝ) : ℂ) / 2)) :
    P.map Y = gaussianReal (∫ z, u₀ z * φ z) (zeroGFFTestCov upperHalfPlaneOpens φ φ).toNNReal := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hnn : 0 ≤ zeroGFFTestCov upperHalfPlaneOpens φ φ :=
    LQGMetric.zeroGFFTestCov_self_nonneg (LQGMetric.zbAdmissible_of_subset_H subset_rfl) φ
  refine map_eq_gaussianReal_of_condExp hσ.measurableSpace_le hY hcond fun θ => ?_
  rw [integral_cexp_testMean_stopped hE hκ hσ hσp φ.tsupport_subset φ.continuous φ.hasCompactSupport
    hδ u hu hu₀ θ, greenEnergy0_eq_zeroGFFTestCov, Real.coe_toNNReal _ hnn]

/-- **Lemma 3.11 at a protected stop, as an equality in law**: `Y =d (h, φ)` for every `h` with `h − 𝔥₀` a
zero-boundary GFF on `ℍ` (on any probability space). -/
theorem map_eq_map_eval_of_condExp_testMean
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens)
    (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hσp : ∀ᵐ ω ∂P, IsTestProtected W VL VR B ζ φ σ δ R N ω) (hδ : 0 < δ)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {Y : Ω → ℝ} (hY : Measurable Y)
    (hcond : ∀ θ : ℝ, P[fun ω => Complex.exp (Complex.I * θ * Y ω) | hσ.measurableSpace] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * θ *
        ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (σ ω) (u ω (σ ω)) z * φ z : ℝ) : ℂ) -
        θ ^ 2 * ((loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (σ ω) φ : ℝ) : ℂ) / 2))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h : Ω' → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P') :
    P.map Y = P'.map (fun ω => h ω φ) := by
  rw [map_eq_gaussianReal_of_condExp_testMean hE hκ φ hσ hσp hδ u hu hu₀ hY hcond,
    map_eval_eq_gaussianReal_of_isZBGFFProcess hh φ]

end Lemma311

end Coupling

end InteractingSLE
