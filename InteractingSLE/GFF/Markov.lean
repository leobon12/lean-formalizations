import SupercriticalConformalCovariance.Markov.MarkovTheorem
import LQGMetric.Field.ExistGFF
import LQGMetric.Field.ZeroBoundaryLaw
import LQGMetric.Field.StandardBorelRange
import Mathlib.Probability.ConditionalExpectation

/-!
# The Markov property of the zero-boundary GFF (specification Proposition 3.1)

Source: `source/ig1-specification.pdf`, §3.1, Proposition 3.1 (p. 42; transcription
`source/spec/p001-048.md#prop-3.1`): for open `U ⊆ D`, `h = h_U + h_{U^c}` with `h_U`, `h_{U^c}`
independent distributions on `D`, `h_U` a zero-boundary GFF on `U` that is zero on `D \ U`, and
`h_{U^c}` harmonic on `U`; that is, the conditional law of `h|_U` given `h|_{D∖U}` is that of a GFF
on `U` plus the harmonic extension.

Carriers: fields are `LQGMetric.DistOn D = 𝒟'(D)` (cylinder σ-algebra); the zero-boundary GFF is
`LQGMetric.IsZeroBoundaryGFF D` (covariance `QuantumZipper.zeroGFFTestCov D`, Dirichlet
normalization `(2π)⁻¹∫∇f·∇g`); `D` is any open set with `LQGMetric.ZBAdmissible D` (every test
function has finite `H⁻¹(D)` norm), which holds for `D ⊆ ℍ` (`LQGMetric.zbAdmissible_of_subset_H`).

## Main results

* `IsZBGFFExtOn U D X P` : `X` has the law of the zero-boundary GFF on `U` extended by zero to `D`;
* `IsMarkovDecomposition U D h hU P` : `h = hU + (h − hU)` is the decomposition of Proposition 3.1;
* `exists_markovMap` : for `U ≤ D` with `ZBAdmissible D` there is one Borel map
  `G : 𝒟'(D) → 𝒟'(D)` such that every zero-boundary GFF `h` on `D`, on any probability space,
  satisfies `IsMarkovDecomposition U D h (G ∘ h)`;
* `exists_markovMap_of_subset_H`, `exists_markovMap_upperHalfPlane` : `D ⊆ ℍ` and `D = ℍ`;
* `IsMarkovDecomposition.condExp_exp_zbPart`, `IsMarkovDecomposition.condExp_exp_field`,
  `IsMarkovDecomposition.map_pair_eq` : the conditional-law (kernel) forms.

## Route (transfer along laws; own argument from library results)

The whole-plane Markov property is proved in the host libraries (SupercriticalConformalCovariance
`exists_measurable_zeroExtension_map`; LQGMetric `MarkovZB`, `MarkovExt`, `MarkovHarm`): for a
whole-plane GFF `h` and admissible `V`, the zero-boundary part `h̊^V` is the image of `h` under the
Cameron–Martin isometry of `H₀¹(V)` (Miller–Sheffield IG4 Prop. 2.8; Sheffield math/0312099
Thm 2.17; Berestycki–Powell arXiv:2404.16642 Thm 1.52). Take `V = D` and `V = U`:
1. `A = h̊^D|_D` is a zero-boundary GFF on `D` (SCC);
2. `h̊^U` is almost surely a Borel function `G` of `A` (`exists_markovMap_of_wholePlane`): its
   pairings are `L²` limits of the Dirichlet pairings `(h, f)_∇ = ⟨A, −Δf/2π⟩`, `f ∈ C_c^∞(U)`;
   countably many pairings determine a distribution (`LQGMetric.measurableEmbedding_pairJ`);
   Doob–Dynkin (`Measurable.exists_eq_measurable_comp`);
3. for this model pair, `G(A)` has the extended zero-boundary law, `A − G(A)` annihilates
   `Δ C_c^∞(U)`, and `G(A)`, `A − G(A)` are independent: both lie in the Gaussian space of `h` and
   are orthogonal, `H₀¹(U) ⟂ H₀¹(D) ⊖ H₀¹(U)` (`inner_cmIso_extVec_sub`);
4. these are properties of the law of `A`, which is the law of every zero-boundary GFF on `D`
   (`LQGMetric.IsZeroBoundaryGFF.map_eq`), so they hold for `(h, G(h))`; Weyl's lemma
   (`LQGMetric.MarkovWeyl3.exists_harmonic_of_laplacian_eq_zero`) gives the harmonic function.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped RealInnerProductSpace

namespace InteractingSLE
namespace GFF

open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovExt LQGMetric.MarkovHarm LQGMetric.MarkovGauss
  LQGMetric.MarkovGerm LQGMetric.MarkovAsm QuantumZipper QuantumZipper.K3

/-! ### Inclusions and restrictions between open sets -/

/-- The inclusion `𝓓(U) ⊆ 𝓓(D)` of test functions (Mathlib's `monoCLM`; the identity on
functions when `U ≤ D`). -/
abbrev testIncl (U D : Opens ℂ) : TestOn U →L[ℝ] TestOn D :=
  TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := D)

lemma coe_testIncl {U D : Opens ℂ} (hUD : U ≤ D) (φ : TestOn U) :
    ((testIncl U D φ : TestOn D) : ℂ → ℝ) = φ := by
  simp [testIncl, TestFunction.monoCLM_apply, hUD]

/-- The restriction `T|_U ∈ 𝒟'(U)` of `T ∈ 𝒟'(D)` (meaningful for `U ≤ D`). -/
def restrictDist (U : Opens ℂ) {D : Opens ℂ} (T : DistOn D) : DistOn U :=
  T.comp (testIncl U D)

lemma restrictDist_apply (U : Opens ℂ) {D : Opens ℂ} (T : DistOn D) (φ : TestOn U) :
    restrictDist U T φ = T (testIncl U D φ) := rfl

theorem measurable_restrictDist (U : Opens ℂ) {D : Opens ℂ} :
    Measurable (restrictDist U (D := D)) :=
  measurable_distOn_iff.2 fun _ => measurable_distOn_apply _

lemma testIncl_testIncl {U D : Opens ℂ} (hUD : U ≤ D) (φ : TestOn U) :
    extC D (testIncl U D φ) = extC U φ := by
  ext x
  rw [coe_extC, coe_extC, coe_testIncl hUD]

lemma restrictDist_restrictTo {U D : Opens ℂ} (hUD : U ≤ D) (T : DistC) :
    restrictDist U (restrictTo D T) = restrictTo U T := by
  ext φ
  change T (extC D (testIncl U D φ)) = T (extC U φ)
  rw [testIncl_testIncl hUD]

lemma restrictTo_apply (D : Opens ℂ) (T : DistC) (φ : TestOn D) :
    restrictTo D T φ = T (extC D φ) := rfl

/-- Admissibility passes to open subsets. -/
theorem zbAdmissible_mono {U D : Opens ℂ} (hUD : U ≤ D) (hD : ZBAdmissible D) :
    ZBAdmissible U := by
  intro φ
  obtain ⟨h1, h2⟩ := hD (testIncl U D φ)
  rw [coe_testIncl hUD] at h1 h2
  exact ⟨⟨h1.1, ⟨_, φ.hasCompactSupport.isCompact, φ.tsupport_subset.trans subset_closure,
      testMeasPos_compl_tsupport φ⟩,
      (dualNormSq_zeroSpace_mono U.isOpen hUD).trans_lt h1.2.2⟩,
    ⟨h2.1, ⟨_, φ.hasCompactSupport.isCompact, φ.tsupport_subset.trans subset_closure,
      testMeasNeg_compl_tsupport φ⟩,
      (dualNormSq_zeroSpace_mono U.isOpen hUD).trans_lt h2.2.2⟩⟩

/-! ### The zero-boundary parts of a whole-plane GFF on `U ⊆ D` -/

section WholePlane

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- `f ∈ C_c^∞(U)` as an element of `C_c^∞(D)`, `U ⊆ D`. -/
def zsSubIncl {U D : Set ℂ} (hUD : U ⊆ D) (f : zsSub U) : zsSub D :=
  ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.trans hUD⟩

/-- A distribution version of the zero-boundary part of `h` on `D` has the same Dirichlet
pairings `(h, f)_∇ = ⟨h, −Δf/(2π)⟩` as `h` for `f ∈ C_c^∞(U)`, `U ⊆ D`. -/
theorem ae_version_cmTest_eq (hh : IsWholePlaneGFF h P) {U D : Opens ℂ} (hUD : U ≤ D)
    (hD : ZBAdmissible D) {hz : Ω → DistC}
    (hzae : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh D φ) (f : zsSub (U : Set ℂ)) :
    (fun ω => hz ω (cmTest (zsTest f.2))) =ᵐ[P] fun ω => h ω (cmTest (zsTest f.2)) := by
  set f' : zsSub (D : Set ℂ) := zsSubIncl hUD f
  have e : extC D (cmTestOn f') = cmTest (zsTest f.2) := extC_cmTestOn f'
  filter_upwards [hzae (extC D (cmTestOn f')), zbExt_ae_eq_zbProc hh (cmTestOn f'),
    zbProc_cmTestOn_ae hh hD f'] with ω h1 h2 h3
  calc hz ω (cmTest (zsTest f.2)) = hz ω (extC D (cmTestOn f')) := by rw [e]
    _ = zbExt hh D (extC D (cmTestOn f')) ω := h1
    _ = zbProc hh (cmTestOn f') ω := h2
    _ = h ω (cmTest (zsTest f.2)) := h3

end WholePlane

/-- The Cameron–Martin image of `H₀¹(U)` consists of `m`-measurable classes whenever the
Dirichlet pairings `(h, f)_∇`, `f ∈ C_c^∞(U)`, are `m`-measurable. -/
theorem cmIso_mem_lpMeas {Ω : Type} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (U : Opens ℂ) (hm : m ≤ mΩ)
    (hf : ∀ f : zsSub (U : Set ℂ),
      AEStronglyMeasurable[m] (fun ω => h ω (cmTest (zsTest f.2))) P)
    (v : gradClosure (U : Set ℂ) (zeroSpace U)) : cmIso hh U v ∈ lpMeas ℝ ℝ m 2 P := by
  refine (denseRange_gradLin U).induction_on v ?_ fun f => ?_
  · exact (isClosed_aestronglyMeasurable hm).preimage (cmIso hh U).continuous
  · rw [cmIso_gradLin, mem_lpMeas_iff_aestronglyMeasurable]
    simp only [cmLin, LinearMap.coe_mk, AddHom.coe_mk]
    exact (hf f).congr (memLp_pair hh (cmTest0 (zsTest f.2))).coeFn_toLp.symm

/-- An `m`-measurable version of the extension by zero of the zero-boundary part on `U`. -/
theorem exists_measurable_version_zbExt {Ω : Type} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (U : Opens ℂ) (hm : m ≤ mΩ)
    (hf : ∀ f : zsSub (U : Set ℂ),
      AEStronglyMeasurable[m] (fun ω => h ω (cmTest (zsTest f.2))) P) (φ : TestC) :
    ∃ Y : Ω → ℝ, Measurable[m] Y ∧ zbExt hh U φ =ᵐ[P] Y := by
  have hmem := cmIso_mem_lpMeas hh U hm hf
    ⟨rieszFun U ((U : Set ℂ).indicator φ), rieszFun_mem U _⟩
  obtain ⟨g, hg, hge⟩ := mem_lpMeas_iff_aestronglyMeasurable.1 hmem
  exact ⟨g, hg.measurable, (zbExt_ae hh U φ).trans hge⟩

/-! The next results carry a second σ-algebra `m`; it is bound before the ambient one so
that the ambient `mΩ` stays the instance. -/

/-- A random distribution whose pairings have `m`-measurable versions has an `m`-measurable
version (`𝒟'(ℂ)` embeds measurably into `ℝ^J`, `J` countable). -/
theorem exists_measurable_dist_version {Ω : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace Ω] {P : Measure Ω} (hz : Ω → DistC)
    (hY : ∀ φ : TestC, ∃ Y : Ω → ℝ, Measurable[m] Y ∧ (fun ω => hz ω φ) =ᵐ[P] Y) :
    ∃ B : Ω → DistC, Measurable[m] B ∧ B =ᵐ[P] hz := by
  choose Y hYm hYe using fun c : CoordJ => hY (comb ⊤ c)
  obtain ⟨Ψ, hΨm, hΨ⟩ := (measurableEmbedding_pairJ ⊤).exists_measurable_extend measurable_id
    (fun _ => ⟨0⟩)
  have hYm' : Measurable[m] (fun ω c => Y c ω) := by
    let _ := m
    exact measurable_pi_iff.2 hYm
  refine ⟨fun ω => Ψ (fun c => Y c ω), hΨm.comp hYm', ?_⟩
  filter_upwards [ae_all_iff.2 hYe] with ω hω
  have : (fun c => Y c ω) = pairJ ⊤ (hz ω) := funext fun c => (hω c).symm
  rw [this]
  exact congrFun hΨ (hz ω)

section MarkovMap

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- **The Markov map, built from a whole-plane GFF.** Let `hzD`, `hzU` be distribution versions
of the zero-boundary parts of a whole-plane GFF on `D` and on `U ≤ D` (SCC). Then the restriction
of `hzU` to `D` is almost surely a fixed Borel function `G` of the restriction of `hzD` to `D`. -/
theorem exists_markovMap_of_wholePlane (hh : IsWholePlaneGFF h P) {U D : Opens ℂ}
    (hUD : U ≤ D) (hD : ZBAdmissible D) :
    ∃ (hzD hzU : Ω → DistC) (G : DistOn D → DistOn D),
      Measurable hzD ∧ (∀ φ : TestC, (fun ω => hzD ω φ) =ᵐ[P] zbExt hh D φ) ∧
      Measurable hzU ∧ (∀ φ : TestC, (fun ω => hzU ω φ) =ᵐ[P] zbExt hh U φ) ∧
      Measurable G ∧
      (fun ω => G (restrictTo D (hzD ω))) =ᵐ[P] fun ω => restrictTo D (hzU ω) := by
  have hU : ZBAdmissible U := zbAdmissible_mono hUD hD
  obtain ⟨FD, hFDm, hFDae, -⟩ :=
    SupercriticalConformalCovariance.Markov.exists_measurable_zeroExtension_map hh hD
  obtain ⟨FU, hFUm, hFUae, -⟩ :=
    SupercriticalConformalCovariance.Markov.exists_measurable_zeroExtension_map hh hU
  let A : Ω → DistOn D := fun ω => restrictTo D (FD (h ω))
  have hAm : Measurable A := (measurable_restrictTo D).comp (hFDm.comp hh.measurable)
  have hm : MeasurableSpace.comap A inferInstance ≤ mΩ := hAm.comap_le
  have hf : ∀ f : zsSub (U : Set ℂ), AEStronglyMeasurable[MeasurableSpace.comap A inferInstance]
      (fun ω => h ω (cmTest (zsTest f.2))) P := by
    intro f
    have hmeas : Measurable[MeasurableSpace.comap A inferInstance]
        (fun ω => A ω (cmTestOn (zsSubIncl hUD f))) :=
      (measurable_distOn_apply _).comp (comap_measurable A)
    refine ⟨_, hmeas.stronglyMeasurable, ?_⟩
    filter_upwards [ae_version_cmTest_eq hh hUD hD hFDae f] with ω hω
    rw [← hω]
    change _ = FD (h ω) (extC D (cmTestOn (zsSubIncl hUD f)))
    rw [extC_cmTestOn]
    rfl
  obtain ⟨B, hBm, hBe⟩ := exists_measurable_dist_version (P := P)
    (m := MeasurableSpace.comap A inferInstance) (fun ω => FU (h ω)) fun φ => by
      obtain ⟨Y, hY, hYe⟩ := exists_measurable_version_zbExt hh U hm hf φ
      exact ⟨Y, hY, (hFUae φ).trans hYe⟩
  obtain ⟨G₀, hG₀m, hG₀⟩ := hBm.exists_eq_measurable_comp
  refine ⟨fun ω => FD (h ω), fun ω => FU (h ω), fun T => restrictTo D (G₀ T),
    hFDm.comp hh.measurable, hFDae, hFUm.comp hh.measurable, hFUae,
    (measurable_restrictTo D).comp hG₀m, ?_⟩
  filter_upwards [hBe] with ω hω
  change restrictTo D (G₀ (A ω)) = restrictTo D (FU (h ω))
  rw [← hω, hG₀]
  rfl

end MarkovMap

/-- Covariance only depends on the almost-everywhere classes. -/
lemma covariance_congr_of_ae_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') : cov[X, Y; μ] = cov[X', Y'; μ] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω h1 h2
  rw [h1, h2]

/-- `X : Ω → 𝒟'(D)` has the law of the zero-boundary GFF on `U ⊆ D` extended by zero to `D`
(specification Proposition 3.1: "`h_U` has the law of a zero boundary GFF on `U` and is zero on
`D \ U`"): its pairings with `𝓓(D)` form a centred Gaussian process with covariance
`⟨1_U φ, 1_U ψ⟩_{H⁻¹(U)}` (QZ's dual Dirichlet form, normalization `(2π)⁻¹∫∇f·∇g`). -/
structure IsZBGFFExtOn {Ω : Type*} [MeasurableSpace Ω] (U D : Opens ℂ) (X : Ω → DistOn D)
    (P : Measure Ω) : Prop where
  /-- `X` is a random distribution. -/
  measurable : Measurable X
  /-- Its pairings form a Gaussian process. -/
  gaussian : IsGaussianProcess (fun (φ : TestOn D) ω => X ω φ) P
  /-- It is centred. -/
  centered : ∀ φ : TestOn D, ∫ ω, X ω φ ∂P = 0
  /-- Its covariance is the `H⁻¹(U)` form of the restrictions to `U`. -/
  covariance_eq : ∀ φ ψ : TestOn D, cov[fun ω => X ω φ, fun ω => X ω ψ; P] =
    zeroGFFTestCov U ((U : Set ℂ).indicator φ) ((U : Set ℂ).indicator ψ)

section Model

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- The two Cameron–Martin images are compatible: `(h, f)_∇` for `f ∈ C_c^∞(U)`, `U ⊆ D`. -/
lemma cmIso_gradLin_incl (hh : IsWholePlaneGFF h P) {U D : Opens ℂ} (hUD : U ≤ D)
    (f : zsSub (U : Set ℂ)) :
    cmIso hh U (gradLin U f) = cmIso hh D (gradLin D (zsSubIncl hUD f)) := by
  rw [cmIso_gradLin, cmIso_gradLin]
  rfl

lemma dirichletEnergyOn_incl {U D : Opens ℂ} (hUD : U ≤ D) (f : zsSub (U : Set ℂ)) :
    dirichletEnergyOn D (zsSubIncl hUD f).1 = dirichletEnergyOn U f.1 := by
  rw [← gradEnergy_eq_dirichletEnergyOn D (zsSubIncl hUD f).2,
    ← gradEnergy_eq_dirichletEnergyOn U f.2]
  rfl

/-- **Orthogonality of the two parts.** The Cameron–Martin image of `H₀¹(U)` is orthogonal to
`⟨h̊^D, 1_D ψ⟩ − ⟨h̊^U, 1_U ψ⟩` (the projection of the field onto `H₀¹(D) ⊖ H₀¹(U)`). -/
theorem inner_cmIso_extVec_sub (hh : IsWholePlaneGFF h P) {U D : Opens ℂ} (hUD : U ≤ D)
    (hD : ZBAdmissible D) (v : gradClosure (U : Set ℂ) (zeroSpace U)) (ψ : TestC) :
    ⟪cmIso hh U v, extVec hh D ((D : Set ℂ).indicator ψ) -
      extVec hh U ((U : Set ℂ).indicator ψ)⟫ = 0 := by
  have hU : ZBAdmissible U := zbAdmissible_mono hUD hD
  refine (denseRange_gradLin U).induction_on v
    (isClosed_eq (continuous_inner.comp ((cmIso hh U).continuous.prodMk continuous_const))
      continuous_const) fun f => ?_
  by_cases hpos : 0 < dirichletEnergyOn U f.1
  · have hposU : ∃ g ∈ zeroSpace (U : Set ℂ), 0 < dirichletEnergyOn U g := ⟨f.1, f.2, hpos⟩
    have hposD : ∃ g ∈ zeroSpace (D : Set ℂ), 0 < dirichletEnergyOn D g :=
      ⟨(zsSubIncl hUD f).1, (zsSubIncl hUD f).2, by rw [dirichletEnergyOn_incl]; exact hpos⟩
    have e1 : ⟪cmIso hh U (gradLin U f), extVec hh D ((D : Set ℂ).indicator ψ)⟫ =
        ∫ x, ψ x * f.1 x := by
      rw [cmIso_gradLin_incl hh hUD, extVec, LinearIsometry.inner_map_map, Submodule.coe_inner,
        real_inner_comm]
      exact SupercriticalConformalCovariance.Markov.inner_rieszFun_indicator_gradFeat hh hD
        hposD ψ (zsSubIncl hUD f).2
    have e2 : ⟪cmIso hh U (gradLin U f), extVec hh U ((U : Set ℂ).indicator ψ)⟫ =
        ∫ x, ψ x * f.1 x := by
      rw [extVec, LinearIsometry.inner_map_map, Submodule.coe_inner, real_inner_comm]
      exact SupercriticalConformalCovariance.Markov.inner_rieszFun_indicator_gradFeat hh hU
        hposU ψ f.2
    rw [inner_sub_right, e1, e2, sub_self]
  · have hn : ‖gradLin U f‖ ^ 2 = dirichletEnergyOn U f.1 :=
      norm_gradFeat_sq ((isDNSpace_zeroSpace _).smooth f f.2)
        ((isDNSpace_zeroSpace _).energy f f.2)
    have hle : ‖gradLin U f‖ ^ 2 ≤ 0 := hn ▸ not_lt.1 hpos
    have h0 : gradLin U f = 0 :=
      norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm hle (sq_nonneg _)))
    rw [h0, map_zero, inner_zero_left]

/-- The independence of the two parts, at the level of pairing processes. -/
theorem indepFun_zbExt_sub (hh : IsWholePlaneGFF h P) {U D : Opens ℂ} (hUD : U ≤ D)
    (hD : ZBAdmissible D) :
    IndepFun (fun ω (φ : TestOn D) => zbExt hh U (extC D φ) ω)
      (fun ω (ψ : TestOn D) => zbExt hh D (extC D ψ) ω - zbExt hh U (extC D ψ) ω) P := by
  let W₁ : TestOn D → Lp ℝ 2 P := fun φ => extVec hh U ((U : Set ℂ).indicator (extC D φ))
  let W₂ : TestOn D → Lp ℝ 2 P := fun ψ =>
    extVec hh D ((D : Set ℂ).indicator (extC D ψ)) - extVec hh U ((U : Set ℂ).indicator (extC D ψ))
  have hW₁ : ∀ φ, W₁ φ ∈ gaussSpace (pairProc h) (memLp_pair hh) := fun φ =>
    extVec_mem_gaussSpace hh U _
  have hW₂ : ∀ ψ, W₂ ψ ∈ gaussSpace (pairProc h) (memLp_pair hh) := fun ψ =>
    Submodule.sub_mem _ (extVec_mem_gaussSpace hh D _) (extVec_mem_gaussSpace hh U _)
  let W : (TestOn D ⊕ TestOn D) → Lp ℝ 2 P := Sum.elim W₁ W₂
  have hW : ∀ s, W s ∈ gaussSpace (pairProc h) (memLp_pair hh) := by
    intro s
    cases s with
    | inl φ => exact hW₁ φ
    | inr ψ => exact hW₂ ψ
  have hG := isGaussianProcess_of_mem_gaussSpace (gaussian_pairProc hh)
    (centered_pairProc hh) (memLp_pair hh) W hW
  have hG' : IsGaussianProcess
      (Sum.elim (fun φ => (W₁ φ : Ω → ℝ)) (fun ψ => (W₂ ψ : Ω → ℝ))) P := by
    have he : (fun s => (W s : Ω → ℝ)) =
        Sum.elim (fun φ => (W₁ φ : Ω → ℝ)) (fun ψ => (W₂ ψ : Ω → ℝ)) := by
      funext s
      cases s <;> rfl
    rwa [← he]
  have hind := hG'.indepFun_of_covariance_eq_zero
    (fun φ => (Lp.aestronglyMeasurable _).aemeasurable)
    (fun ψ => (Lp.aestronglyMeasurable _).aemeasurable) fun φ ψ => by
      rw [covariance_eq_inner _ (Lp.memLp _)
        (isCGauss_of_mem_gaussSpace (gaussian_pairProc hh) (centered_pairProc hh)
          (memLp_pair hh) (hW₁ φ)).2, Lp.toLp_coeFn]
      exact inner_cmIso_extVec_sub hh hUD hD _ (extC D ψ)
  refine hind.process_congr (fun φ => (zbExt_ae hh U (extC D φ)).symm) fun ψ => ?_
  filter_upwards [Lp.coeFn_sub (extVec hh D ((D : Set ℂ).indicator (extC D ψ)))
    (extVec hh U ((U : Set ℂ).indicator (extC D ψ))), zbExt_ae hh D (extC D ψ),
    zbExt_ae hh U (extC D ψ)] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]

end Model

section ModelPair

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {U D : Opens ℂ} (hUD : U ≤ D)
  (hD : ZBAdmissible D) {hzD hzU : Ω → DistC} {G : DistOn D → DistOn D}

include hh hUD hD in
/-- Model pair, harmonic part: `⟨h_{U^c}, −Δf/(2π)⟩ = 0` a.s. for each `f ∈ C_c^∞(U)`. -/
theorem wholePlaneModel_harm (hzDae : ∀ φ : TestC, (fun ω => hzD ω φ) =ᵐ[P] zbExt hh D φ)
    (hzUae : ∀ φ : TestC, (fun ω => hzU ω φ) =ᵐ[P] zbExt hh U φ)
    (hGae : (fun ω => G (restrictTo D (hzD ω))) =ᵐ[P] fun ω => restrictTo D (hzU ω))
    (f : zsSub (U : Set ℂ)) :
    ∀ᵐ ω ∂P, restrictDist U (restrictTo D (hzD ω) - G (restrictTo D (hzD ω)))
      (cmTestOn f) = 0 := by
  have hU : ZBAdmissible U := zbAdmissible_mono hUD hD
  have e : extC D (testIncl U D (cmTestOn f)) = cmTest (zsTest f.2) := by
    rw [testIncl_testIncl hUD, extC_cmTestOn]
  filter_upwards [hGae, ae_version_cmTest_eq hh hUD hD hzDae f,
    ae_version_cmTest_eq hh le_rfl hU hzUae f] with ω h1 h2 h3
  rw [restrictDist_apply, sub_apply, h1, restrictTo_apply,
    restrictTo_apply, e, h2, h3, sub_self]

include hh hUD hD in
/-- Model pair, law of the zero-boundary part. -/
theorem wholePlaneModel_isZBGFFExtOn (hzDm : Measurable hzD)
    (hzUae : ∀ φ : TestC, (fun ω => hzU ω φ) =ᵐ[P] zbExt hh U φ) (hGm : Measurable G)
    (hGae : (fun ω => G (restrictTo D (hzD ω))) =ᵐ[P] fun ω => restrictTo D (hzU ω)) :
    IsZBGFFExtOn U D (fun ω => G (restrictTo D (hzD ω))) P := by
  have hU : ZBAdmissible U := zbAdmissible_mono hUD hD
  have hae : ∀ φ : TestOn D, (fun ω => G (restrictTo D (hzD ω)) φ) =ᵐ[P]
      zbExt hh U (extC D φ) := fun φ => by
    filter_upwards [hGae, hzUae (extC D φ)] with ω h1 h2
    rw [h1, restrictTo_apply]
    exact h2
  refine ⟨hGm.comp ((measurable_restrictTo D).comp hzDm), ?_, fun φ => ?_, fun φ ψ => ?_⟩
  · exact ((isGaussianProcess_zbExt_sumElim hh U).comp_right
      (fun φ : TestOn D => Sum.inl (extC D φ))).congr fun φ => (hae φ).symm
  · rw [integral_congr_ae (hae φ)]
    exact integral_zbExt hh U _
  · rw [covariance_congr_of_ae_eq (hae φ) (hae ψ),
      SupercriticalConformalCovariance.Markov.covariance_zbExt_general hh hU, coe_extC,
      coe_extC]

include hh hUD hD in
/-- Model pair, independence of the two parts. -/
theorem wholePlaneModel_indepFun (hzDae : ∀ φ : TestC, (fun ω => hzD ω φ) =ᵐ[P] zbExt hh D φ)
    (hzUae : ∀ φ : TestC, (fun ω => hzU ω φ) =ᵐ[P] zbExt hh U φ)
    (hGae : (fun ω => G (restrictTo D (hzD ω))) =ᵐ[P] fun ω => restrictTo D (hzU ω)) :
    IndepFun (fun ω => G (restrictTo D (hzD ω)))
      (fun ω => restrictTo D (hzD ω) - G (restrictTo D (hzD ω))) P := by
  have hp := (indepFun_zbExt_sub hh hUD hD).process_congr
    (X' := fun (φ : TestOn D) ω => G (restrictTo D (hzD ω)) φ)
    (Y' := fun (ψ : TestOn D) ω =>
      (restrictTo D (hzD ω) - G (restrictTo D (hzD ω))) ψ) (fun φ => by
      filter_upwards [hGae, hzUae (extC D φ)] with ω h1 h2
      rw [h1, restrictTo_apply]
      exact h2.symm) fun ψ => by
      filter_upwards [hGae, hzUae (extC D ψ), hzDae (extC D ψ)] with ω h1 h2 h3
      rw [sub_apply, h1, restrictTo_apply, restrictTo_apply, h2, h3]
  rw [IndepFun_iff_Indep] at hp ⊢
  simp only [DistOn.measurableSpace, MeasurableSpace.comap_comp]
  exact hp

end ModelPair

/-! ### Transfer along equal laws -/

section Transfer

variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
  {P : Measure Ω} {P' : Measure Ω'} {X : Ω → E} {X' : Ω' → E}

lemma map_comp_eq_of_map_eq {β : Type*} [MeasurableSpace β] (hX : Measurable X)
    (hX' : Measurable X') (hlaw : P.map X = P'.map X') {F : E → β} (hF : Measurable F) :
    P.map (fun ω => F (X ω)) = P'.map (fun ω => F (X' ω)) := by
  calc P.map (fun ω => F (X ω)) = (P.map X).map F := (Measure.map_map hF hX).symm
    _ = (P'.map X').map F := by rw [hlaw]
    _ = P'.map (fun ω => F (X' ω)) := Measure.map_map hF hX'

lemma ae_of_map_eq (hX : Measurable X) (hX' : Measurable X') (hlaw : P.map X = P'.map X')
    {p : E → Prop} (hp : MeasurableSet {x | p x}) (h : ∀ᵐ ω ∂P, p (X ω)) :
    ∀ᵐ ω ∂P', p (X' ω) := by
  rw [← ae_map_iff hX'.aemeasurable hp, ← hlaw]
  exact (ae_map_iff hX.aemeasurable hp).2 h

lemma integral_comp_of_map_eq (hX : Measurable X) (hX' : Measurable X')
    (hlaw : P.map X = P'.map X') {F : E → ℝ} (hF : Measurable F) :
    ∫ ω, F (X ω) ∂P = ∫ ω, F (X' ω) ∂P' := by
  rw [← integral_map hX.aemeasurable hF.aestronglyMeasurable, hlaw,
    integral_map hX'.aemeasurable hF.aestronglyMeasurable]

lemma covariance_comp_of_map_eq (hX : Measurable X) (hX' : Measurable X')
    (hlaw : P.map X = P'.map X') {F₁ F₂ : E → ℝ} (hF₁ : Measurable F₁) (hF₂ : Measurable F₂) :
    cov[fun ω => F₁ (X ω), fun ω => F₂ (X ω); P] =
      cov[fun ω => F₁ (X' ω), fun ω => F₂ (X' ω); P'] := by
  have h1 := covariance_map (μ := P) hF₁.aestronglyMeasurable hF₂.aestronglyMeasurable
    hX.aemeasurable
  have h2 := covariance_map (μ := P') hF₁.aestronglyMeasurable hF₂.aestronglyMeasurable
    hX'.aemeasurable
  rw [hlaw] at h1
  exact h1.symm.trans h2

lemma indepFun_comp_of_map_eq [IsFiniteMeasure P] [IsFiniteMeasure P'] (hX : Measurable X)
    (hX' : Measurable X') (hlaw : P.map X = P'.map X') {β₁ β₂ : Type*} [MeasurableSpace β₁]
    [MeasurableSpace β₂] {F₁ : E → β₁} {F₂ : E → β₂} (hF₁ : Measurable F₁)
    (hF₂ : Measurable F₂) (h : IndepFun (fun ω => F₁ (X ω)) (fun ω => F₂ (X ω)) P) :
    IndepFun (fun ω => F₁ (X' ω)) (fun ω => F₂ (X' ω)) P' := by
  have h' : IndepFun (F₁ ∘ X) (F₂ ∘ X) P := h
  rw [indepFun_iff_map_prod_eq_prod_map_map (hF₁.comp hX).aemeasurable
    (hF₂.comp hX).aemeasurable] at h'
  show IndepFun (F₁ ∘ X') (F₂ ∘ X') P'
  rw [indepFun_iff_map_prod_eq_prod_map_map (hF₁.comp hX').aemeasurable
    (hF₂.comp hX').aemeasurable]
  have e1 := map_comp_eq_of_map_eq hX hX' hlaw hF₁
  have e2 := map_comp_eq_of_map_eq hX hX' hlaw hF₂
  have e3 := map_comp_eq_of_map_eq hX hX' hlaw (F := fun x => (F₁ x, F₂ x)) (hF₁.prodMk hF₂)
  simp only [Function.comp_def] at h' e3 ⊢
  rw [← e1, ← e2, ← e3]
  exact h'

/-- The law of the extended zero-boundary GFF passes along equal laws. -/
theorem IsZBGFFExtOn.of_map_eq {U D : Opens ℂ} (hX : Measurable X) (hX' : Measurable X')
    (hlaw : P.map X = P'.map X') {G : E → DistOn D} (hG : Measurable G)
    (h : IsZBGFFExtOn U D (fun ω => G (X ω)) P) : IsZBGFFExtOn U D (fun ω => G (X' ω)) P' := by
  have hev : ∀ φ : TestOn D, Measurable fun x => G x φ := fun φ =>
    (measurable_distOn_apply φ).comp hG
  refine ⟨hG.comp hX', ⟨fun I => ?_⟩, fun φ => ?_, fun φ ψ => ?_⟩
  · have hF : Measurable fun x => I.restrict fun φ : TestOn D => G x φ :=
      measurable_pi_iff.2 fun i => hev i
    exact ⟨(hF.comp hX').aemeasurable, by
      rw [← map_comp_eq_of_map_eq hX hX' hlaw hF]
      exact (h.gaussian.hasGaussianLaw I).isGaussian_map⟩
  · rw [← integral_comp_of_map_eq hX hX' hlaw (hev φ)]
    exact h.centered φ
  · rw [← covariance_comp_of_map_eq hX hX' hlaw (hev φ) (hev ψ)]
    exact h.covariance_eq φ ψ

end Transfer

/-! ### The covariance only sees `1_U φ` -/

lemma testMeasPos_indicator {U : Set ℂ} (hU : MeasurableSet U) (ρ : ℂ → ℝ) :
    testMeasPos (U.indicator ρ) = (testMeasPos ρ).restrict U := by
  unfold testMeasPos
  rw [restrict_withDensity hU, ← withDensity_indicator hU]
  congr 1
  funext z
  by_cases hz : z ∈ U <;> simp [hz]

lemma testMeasNeg_indicator {U : Set ℂ} (hU : MeasurableSet U) (ρ : ℂ → ℝ) :
    testMeasNeg (U.indicator ρ) = (testMeasNeg ρ).restrict U := by
  unfold testMeasNeg
  rw [restrict_withDensity hU, ← withDensity_indicator hU]
  congr 1
  funext z
  by_cases hz : z ∈ U <;> simp [hz]

lemma dualCov_zeroSpace_restrict {U : Set ℂ} (hU : IsOpen U) (μ ν : Measure ℂ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    dualCov U (zeroSpace U) (μ.restrict U) (ν.restrict U) = dualCov U (zeroSpace U) μ ν := by
  unfold dualCov
  rw [← Measure.restrict_add, ← dualNormSq_zeroSpace_restrict hU,
    ← dualNormSq_zeroSpace_restrict hU, ← dualNormSq_zeroSpace_restrict hU]

/-- `⟨1_U ρ, 1_U σ⟩_{H⁻¹(U)} = ⟨ρ, σ⟩_{H⁻¹(U)}` for continuous compactly supported `ρ, σ`: the
dual Dirichlet form on `U` only sees the restrictions to `U`. -/
theorem zeroGFFTestCov_indicator (U : Opens ℂ) {ρ σ : ℂ → ℝ} (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) (hσ : Continuous σ) (hσc : HasCompactSupport σ) :
    zeroGFFTestCov U ((U : Set ℂ).indicator ρ) ((U : Set ℂ).indicator σ) =
      zeroGFFTestCov U ρ σ := by
  have : IsFiniteMeasure (testMeasPos ρ) := (K3.isGoodMeas_withDensity hρ hρc).1
  have : IsFiniteMeasure (testMeasNeg ρ) := (K3.isGoodMeas_withDensity hρ.neg hρc.neg).1
  have : IsFiniteMeasure (testMeasPos σ) := (K3.isGoodMeas_withDensity hσ hσc).1
  have : IsFiniteMeasure (testMeasNeg σ) := (K3.isGoodMeas_withDensity hσ.neg hσc.neg).1
  have hm := U.isOpen.measurableSet
  unfold zeroGFFTestCov
  rw [testMeasPos_indicator hm, testMeasNeg_indicator hm, testMeasPos_indicator hm,
    testMeasNeg_indicator hm, dualCov_zeroSpace_restrict U.isOpen,
    dualCov_zeroSpace_restrict U.isOpen, dualCov_zeroSpace_restrict U.isOpen,
    dualCov_zeroSpace_restrict U.isOpen]

/-- The covariance of the extended zero-boundary GFF, without indicators. -/
theorem IsZBGFFExtOn.covariance_eq' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U D : Opens ℂ} {X : Ω → DistOn D} (hX : IsZBGFFExtOn U D X P) (φ ψ : TestOn D) :
    cov[fun ω => X ω φ, fun ω => X ω ψ; P] = zeroGFFTestCov U φ ψ := by
  rw [hX.covariance_eq, zeroGFFTestCov_indicator U φ.continuous φ.hasCompactSupport
    ψ.continuous ψ.hasCompactSupport]

/-! ### `h_U` vanishes on `D \ cl U` -/

/-- `D \ cl U` as an open set. -/
def outsideOpens (U D : Opens ℂ) : Opens ℂ :=
  D ⊓ ⟨(closure (U : Set ℂ))ᶜ, isClosed_closure.isOpen_compl⟩

lemma outsideOpens_le (U D : Opens ℂ) : outsideOpens U D ≤ D := inf_le_left

lemma zeroGFFTestCov_zero_zero (U : Set ℂ) : zeroGFFTestCov U 0 0 = 0 := by
  simp [zeroGFFTestCov, dualCov, dualNormSq, testMeasPos, testMeasNeg]

/-- A random distribution with the law of the zero-boundary GFF on `U` extended by zero vanishes
almost surely on `D \ cl U` ("`h_U` is zero on `D \ U`", Proposition 3.1). -/
theorem IsZBGFFExtOn.ae_restrictDist_outside_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {U D : Opens ℂ} {X : Ω → DistOn D}
    (hX : IsZBGFFExtOn U D X P) :
    ∀ᵐ ω ∂P, restrictDist (outsideOpens U D) (X ω) = 0 := by
  set W := outsideOpens U D
  have key : ∀ φ : TestOn W, ∀ᵐ ω ∂P, X ω (testIncl W D φ) = 0 := by
    intro φ
    set ψ := testIncl W D φ
    have hind : (U : Set ℂ).indicator (ψ : ℂ → ℝ) = 0 := by
      funext x
      by_cases hx : x ∈ (U : Set ℂ)
      · rw [indicator_of_mem hx, coe_testIncl (outsideOpens_le U D)]
        refine φ.zero_on_compl fun hxW => ?_
        exact (show x ∉ closure (U : Set ℂ) from hxW.2) (subset_closure hx)
      · rw [indicator_of_notMem hx]
        rfl
    have hG : HasGaussianLaw (fun ω => X ω ψ) P := hX.gaussian.hasGaussianLaw_eval ψ
    have hvar : Var[fun ω => X ω ψ; P] = 0 := by
      rw [← covariance_self hG.aemeasurable, hX.covariance_eq, hind, zeroGFFTestCov_zero_zero]
    have hmap := hG.map_eq_gaussianReal
    rw [hX.centered, hvar, Real.toNNReal_zero, gaussianReal_zero_var] at hmap
    have h0 : ∀ᵐ x ∂(P.map fun ω => X ω ψ), x = 0 := by
      rw [hmap]
      exact (ae_dirac_iff (measurableSet_singleton 0)).2 rfl
    exact ae_of_ae_map hG.aemeasurable h0
  filter_upwards [ae_all_iff.2 fun j => key (distGen W j)] with ω hω
  apply injective_distOn_pairings W
  funext j
  exact hω j

/-! ### The Markov property of the zero-boundary GFF -/

lemma indicator_testOn {U : Opens ℂ} (φ : TestOn U) :
    (U : Set ℂ).indicator (φ : ℂ → ℝ) = φ := by
  funext x
  by_cases hx : x ∈ (U : Set ℂ)
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, φ.zero_on_compl hx]
    rfl

/-- The restriction to `U` of the zero-boundary GFF on `U` extended by zero is a zero-boundary
GFF on `U`. -/
theorem IsZBGFFExtOn.isZeroBoundaryGFF_restrictDist {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U D : Opens ℂ} (hUD : U ≤ D) {X : Ω → DistOn D}
    (hX : IsZBGFFExtOn U D X P) : IsZeroBoundaryGFF U (fun ω => restrictDist U (X ω)) P := by
  have hfun : ∀ φ : TestOn U,
      (U : Set ℂ).indicator ((testIncl U D φ : TestOn D) : ℂ → ℝ) = φ := fun φ => by
    rw [coe_testIncl hUD, indicator_testOn]
  have hm : Measurable fun ω => restrictDist U (X ω) :=
    (measurable_restrictDist U).comp hX.measurable
  refine ⟨hm, ⟨fun φ => (measurable_distOn_apply φ).comp hm,
    hX.gaussian.comp_right (testIncl U D), fun φ => hX.centered _, fun φ ψ => ?_⟩⟩
  rw [← hfun φ, ← hfun ψ]
  exact hX.covariance_eq _ _

/-- **The Markov decomposition** `h = h_U + h_{U^c}` of a random distribution `h` on `D` along
the open set `U ⊆ D` (specification Proposition 3.1), with `h_U = hU` and `h_{U^c} = h − hU`:
* `hU` has the law of the zero-boundary GFF on `U` extended by zero to `D`
  (`IsZBGFFExtOn`); in particular its restriction to `U` is a zero-boundary GFF on `U` and it
  vanishes on `D \ cl U`;
* `hU` and `h − hU` are independent;
* `h − hU` is harmonic on `U`: almost surely its restriction to `U` is integration against a
  harmonic function on `U`. -/
structure IsMarkovDecomposition {Ω : Type*} [MeasurableSpace Ω] (U D : Opens ℂ)
    (h hU : Ω → DistOn D) (P : Measure Ω) : Prop where
  /-- `h_U` is a zero-boundary GFF on `U` extended by zero to `D`. -/
  isZBGFFExtOn : IsZBGFFExtOn U D hU P
  /-- The restriction of `h_U` to `U` is a zero-boundary GFF on `U`. -/
  isZeroBoundaryGFF : IsZeroBoundaryGFF U (fun ω => restrictDist U (hU ω)) P
  /-- `h_U` vanishes on `D \ cl U`. -/
  ae_restrictDist_outside_eq_zero : ∀ᵐ ω ∂P, restrictDist (outsideOpens U D) (hU ω) = 0
  /-- `h_U` and `h_{U^c} = h − h_U` are independent. -/
  indepFun : IndepFun hU (fun ω => h ω - hU ω) P
  /-- `h_{U^c}` is harmonic on `U`. -/
  ae_harmonic : ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (U : Set ℂ) ∧
    ∀ φ : TestOn U, restrictDist U (h ω - hU ω) φ = ∫ x, g x * φ x

/-- A distribution on `U` that annihilates `−Δψ/(2π)` for the countable generating family
`ψ = distGen U j` is a harmonic function (Weyl's lemma, LQGMetric). -/
theorem exists_harmonic_of_distGen {U : Opens ℂ} (T : DistOn U)
    (hT : ∀ j : ℕ × ℕ, T (cmTestOn (toZs (distGen U j))) = 0) :
    ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (U : Set ℂ) ∧
      ∀ φ : TestOn U, T φ = ∫ x, g x * φ x := by
  have hT0 : T.comp (lapV U) = 0 := by
    apply injective_distOn_pairings U
    funext j
    show T (lapV U (distGen U j)) = 0
    rw [← cmTestOn_toZs]
    exact hT j
  refine MarkovWeyl3.exists_harmonic_of_laplacian_eq_zero T fun f => ?_
  rw [← toZs_ofZs f, cmTestOn_toZs]
  exact congrArg (fun S : DistOn U => S (ofZs f)) hT0

/-- **Proposition 3.1 (Markov property), zero-boundary GFF on an admissible open set `D`.**
For every open `U ⊆ D` there is a single Borel map `G : 𝒟'(D) → 𝒟'(D)` such that, for every
zero-boundary GFF `h` on `D` (on any probability space), `h = G(h) + (h − G(h))` is the Markov
decomposition: `G(h)` is a zero-boundary GFF on `U` extended by zero, independent of
`h − G(h)`, which is harmonic on `U`. -/
theorem exists_markovMap {U D : Opens ℂ} (hUD : U ≤ D) (hD : ZBAdmissible D) :
    ∃ G : DistOn D → DistOn D, Measurable G ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        {h : Ω → DistOn D}, IsZeroBoundaryGFF D h P →
          IsMarkovDecomposition U D h (fun ω => G (h ω)) P := by
  obtain ⟨Ω₀, _, P₀, w, hP₀, hh⟩ := GFFExist.exists_wholePlaneGFF
  obtain ⟨hzD, hzU, G, hzDm, hzDae, -, hzUae, hGm, hGae⟩ :=
    exists_markovMap_of_wholePlane hh hUD hD
  refine ⟨G, hGm, fun {Ω} _ {P} _ {h} hh' => ?_⟩
  have hA := SupercriticalConformalCovariance.Markov.isZeroBoundaryGFF_restrict_of_version hh hD
    hzDm hzDae
  have hAm : Measurable fun ω => restrictTo D (hzD ω) := hA.measurable
  have hlaw := hA.map_eq hh'
  have hsubm : Measurable fun T : DistOn D => T - G T :=
    measurable_distOn_iff.2 fun φ =>
      (measurable_distOn_apply φ).sub ((measurable_distOn_apply φ).comp hGm)
  have hext : IsZBGFFExtOn U D (fun ω => G (h ω)) P :=
    (wholePlaneModel_isZBGFFExtOn hh hUD hD hzDm hzUae hGm hGae).of_map_eq hAm hh'.measurable
      hlaw hGm
  refine ⟨hext, hext.isZeroBoundaryGFF_restrictDist hUD, hext.ae_restrictDist_outside_eq_zero,
    ?_, ?_⟩
  · exact indepFun_comp_of_map_eq hAm hh'.measurable hlaw hGm hsubm
      (wholePlaneModel_indepFun hh hUD hD hzDae hzUae hGae)
  · have key : ∀ j : ℕ × ℕ, ∀ᵐ ω ∂P,
        restrictDist U (h ω - G (h ω)) (cmTestOn (toZs (distGen U j))) = 0 := by
      intro j
      have hΦ : Measurable fun T : DistOn D =>
          restrictDist U (T - G T) (cmTestOn (toZs (distGen U j))) :=
        (measurable_distOn_apply _).comp ((measurable_restrictDist U).comp hsubm)
      exact ae_of_map_eq (p := fun T : DistOn D =>
          restrictDist U (T - G T) (cmTestOn (toZs (distGen U j))) = 0)
        hAm hh'.measurable hlaw (measurableSet_eq_fun hΦ measurable_const)
        (wholePlaneModel_harm hh hUD hD hzDae hzUae hGae _)
    filter_upwards [ae_all_iff.2 key] with ω hω
    exact exists_harmonic_of_distGen _ hω

/-! ### The conditional law given the field outside `U` -/

/-- `E[exp(iX)] = exp(−Var X / 2)` for a centred Gaussian `X`. -/
lemma integral_exp_I_mul_of_hasGaussianLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : HasGaussianLaw X P) (h0 : ∫ ω, X ω ∂P = 0) :
    ∫ ω, Complex.exp (Complex.I * (X ω : ℂ)) ∂P =
      ((Real.exp (-(1 / 2) * Var[X; P]) : ℝ) : ℂ) := by
  have hmap := hX.map_eq_gaussianReal
  rw [h0] at hmap
  have hc := charFun_gaussianReal (μ := 0) (v := Var[X; P].toNNReal) 1
  rw [← hmap, charFun_apply_real, integral_map hX.aemeasurable (by fun_prop)] at hc
  have hv : ((Var[X; P].toNNReal : ℝ)) = Var[X; P] :=
    Real.coe_toNNReal _ (variance_nonneg X P)
  calc ∫ ω, Complex.exp (Complex.I * (X ω : ℂ)) ∂P
      = ∫ ω, Complex.exp (((1 : ℝ) : ℂ) * (X ω : ℂ) * Complex.I) ∂P := by
        congr 1
        funext ω
        congr 1
        push_cast
        ring
    _ = _ := hc
    _ = ((Real.exp (-(1 / 2) * Var[X; P]) : ℝ) : ℂ) := by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        rw [hv]
        ring

lemma measurable_exp_I_mul {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) :
    Measurable fun a => Complex.exp (Complex.I * (f a : ℂ)) :=
  (measurable_const.mul (Complex.measurable_ofReal.comp hf)).cexp

lemma integrable_exp_I_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {f : Ω → ℝ} (hf : Measurable f) :
    Integrable (fun ω => Complex.exp (Complex.I * (f ω : ℂ))) P :=
  Integrable.of_bound (measurable_exp_I_mul hf).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal (f ω)).le)

section CondLaw

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {U D : Opens ℂ} {h hU : Ω → DistOn D}

/-- **Conditional law of `h_U` given `h_{U^c}`.** Conditionally on `σ(h − h_U)`, `h_U` is a
zero-boundary GFF on `U` (extended by zero): for every test function `φ ∈ 𝓓(D)`,
`E[exp(i⟨h_U, φ⟩) | σ(h − h_U)] = exp(−½ ‖φ‖²_{H⁻¹(U)})` almost surely. -/
theorem IsMarkovDecomposition.condExp_exp_zbPart (hd : IsMarkovDecomposition U D h hU P)
    (hm : Measurable fun ω => h ω - hU ω) (φ : TestOn D) :
    P[fun ω => Complex.exp (Complex.I * (hU ω φ : ℂ)) |
        MeasurableSpace.comap (fun ω => h ω - hU ω) inferInstance] =ᵐ[P]
      fun _ => ((Real.exp (-(1 / 2) * zeroGFFTestCov U φ φ) : ℝ) : ℂ) := by
  have hUm := hd.isZBGFFExtOn.measurable
  have hind : Indep (MeasurableSpace.comap hU inferInstance)
      (MeasurableSpace.comap (fun ω => h ω - hU ω) inferInstance) P :=
    (IndepFun_iff_Indep _ _ _).1 hd.indepFun
  have hf : StronglyMeasurable[MeasurableSpace.comap hU inferInstance]
      (fun ω => Complex.exp (Complex.I * (hU ω φ : ℂ))) :=
    (@measurable_exp_I_mul Ω (MeasurableSpace.comap hU inferInstance) _
      ((measurable_distOn_apply φ).comp (comap_measurable hU))).stronglyMeasurable
  refine (condExp_indep_eq hUm.comap_le hm.comap_le hf hind).trans
    (Eventually.of_forall fun _ => ?_)
  have hG : HasGaussianLaw (fun ω => hU ω φ) P := hd.isZBGFFExtOn.gaussian.hasGaussianLaw_eval φ
  rw [integral_exp_I_mul_of_hasGaussianLaw hG (hd.isZBGFFExtOn.centered φ),
    ← covariance_self hG.aemeasurable, hd.isZBGFFExtOn.covariance_eq']

/-- **Conditional law of the field given the field outside `U`** (Proposition 3.1, "the conditional
law of `h|_U` given `h|_{D∖U}` is that of the GFF on `U` plus the harmonic extension"): for every
test function `φ ∈ 𝓓(D)`,
`E[exp(i⟨h, φ⟩) | σ(h_{U^c})] = exp(i⟨h_{U^c}, φ⟩ − ½ ‖φ‖²_{H⁻¹(U)})` almost surely, where
`h_{U^c} = h − h_U` is harmonic on `U`. -/
theorem IsMarkovDecomposition.condExp_exp_field (hd : IsMarkovDecomposition U D h hU P)
    (hh : Measurable h) (φ : TestOn D) :
    P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) |
        MeasurableSpace.comap (fun ω => h ω - hU ω) inferInstance] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * ((h ω - hU ω) φ : ℂ)) *
        ((Real.exp (-(1 / 2) * zeroGFFTestCov U φ φ) : ℝ) : ℂ) := by
  have hUm := hd.isZBGFFExtOn.measurable
  have hm : Measurable fun ω => h ω - hU ω := measurable_distOn_iff.2 fun ψ =>
    ((measurable_distOn_apply ψ).comp hh).sub ((measurable_distOn_apply ψ).comp hUm)
  have hsplit : (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) = fun ω =>
      ContinuousLinearMap.mul ℝ ℂ (Complex.exp (Complex.I * ((h ω - hU ω) φ : ℂ)))
        (Complex.exp (Complex.I * (hU ω φ : ℂ))) := by
    funext ω
    rw [ContinuousLinearMap.mul_apply', ← Complex.exp_add, ← mul_add, sub_apply]
    push_cast
    ring_nf
  have hf : StronglyMeasurable[MeasurableSpace.comap (fun ω => h ω - hU ω) inferInstance]
      (fun ω => Complex.exp (Complex.I * ((h ω - hU ω) φ : ℂ))) :=
    (@measurable_exp_I_mul Ω (MeasurableSpace.comap (fun ω => h ω - hU ω) inferInstance) _
      ((measurable_distOn_apply φ).comp (comap_measurable fun ω => h ω - hU ω))).stronglyMeasurable
  have hfg : Integrable (fun ω => ContinuousLinearMap.mul ℝ ℂ
      (Complex.exp (Complex.I * ((h ω - hU ω) φ : ℂ)))
      (Complex.exp (Complex.I * (hU ω φ : ℂ)))) P := by
    rw [← hsplit]
    exact integrable_exp_I_mul ((measurable_distOn_apply φ).comp hh)
  have hg := integrable_exp_I_mul (P := P) ((measurable_distOn_apply φ).comp hUm)
  rw [hsplit]
  filter_upwards [condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hf hfg
    hg, hd.condExp_exp_zbPart hm φ] with ω h1 h2
  rw [h1, h2, ContinuousLinearMap.mul_apply']

end CondLaw

/-- **Joint law of `(h_{U^c}, h)`** (the kernel form of Proposition 3.1): the pair is distributed
as `(Y, Y + Z)` with `Y = h_{U^c}` and `Z` an independent copy of `h_U` (a zero-boundary GFF on
`U` extended by zero). Equivalently, given `h_{U^c} = y`, the field is `y` plus a fresh
zero-boundary GFF on `U`. -/
theorem IsMarkovDecomposition.map_pair_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U D : Opens ℂ} {h hU : Ω → DistOn D}
    (hd : IsMarkovDecomposition U D h hU P) (hh : Measurable h) :
    P.map (fun ω => (h ω - hU ω, h ω)) =
      ((P.map fun ω => h ω - hU ω).prod (P.map hU)).map fun p => (p.1, p.1 + p.2) := by
  have hUm := hd.isZBGFFExtOn.measurable
  have hm : Measurable fun ω => h ω - hU ω := measurable_distOn_iff.2 fun ψ =>
    ((measurable_distOn_apply ψ).comp hh).sub ((measurable_distOn_apply ψ).comp hUm)
  have hadd : Measurable fun p : DistOn D × DistOn D => (p.1, p.1 + p.2) :=
    measurable_fst.prodMk (measurable_distOn_iff.2 fun ψ =>
      ((measurable_distOn_apply ψ).comp measurable_fst).add
        ((measurable_distOn_apply ψ).comp measurable_snd))
  rw [← (indepFun_iff_map_prod_eq_prod_map_map hm.aemeasurable hUm.aemeasurable).1
    hd.indepFun.symm, Measure.map_map hadd (hm.prodMk hUm)]
  congr 1
  funext ω
  simp

/-- **Proposition 3.1 on subdomains of `ℍ`.** For open `U ⊆ D ⊆ ℍ` there is a Borel map
`G : 𝒟'(D) → 𝒟'(D)` such that every zero-boundary GFF `h` on `D` has the Markov decomposition
`h = G(h) + (h − G(h))` along `U`. -/
theorem exists_markovMap_of_subset_H {U D : Opens ℂ} (hUD : U ≤ D)
    (hDH : (D : Set ℂ) ⊆ QuantumZipper.H) :
    ∃ G : DistOn D → DistOn D, Measurable G ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        {h : Ω → DistOn D}, IsZeroBoundaryGFF D h P →
          IsMarkovDecomposition U D h (fun ω => G (h ω)) P :=
  exists_markovMap hUD (zbAdmissible_of_subset_H hDH)

/-- **Proposition 3.1 for `D = ℍ`.** For every open `U ⊆ ℍ` there is a Borel map `G` on
`𝒟'(ℍ)` such that every zero-boundary GFF `h` on `ℍ` decomposes as `h = G(h) + (h − G(h))`,
with `G(h)` a zero-boundary GFF on `U` (extended by zero), independent of `h − G(h)`, which is
harmonic on `U`. -/
theorem exists_markovMap_upperHalfPlane {U : Opens ℂ} (hU : (U : Set ℂ) ⊆ QuantumZipper.H) :
    ∃ G : DistOn ⟨QuantumZipper.H, QuantumZipper.isOpen_H⟩ →
        DistOn ⟨QuantumZipper.H, QuantumZipper.isOpen_H⟩, Measurable G ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        {h : Ω → DistOn ⟨QuantumZipper.H, QuantumZipper.isOpen_H⟩},
        IsZeroBoundaryGFF ⟨QuantumZipper.H, QuantumZipper.isOpen_H⟩ h P →
          IsMarkovDecomposition U ⟨QuantumZipper.H, QuantumZipper.isOpen_H⟩ h
            (fun ω => G (h ω)) P :=
  exists_markovMap_of_subset_H (D := ⟨QuantumZipper.H, QuantumZipper.isOpen_H⟩) hU le_rfl

end GFF
end InteractingSLE
