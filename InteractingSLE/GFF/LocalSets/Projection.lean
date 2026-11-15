import InteractingSLE.GFF.LocalSets.Characterization
import QuantumZipper.Proofs.Thm11.AddendumAssemblyLin
import LQGMetric.Field.MarkovHarm
import LQGMetric.Field.HarmLocA
import LQGMetric.Field.ExistGFF
import QuantumZipper.Proofs.GFF.K3.MixedRiesz
import LQGMetric.Field.StandardBorelDist

/-!
# The projection onto `H(U)` as an `L²` limit of Dirichlet pairings

Infrastructure for the proof of Lemma 3.6, (iv) ⇒ (ii) (specification p. 54: "`P_U` may be defined
by choosing a Dirichlet-orthonormal basis obtained from a countable dense subset of `C_c^∞(U)` and
taking the distributional limit of the corresponding Gaussian series").

For `f ∈ C_c^∞(U)` write `lapTest U f = −Δf/2π ∈ 𝓓(ℍ)`, so that `T (lapTest U f) = (T, f)_∇` is the
Dirichlet pairing. With QuantumZipper's Gram vectors `covVec V φ` of the covariance
(`zeroGFFTestCov V φ ψ = ⟪covVec V φ, covVec V ψ⟫`, any open `V ⊆ ℍ`):

* `covVec_lapTest` : `covVec V (lapTest U f) = ∇f` for `U ⊆ V` (Green's identity);
* `inner_gradFeat_covVec_eq` : `⟪∇f, covVec V ψ⟫_V = ⟪∇f, covVec U ψ⟫_U` for `f ∈ C_c^∞(U)`,
  `U ⊆ V` (both are `∫ ψ f`);
* `exists_tendsto_gradFeat_covVec` : `∇f_n → covVec U Φ` for some `f_n ∈ C_c^∞(U)` (density);
* `IsMarkovDecomposition.integral_sq_sub_lapTest` : for the Markov decomposition `h = h_U + h_{U^c}`,
  `E|h_U(Φ) − (h, f)_∇|² = ‖covVec U Φ − ∇f‖²`, so `h_U(Φ)` is the `L²` limit of `(h, f_n)_∇`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper QuantumZipper.K3 QuantumZipper.Thm11Asm LQGMetric LQGMetric.MarkovZB
  LQGMetric.MarkovHarm

/-! ### Laplacian test functions -/

/-- `−Δf/2π` for `f ∈ C_c^∞(U)`, as a test function on `ℍ` (the Dirichlet pairing
`T (lapTest U f) = (T, f)_∇`). -/
def lapTest (U : Opens ℂ) (f : zsSub (U : Set ℂ)) : TestOn upperHalfPlaneOpens :=
  GFF.testIncl U upperHalfPlaneOpens (cmTestOn f)

lemma coe_lapTest {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens) (f : zsSub (U : Set ℂ)) :
    ⇑(lapTest U f) = cmTest (zsTest f.2) := by
  rw [lapTest, GFF.coe_testIncl hU]
  rfl

lemma tsupport_lapTest_subset {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens)
    (f : zsSub (U : Set ℂ)) : tsupport (lapTest U f) ⊆ tsupport f.1 := by
  rw [coe_lapTest hU]
  exact tsupport_cmTest_subset f.2

/-- A distribution harmonic on `V ⊇ U` annihilates the Dirichlet pairings of `C_c^∞(U)`. -/
theorem IsHarmonicDistOn.apply_lapTest_eq_zero {T : DistOn upperHalfPlaneOpens} {V : Set ℂ}
    (hV : IsOpen V) (hT : IsHarmonicDistOn T V) {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens)
    (hUV : (U : Set ℂ) ⊆ V) (f : zsSub (U : Set ℂ)) : T (lapTest U f) = 0 := by
  obtain ⟨v, hv, hTv⟩ := hT
  have hsupp : tsupport (lapTest U f) ⊆ V :=
    (tsupport_lapTest_subset hU f).trans (f.2.2.2.trans hUV)
  rw [hTv _ hsupp, coe_lapTest hU]
  exact HarmLoc.integral_mul_cmTest_of_harmonic hV hv (zsTest f.2) (f.2.2.2.trans hUV)

/-! ### Gram vectors -/

/-- `zeroGFFTestCov V` is the Gram form of `covVec V` on test functions of `ℍ`. -/
theorem zeroGFFTestCov_eq_inner_covVec {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H)
    (φ ψ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov V φ ψ = ⟪covVec V φ, covVec V ψ⟫ :=
  Thm11Asm.zeroGFFTestCov_eq_inner hV hVH (toTestFunH φ) (toTestFunH ψ)

theorem covVec_sub {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H) (φ ψ : TestOn upperHalfPlaneOpens) :
    covVec V ⇑(φ - ψ) = covVec V φ - covVec V ψ := by
  have := covVec_lin hV hVH (toTestFunH ψ) (toTestFunH (φ - ψ)) (toTestFunH φ) 1
    (fun z => by simp [toTestFunH])
  rw [one_smul] at this
  simp only [toTestFunH] at this
  rw [this]
  abel

theorem covVec_add {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H) (φ ψ : TestOn upperHalfPlaneOpens) :
    covVec V ⇑(φ + ψ) = covVec V φ + covVec V ψ := by
  have := covVec_lin hV hVH (toTestFunH φ) (toTestFunH ψ) (toTestFunH (φ + ψ)) 1
    (fun z => by simp [toTestFunH])
  rw [one_smul] at this
  exact this

/-- No positive-energy test function on `U` forces `f = 0` energy, hence `∇f = 0`, on every
`V ⊇ U`. -/
lemma gradFeat_eq_zero_of_nopos {U V : Set ℂ} (hUV : U ⊆ V)
    (hpos : ¬ ∃ g ∈ zeroSpace U, 0 < dirichletEnergyOn U g) {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) :
    gradFeat V f = 0 := by
  have hE : dirichletEnergyOn U f = 0 :=
    le_antisymm (not_lt.1 fun hlt => hpos ⟨f, hf, hlt⟩) (energy_nonneg _ _)
  have hfV : f ∈ zeroSpace V := ⟨hf.1, hf.2.1, hf.2.2.trans hUV⟩
  refine gradFeat_eq_zero_of_energy (isDNSpace_zeroSpace V) hfV ?_
  rw [energy_eq_of_tsupport_subset hfV.2.2, ← energy_eq_of_tsupport_subset hf.2.2, hE]

/-- Green's identity on an open `V ⊆ ℍ`: `⟪∇f, ∇g⟫_V = ∫ g · (−Δf/2π)`. -/
theorem inner_gradFeat_gradFeat {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g) {f g : ℂ → ℝ} (hf : f ∈ zeroSpace V)
    (hg : g ∈ zeroSpace V) :
    ⟪gradFeat V f, gradFeat V g⟫ = ∫ x, g x * cmTest (zsTest hf) x := by
  obtain ⟨Ω₀, _, P₀, h₀, hP₀, hh₀⟩ := GFFExist.exists_wholePlaneGFF
  let Vo : Opens ℂ := ⟨V, hV⟩
  have hadm : ZBAdmissible Vo := zbAdmissible_of_subset_H hVH
  have h1 := zbRiesz_cmTestOn hh₀ hadm (⟨f, hf⟩ : zsSub (Vo : Set ℂ))
  have h2 := inner_zbRiesz_gradFeat hadm hpos (cmTestOn (⟨f, hf⟩ : zsSub (Vo : Set ℂ))) hg
  rw [h1] at h2
  exact h2

/-- `covVec V (−Δf/2π) = ∇f` for `f ∈ C_c^∞(U)`, `U ⊆ V ⊆ ℍ`. -/
theorem covVec_lapTest {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens) {V : Set ℂ} (hV : IsOpen V)
    (hVH : V ⊆ H) (hUV : (U : Set ℂ) ⊆ V) (f : zsSub (U : Set ℂ)) :
    covVec V (lapTest U f) = gradFeat V f.1 := by
  have hfV : f.1 ∈ zeroSpace V := ⟨f.2.1, f.2.2.1, f.2.2.2.trans hUV⟩
  by_cases hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g
  · refine eq_of_mem_gradClosure_of_inner_eq (covVec_mem V _) (gradFeat_mem_gradClosure hfV)
      fun g hg => ?_
    have h1 := inner_covVec_gradFeat hV hVH (toTestFunH (lapTest U f)) hpos hg
    simp only [toTestFunH] at h1
    rw [h1, inner_gradFeat_gradFeat hV hVH hpos hfV hg]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport fun h' => hz (hg.2.2 h'), mul_zero]]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [coe_lapTest hU]
    exact mul_comm _ _
  · rw [eq_zero_of_mem_gradClosure_of_nopos (isDNSpace_zeroSpace V) hpos (covVec_mem V _),
      eq_zero_of_mem_gradClosure_of_nopos (isDNSpace_zeroSpace V) hpos
        (gradFeat_mem_gradClosure hfV)]

/-- Domain independence of the pairing `⟪∇f, covVec · ψ⟫ = ∫ ψ f` for `f ∈ C_c^∞(U)`. -/
theorem inner_gradFeat_covVec_eq {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (hVH : V ⊆ H)
    (hUV : U ⊆ V) {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) (ψ : TestOn upperHalfPlaneOpens) :
    ⟪gradFeat V f, covVec V ψ⟫ = ⟪gradFeat U f, covVec U ψ⟫ := by
  have hfV : f ∈ zeroSpace V := ⟨hf.1, hf.2.1, hf.2.2.trans hUV⟩
  by_cases hpos : ∃ g ∈ zeroSpace U, 0 < dirichletEnergyOn U g
  · have hposV : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g := by
      obtain ⟨g, hg, hgE⟩ := hpos
      refine ⟨g, ⟨hg.1, hg.2.1, hg.2.2.trans hUV⟩, ?_⟩
      rwa [energy_eq_of_tsupport_subset (hg.2.2.trans hUV), ← energy_eq_of_tsupport_subset hg.2.2]
    rw [← real_inner_comm (gradFeat V f) (covVec V ψ), ← real_inner_comm (gradFeat U f) (covVec U ψ)]
    change ⟪covVec V (toTestFunH ψ).1, gradFeat V f⟫ = ⟪covVec U (toTestFunH ψ).1, gradFeat U f⟫
    rw [inner_covVec_gradFeat hV hVH (toTestFunH ψ) hposV hfV,
      inner_covVec_gradFeat hU (hUV.trans hVH) (toTestFunH ψ) hpos hf]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport fun h' => hz (hfV.2.2 h'), mul_zero],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport fun h' => hz (hf.2.2 h'), mul_zero]]
  · rw [gradFeat_eq_zero_of_nopos hUV hpos hf, gradFeat_eq_zero_of_nopos subset_rfl hpos hf,
      inner_zero_left, inner_zero_left]

/-- Domain independence of the Dirichlet norm on `C_c^∞(U)`. -/
theorem norm_gradFeat_eq {U V : Set ℂ} (hUV : U ⊆ V) {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) :
    ‖gradFeat V f‖ = ‖gradFeat U f‖ := by
  have hfV : f ∈ zeroSpace V := ⟨hf.1, hf.2.1, hf.2.2.trans hUV⟩
  have h1 := norm_gradFeat_sq ((isDNSpace_zeroSpace V).smooth f hfV)
    ((isDNSpace_zeroSpace V).energy f hfV)
  have h2 := norm_gradFeat_sq ((isDNSpace_zeroSpace U).smooth f hf)
    ((isDNSpace_zeroSpace U).energy f hf)
  rw [energy_eq_of_tsupport_subset hfV.2.2, ← energy_eq_of_tsupport_subset hf.2.2] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.trans h2.symm)

/-- Density: `covVec U Φ` is a limit of gradients of `C_c^∞(U)` functions. -/
theorem exists_tendsto_gradFeat_covVec (U : Opens ℂ) (Φ : TestOn upperHalfPlaneOpens) :
    ∃ f : ℕ → zsSub (U : Set ℂ),
      Tendsto (fun n => gradFeat (U : Set ℂ) (f n).1) atTop (𝓝 (covVec U Φ)) := by
  have hmem : (⟨covVec U Φ, covVec_mem _ _⟩ : gradClosure (U : Set ℂ) (zeroSpace U)) ∈
      closure (range (gradLin U)) := denseRange_gradLin U _
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
  choose f hf using hv
  refine ⟨f, ?_⟩
  have := (continuous_subtype_val.tendsto _).comp hlim
  refine this.congr fun n => ?_
  simp only [Function.comp_apply, ← hf n]
  rfl

/-! ### The Markov projection as an `L²` limit -/

section Variance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The second moment of a pairing of the zero-boundary GFF on `U` (extended by zero) is the
squared norm of its Gram vector. -/
theorem integral_sq_of_isZBGFFExtOn {U : Opens ℂ} (hUH : (U : Set ℂ) ⊆ H)
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : GFF.IsZBGFFExtOn U upperHalfPlaneOpens X P)
    (φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, (X ω φ) ^ 2 ∂P = ‖covVec U φ‖ ^ 2 := by
  have hm : AEMeasurable (fun ω => X ω φ) P :=
    ((measurable_distOn_apply φ).comp hX.measurable).aemeasurable
  rw [← variance_of_integral_eq_zero hm (hX.centered φ), ← covariance_self hm,
    hX.covariance_eq φ φ,
    GFF.zeroGFFTestCov_indicator U φ.continuous φ.hasCompactSupport φ.continuous
      φ.hasCompactSupport,
    zeroGFFTestCov_eq_inner_covVec U.isOpen hUH, real_inner_self_eq_norm_sq]

/-- `E|h_U(Φ) − (h, f)_∇|² = ‖covVec U Φ − ∇f‖²` for the Markov decomposition on `U ⊆ ℍ`. -/
theorem ae_markov_sub_lapTest_eq {U : Opens ℂ}
    (hU : U ≤ upperHalfPlaneOpens) {h hU' : Ω → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h hU' P)
    (Φ : TestOn upperHalfPlaneOpens) (f : zsSub (U : Set ℂ)) :
    ∀ᵐ ω ∂P, hU' ω Φ - h ω (lapTest U f) = hU' ω (Φ - lapTest U f) := by
  filter_upwards [ae_isHarmonicDistOn_of_isMarkovDecomposition hU hd] with ω hω
  have h0 := IsHarmonicDistOn.apply_lapTest_eq_zero U.isOpen hω hU subset_rfl f
  rw [sub_apply] at h0
  rw [map_sub]
  linarith

theorem memLp_markov_sub_lapTest {U : Opens ℂ}
    (hU : U ≤ upperHalfPlaneOpens) {h hU' : Ω → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h hU' P)
    (Φ : TestOn upperHalfPlaneOpens) (f : zsSub (U : Set ℂ)) :
    MemLp (fun ω => hU' ω Φ - h ω (lapTest U f)) 2 P :=
  ((hd.isZBGFFExtOn.gaussian.hasGaussianLaw_eval (Φ - lapTest U f)).memLp_two).ae_eq
    ((ae_markov_sub_lapTest_eq hU hd Φ f).mono fun _ hω => hω.symm)

lemma covVec_zero (V : Set ℂ) (hV : IsOpen V) (hVH : V ⊆ H) :
    covVec V ⇑(0 : TestOn upperHalfPlaneOpens) = 0 := by
  have := covVec_sub hV hVH (0 : TestOn upperHalfPlaneOpens) 0
  rw [sub_self, sub_self] at this
  exact this

theorem integral_sq_sub_lapTest_of_isMarkovDecomposition {U : Opens ℂ}
    (hU : U ≤ upperHalfPlaneOpens) {h hU' : Ω → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h hU' P)
    (Φ : TestOn upperHalfPlaneOpens) (f : zsSub (U : Set ℂ)) :
    ∫ ω, (hU' ω Φ - h ω (lapTest U f)) ^ 2 ∂P = ‖covVec U Φ - gradFeat U f.1‖ ^ 2 := by
  have hae : ∀ᵐ ω ∂P, (hU' ω Φ - h ω (lapTest U f)) ^ 2 = (hU' ω (Φ - lapTest U f)) ^ 2 := by
    filter_upwards [ae_markov_sub_lapTest_eq hU hd Φ f] with ω hω
    rw [hω]
  rw [integral_congr_ae hae, integral_sq_of_isZBGFFExtOn hU hd.isZBGFFExtOn,
    covVec_sub U.isOpen hU, covVec_lapTest hU U.isOpen hU subset_rfl]

/-- The Markov projection `h_U(Φ)` is the `L²` limit of Dirichlet pairings `(h, f_n)_∇`. -/
theorem exists_tendsto_integral_sq_of_isMarkovDecomposition {U : Opens ℂ}
    (hU : U ≤ upperHalfPlaneOpens) {h hU' : Ω → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h hU' P)
    (Φ : TestOn upperHalfPlaneOpens) :
    ∃ f : ℕ → zsSub (U : Set ℂ),
      Tendsto (fun n => gradFeat (U : Set ℂ) (f n).1) atTop (𝓝 (covVec U Φ)) ∧
      Tendsto (fun n => ∫ ω, (hU' ω Φ - h ω (lapTest U (f n))) ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨f, hf⟩ := exists_tendsto_gradFeat_covVec U Φ
  refine ⟨f, hf, ?_⟩
  simp_rw [integral_sq_sub_lapTest_of_isMarkovDecomposition hU hd]
  have : Tendsto (fun n => covVec U Φ - gradFeat (U : Set ℂ) (f n).1) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := covVec U Φ)).sub hf
  simpa using (continuous_norm.tendsto _ |>.comp this).pow 2

end Variance

/-! ### The variance as a supremum, and monotone Dirichlet-space approximation -/

/-- The Dirichlet energy of a function, on all of `ℂ`. -/
def energyC (f : ℂ → ℝ) : ℝ := (2 * Real.pi)⁻¹ * ∫ z, ‖fderiv ℝ f z‖ ^ 2

lemma zeroGFFTestCov_self_nonneg {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H)
    (φ : TestOn upperHalfPlaneOpens) : 0 ≤ zeroGFFTestCov V φ φ := by
  rw [zeroGFFTestCov_eq_inner_covVec hV hVH, real_inner_self_eq_norm_sq]
  positivity

/-- **The variance as a supremum**: `σ²_V(φ) = sup_f (∫ φ f)² / E(f)` over `f ∈ C_c^∞(V)` of positive
energy (any open `V ⊆ ℍ`, any test function `φ` on `ℍ`). -/
theorem ofReal_zeroGFFTestCov_eq_iSup {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H)
    (φ : TestOn upperHalfPlaneOpens) :
    ENNReal.ofReal (zeroGFFTestCov V φ φ) =
      ⨆ f ∈ {f | f ∈ zeroSpace V ∧ 0 < energyC f},
        ENNReal.ofReal ((∫ z, φ z * f z) ^ 2 / energyC f) := by
  have hEV : ∀ f ∈ zeroSpace V, dirichletEnergyOn V f = energyC f := fun f hf =>
    energy_eq_of_tsupport_subset hf.2.2
  have hnorm : ∀ f ∈ zeroSpace V, ‖gradFeat V f‖ ^ 2 = energyC f := fun f hf => by
    rw [norm_gradFeat_sq ((isDNSpace_zeroSpace V).smooth f hf)
      ((isDNSpace_zeroSpace V).energy f hf), hEV f hf]
  have hint : ∀ f ∈ zeroSpace V, ∫ z in V, φ z * f z = ∫ z, φ z * f z := fun f hf =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport fun h' => hz (hf.2.2 h'), mul_zero]
  rw [zeroGFFTestCov_eq_inner_covVec hV hVH, real_inner_self_eq_norm_sq]
  set c := covVec V ⇑φ
  by_cases hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g
  · have hpair : ∀ f ∈ zeroSpace V, ⟪c, gradFeat V f⟫ = ∫ z, φ z * f z := fun f hf => by
      rw [← hint f hf]
      exact inner_covVec_gradFeat hV hVH (toTestFunH φ) hpos hf
    refine le_antisymm ?_ (iSup₂_le fun f hf => ?_)
    · by_cases hc : c = 0
      · rw [hc, norm_zero]; simp
      have hmem : (⟨c, covVec_mem _ _⟩ : gradClosure V (zeroSpace V)) ∈
          closure (range (gradLin (⟨V, hV⟩ : Opens ℂ))) := denseRange_gradLin _ _
      obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
      choose f hf using hv
      have hg : Tendsto (fun n => gradFeat V (f n).1) atTop (𝓝 c) := by
        have := (continuous_subtype_val.tendsto _).comp hlim
        refine this.congr fun n => ?_
        simp only [Function.comp_apply, ← hf n]
        rfl
      have hcpos : 0 < ‖c‖ ^ 2 := by positivity
      have hq : Tendsto (fun n => ⟪c, gradFeat V (f n).1⟫ ^ 2 / ‖gradFeat V (f n).1‖ ^ 2) atTop
          (𝓝 (‖c‖ ^ 2)) := by
        have h1 : Tendsto (fun n => ⟪c, gradFeat V (f n).1⟫ ^ 2) atTop (𝓝 (⟪c, c⟫ ^ 2)) :=
          (tendsto_const_nhds.inner hg).pow 2
        have h2 : Tendsto (fun n => ‖gradFeat V (f n).1‖ ^ 2) atTop (𝓝 (‖c‖ ^ 2)) :=
          ((continuous_norm.tendsto _).comp hg).pow 2
        have := h1.div h2 hcpos.ne'
        rwa [real_inner_self_eq_norm_sq, show (‖c‖ ^ 2) ^ 2 / ‖c‖ ^ 2 = ‖c‖ ^ 2 by
          field_simp] at this
      refine le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp hq) ?_
      filter_upwards [hg.eventually_ne hc] with n hn
      have hfV : (f n).1 ∈ zeroSpace V := (f n).2
      have hE : 0 < energyC (f n).1 := by
        rw [← hnorm _ hfV]
        exact pow_pos (norm_pos_iff.2 hn) 2
      refine le_iSup₂_of_le (f n).1 ⟨hfV, hE⟩ (le_of_eq ?_)
      simp only [Function.comp_apply]
      rw [hpair _ hfV, hnorm _ hfV]
    · obtain ⟨hfV, hE⟩ := hf
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← hpair f hfV, ← hnorm f hfV]
      have hg0 : 0 < ‖gradFeat V f‖ ^ 2 := by rw [hnorm f hfV]; exact hE
      rw [div_le_iff₀ hg0]
      have := abs_real_inner_le_norm c (gradFeat V f)
      calc ⟪c, gradFeat V f⟫ ^ 2 = |⟪c, gradFeat V f⟫| ^ 2 := (sq_abs _).symm
        _ ≤ (‖c‖ * ‖gradFeat V f‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = ‖c‖ ^ 2 * ‖gradFeat V f‖ ^ 2 := mul_pow _ _ _
  · have hc0 : c = 0 := eq_zero_of_mem_gradClosure_of_nopos (isDNSpace_zeroSpace V) hpos
      (covVec_mem V _)
    rw [hc0, norm_zero]
    refine le_antisymm (by simp) (iSup₂_le fun f hf => ?_)
    exact absurd ⟨f, hf.1, by rw [hEV f hf.1]; exact hf.2⟩ hpos

/-- **Monotone Dirichlet-space approximation** (specification p. 50): for open
`U₀ ⊆ U₁ ⊆ ⋯ ⊆ ℍ`, `σ²_{U n}(φ) → σ²_{⋃ U n}(φ)`. -/
theorem tendsto_zeroGFFTestCov_iUnion {U : ℕ → Set ℂ} (hU : ∀ n, IsOpen (U n))
    (hmono : Monotone U) (hUH : ∀ n, U n ⊆ H) (φ : TestOn upperHalfPlaneOpens) :
    Tendsto (fun n => zeroGFFTestCov (U n) φ φ) atTop
      (𝓝 (zeroGFFTestCov (⋃ n, U n) φ φ)) := by
  have hUo : IsOpen (⋃ n, U n) := isOpen_iUnion hU
  have hUH' : (⋃ n, U n) ⊆ H := iUnion_subset hUH
  have hkey : ENNReal.ofReal (zeroGFFTestCov (⋃ n, U n) φ φ) =
      ⨆ n, ENNReal.ofReal (zeroGFFTestCov (U n) φ φ) := by
    simp_rw [ofReal_zeroGFFTestCov_eq_iSup hUo hUH' φ, ofReal_zeroGFFTestCov_eq_iSup (hU _) (hUH _) φ]
    refine le_antisymm (iSup₂_le fun f hf => ?_) (iSup_le fun n => iSup₂_le fun f hf => ?_)
    · obtain ⟨n, hn⟩ := hf.1.2.1.isCompact.elim_directed_cover U hU hf.1.2.2
        hmono.directed_le
      exact le_iSup_of_le n (le_iSup₂_of_le f ⟨⟨hf.1.1, hf.1.2.1, hn⟩, hf.2⟩ le_rfl)
    · exact le_iSup₂_of_le f ⟨⟨hf.1.1, hf.1.2.1, hf.1.2.2.trans (subset_iUnion U n)⟩, hf.2⟩ le_rfl
  have hmono' : Monotone fun n => ENNReal.ofReal (zeroGFFTestCov (U n) φ φ) := by
    intro m n hmn
    simp only
    rw [ofReal_zeroGFFTestCov_eq_iSup (hU m) (hUH m) φ, ofReal_zeroGFFTestCov_eq_iSup (hU n) (hUH n) φ]
    exact iSup₂_le fun f hf =>
      le_iSup₂_of_le f ⟨⟨hf.1.1, hf.1.2.1, hf.1.2.2.trans (hmono hmn)⟩, hf.2⟩ le_rfl
  have hlim := tendsto_atTop_iSup hmono'
  rw [← hkey] at hlim
  have := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hlim
  rw [ENNReal.toReal_ofReal (zeroGFFTestCov_self_nonneg hUo hUH' φ)] at this
  refine this.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (zeroGFFTestCov_self_nonneg (hU n) (hUH n) φ)]

/-! ### Uniqueness of the Markov projection -/

/-- **The projection onto `H(U)` is unique**: two Markov decompositions of the same field on `U ⊆ ℍ`
have almost surely equal zero-boundary parts (both are the `L²` limit of the same Dirichlet
pairings). -/
theorem ae_eq_of_isMarkovDecomposition {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens) {h hU₁ hU₂ : Ω → DistOn upperHalfPlaneOpens}
    (hd₁ : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h hU₁ P)
    (hd₂ : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h hU₂ P) : hU₁ =ᵐ[P] hU₂ := by
  have hΦ : ∀ Φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, hU₁ ω Φ = hU₂ ω Φ := by
    intro Φ
    obtain ⟨f, hf⟩ := exists_tendsto_gradFeat_covVec U Φ
    have hZ : ∀ n, MemLp (fun ω => hU₁ ω Φ - hU₂ ω Φ) 2 P := fun n => by
      have := (memLp_markov_sub_lapTest hU hd₁ Φ (f n)).sub
        (memLp_markov_sub_lapTest hU hd₂ Φ (f n))
      refine this.congr_norm ?_ ?_
      · exact ((measurable_distOn_apply Φ).comp hd₁.isZBGFFExtOn.measurable).aestronglyMeasurable.sub
          ((measurable_distOn_apply Φ).comp hd₂.isZBGFFExtOn.measurable).aestronglyMeasurable
      · exact Eventually.of_forall fun ω => by simp
    have hbound : ∀ n, ∫ ω, (hU₁ ω Φ - hU₂ ω Φ) ^ 2 ∂P ≤
        4 * ‖covVec U Φ - gradFeat (U : Set ℂ) (f n).1‖ ^ 2 := by
      intro n
      have i1 := (memLp_markov_sub_lapTest hU hd₁ Φ (f n)).integrable_sq
      have i2 := (memLp_markov_sub_lapTest hU hd₂ Φ (f n)).integrable_sq
      calc ∫ ω, (hU₁ ω Φ - hU₂ ω Φ) ^ 2 ∂P ≤
          ∫ ω, (2 * (hU₁ ω Φ - h ω (lapTest U (f n))) ^ 2 +
            2 * (hU₂ ω Φ - h ω (lapTest U (f n))) ^ 2) ∂P := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
              ((i1.const_mul 2).add (i2.const_mul 2)) (Eventually.of_forall fun ω => ?_)
            nlinarith [sq_nonneg ((hU₁ ω Φ - h ω (lapTest U (f n))) +
              (hU₂ ω Φ - h ω (lapTest U (f n))))]
        _ = 4 * ‖covVec U Φ - gradFeat (U : Set ℂ) (f n).1‖ ^ 2 := by
            rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul,
              integral_const_mul, integral_sq_sub_lapTest_of_isMarkovDecomposition hU hd₁,
              integral_sq_sub_lapTest_of_isMarkovDecomposition hU hd₂]
            ring
    have hlim : Tendsto (fun n => 4 * ‖covVec U Φ - gradFeat (U : Set ℂ) (f n).1‖ ^ 2) atTop
        (𝓝 0) := by
      have : Tendsto (fun n => covVec U Φ - gradFeat (U : Set ℂ) (f n).1) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := covVec U Φ)).sub hf
      simpa using ((continuous_norm.tendsto _ |>.comp this).pow 2).const_mul 4
    have h0 : ∫ ω, (hU₁ ω Φ - hU₂ ω Φ) ^ 2 ∂P = 0 :=
      le_antisymm (ge_of_tendsto' hlim hbound)
        (integral_nonneg fun ω => sq_nonneg _)
    have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _)
      (hZ 0).integrable_sq).1 h0
    filter_upwards [hae] with ω hω
    have : (hU₁ ω Φ - hU₂ ω Φ) ^ 2 = 0 := hω
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ × ℕ, hU₁ ω (distGen upperHalfPlaneOpens j) =
      hU₂ ω (distGen upperHalfPlaneOpens j) := ae_all_iff.2 fun j => hΦ _
  filter_upwards [hall] with ω hω
  exact injective_distOn_pairings upperHalfPlaneOpens (funext hω)

end LocalSets
end InteractingSLE
