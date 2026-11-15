import InteractingSLE.GFF.LocalSets.GermExchange
import LQGMetric.Field.MarkovGauss
import LQGMetric.Field.MarkovExt
import LQGMetric.Papers.DFGPS.ZBBridge
import QuantumZipper.Proofs.GFF.LateralGerm

/-!
# The germ zero-one law for the zero-boundary GFF (toward Proposition 3.2)

Source: `source/ig1-specification.pdf`, §3.1, proof of Proposition 3.2 (pp. 43–44; transcription
`source/spec/p001-048.md#prop-3.2-proof`): "decreasing closed Gaussian subspaces give the
corresponding intersection of sigma-algebras", specification graph node
`SPEC.prop-3.2#decreasing-gaussian-intersection`.

Let `X` be a zero-boundary GFF on an open `V ⊆ D` extended by zero to `D` (`IsZBGFFExtOn V D X P`;
in Proposition 3.2, `X = h_V` with `V = D ∖ K`), and `U₀ ⊇ U₁ ⊇ ⋯` open subsets of `D` that every
compact subset of `V` eventually avoids (`Uₙ = D ∩ {dist(·, K) < 1/(n+1)}`). Then the germ
σ-algebra `⋂ₙ σ(X|_{Uₙ})` is trivial (`IsZBGFFExtOn.isTrivialSigma_iInf_restrictSigma`). This
is the input `htriv` of `exists_ae_eq_complSigma_of_mem_iInf_restrictSigma` (`GermExchange.lean`).

## Proof (own argument; Hilbert-space form of the source's)

All pairings `X(φ)` lie in one Gaussian Hilbert space `𝒦 ⊆ L²(P)`; `𝒦ₙ ⊆ 𝒦` is the closed span of
the pairings with test functions supported in `Uₙ`.

1. *Riesz vectors.* With `v_φ = rieszFun V (1_V φ) ∈ H₀¹(V)` (LQGMetric), the covariance is
   `⟪X(φ), X(ψ)⟫ = ⟪v_φ, v_ψ⟫` and `v_{Δ̃f} = ∇f` for `f ∈ C_c^∞(V)`, `Δ̃f = −Δf/2π`.
2. *Density.* `‖X(φ) − X(Δ̃fₖ)‖ = ‖v_φ − ∇fₖ‖`, so the Dirichlet pairings `X(Δ̃f)`, `f ∈ C_c^∞(V)`,
   span a dense subspace of `𝒦` (`IsZBGFFExtOn.vec_mem_lapSpace`).
3. *Orthogonality.* `⟪X(φ), X(Δ̃f)⟫ = ∫ f φ = 0` when `supp φ ∩ supp f = ∅`; hence `X(Δ̃f) ⊥ 𝒦ₙ`
   for large `n`, and `⋂ 𝒦ₙ ⊥ 𝒦`, i.e. `⋂ 𝒦ₙ = 0`; the projections `Πₙ` onto `𝒦ₙ` tend to `0`
   strongly (QuantumZipper `exists_tendsto_starProjection_antitone`).
4. *Independence.* `X(ψ) − Πₙ X(ψ) ⊥ 𝒦ₙ` is independent of `σ(X|_{Uₙ})` (Janson: orthogonal
   jointly Gaussian families are independent, LQGMetric `indepFun_of_inner_eq_zero`) and tends to
   `X(ψ)` almost surely along a subsequence, so the germ σ-algebra is independent of every finite
   family `(X(ψ))_{ψ ∈ J}` (QuantumZipper `indep_comap_of_tendsto_ae`), hence of `σ(X)`, which
   contains it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped RealInnerProductSpace ENNReal
open QuantumZipper QuantumZipper.K3 LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovExt
  LQGMetric.MarkovGauss LQGMetric.MarkovHarm QuantumZipper.GermZeroOne

namespace InteractingSLE
namespace GFF

/-! ### Riesz vectors of `1_V φ` -/

section Riesz

variable {V D : Opens ℂ}

/-- `(1_V φ)⁺ dz` is admissible on `V` for `φ ∈ 𝓓(D)`, `V ⊆ D`. -/
lemma isAdmissibleDual_testMeasPos_indicator (hD : ZBAdmissible D) (hVD : V ≤ D)
    (φ : TestOn D) :
    IsAdmissibleDual V (zeroSpace V) (testMeasPos ((V : Set ℂ).indicator φ)) := by
  obtain ⟨⟨hfin, -, hnorm⟩, -⟩ := hD φ
  rw [testMeasPos_indicator V.isOpen.measurableSet]
  refine ⟨inferInstance, ⟨tsupport φ ∩ closure V,
    φ.hasCompactSupport.isCompact.inter_right isClosed_closure, inter_subset_right, ?_⟩, ?_⟩
  · rw [Measure.restrict_apply' V.isOpen.measurableSet]
    refine measure_mono_null (fun x hx => ?_) (testMeasPos_compl_tsupport φ)
    exact fun h => hx.1 ⟨h, subset_closure hx.2⟩
  · rw [← dualNormSq_zeroSpace_restrict V.isOpen]
    exact (dualNormSq_zeroSpace_mono V.isOpen hVD).trans_lt hnorm

/-- `(1_V φ)⁻ dz` is admissible on `V` for `φ ∈ 𝓓(D)`, `V ⊆ D`. -/
lemma isAdmissibleDual_testMeasNeg_indicator (hD : ZBAdmissible D) (hVD : V ≤ D)
    (φ : TestOn D) :
    IsAdmissibleDual V (zeroSpace V) (testMeasNeg ((V : Set ℂ).indicator φ)) := by
  obtain ⟨-, ⟨hfin, -, hnorm⟩⟩ := hD φ
  rw [testMeasNeg_indicator V.isOpen.measurableSet]
  refine ⟨inferInstance, ⟨tsupport φ ∩ closure V,
    φ.hasCompactSupport.isCompact.inter_right isClosed_closure, inter_subset_right, ?_⟩, ?_⟩
  · rw [Measure.restrict_apply' V.isOpen.measurableSet]
    refine measure_mono_null (fun x hx => ?_) (testMeasNeg_compl_tsupport φ)
    exact fun h => hx.1 ⟨h, subset_closure hx.2⟩
  · rw [← dualNormSq_zeroSpace_restrict V.isOpen]
    exact (dualNormSq_zeroSpace_mono V.isOpen hVD).trans_lt hnorm

/-- The covariance of `IsZBGFFExtOn V D` as an inner product of Riesz vectors in `H₀¹(V)`. -/
lemma zeroGFFTestCov_indicator_eq_inner (hD : ZBAdmissible D) (hVD : V ≤ D) (φ ψ : TestOn D) :
    zeroGFFTestCov V ((V : Set ℂ).indicator φ) ((V : Set ℂ).indicator ψ) =
      ⟪rieszFun V ((V : Set ℂ).indicator φ), rieszFun V ((V : Set ℂ).indicator ψ)⟫ :=
  (inner_rieszFun ⟨isAdmissibleDual_testMeasPos_indicator hD hVD φ,
    isAdmissibleDual_testMeasNeg_indicator hD hVD φ⟩
    ⟨isAdmissibleDual_testMeasPos_indicator hD hVD ψ,
    isAdmissibleDual_testMeasNeg_indicator hD hVD ψ⟩).symm

/-- The Riesz vector of the Dirichlet test function `Δ̃f = −Δf/2π`, `f ∈ C_c^∞(V)`, is `∇f`
(Green's identity, LQGMetric `zbRiesz_cmTestOn'`). -/
lemma rieszFun_indicator_cmTestOn (hD : ZBAdmissible D) (hVD : V ≤ D) (f : zsSub (V : Set ℂ)) :
    rieszFun V ((V : Set ℂ).indicator (testIncl V D (cmTestOn f))) = gradFeat V f := by
  rw [coe_testIncl hVD, indicator_testOn]
  exact DFGPS.zbRiesz_cmTestOn' (zbAdmissible_mono hVD hD) f

/-- `⟪v_φ, ∇f⟫ = ∫ f φ = 0` when `f φ ≡ 0`. -/
lemma inner_rieszFun_indicator_gradFeat_eq_zero (hD : ZBAdmissible D) (hVD : V ≤ D)
    (φ : TestOn D) {f : ℂ → ℝ} (hf : f ∈ zeroSpace V) (hfφ : ∀ x, f x * φ x = 0) :
    ⟪rieszFun V ((V : Set ℂ).indicator φ), gradFeat V f⟫ = 0 := by
  have hDN := isDNSpace_zeroSpace (V : Set ℂ)
  by_cases hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g
  · have hfD : f ∈ zeroSpace D := ⟨hf.1, hf.2.1, hf.2.2.trans hVD⟩
    have hV := V.isOpen.measurableSet
    have hfin : IsFiniteMeasure (testMeasPos (φ : ℂ → ℝ)) := (hD φ).1.1
    have hfin' : IsFiniteMeasure (testMeasNeg (φ : ℂ → ℝ)) := (hD φ).2.1
    have hres : ∀ μ : Measure ℂ, ∫ x, f x ∂(μ.restrict V) = ∫ x, f x ∂μ := fun μ =>
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h' => hx (hf.2.2 h')
    rw [rieszFun, inner_sub_left,
      pair_rieszVec hDN (isAdmissibleDual_testMeasPos_indicator hD hVD φ) hpos f hf,
      pair_rieszVec hDN (isAdmissibleDual_testMeasNeg_indicator hD hVD φ) hpos f hf,
      testMeasPos_indicator hV, testMeasNeg_indicator hV, hres, hres,
      integral_mul_test_eq φ hfD]
    simp [hfφ]
  · rw [eq_zero_of_mem_gradClosure_of_nopos hDN hpos (rieszFun_mem V _), inner_zero_left]

end Riesz

/-! ### The pairings in `L²(P)` -/

section Process

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {V D : Opens ℂ} {X : Ω → DistOn D}

/-- The pairing process `φ ↦ X(φ)` of a random distribution. -/
abbrev fieldProc (X : Ω → DistOn D) (φ : TestOn D) : Ω → ℝ := fun ω => X ω φ

omit [IsProbabilityMeasure P] in
lemma IsZBGFFExtOn.memLp_fieldProc (hX : IsZBGFFExtOn V D X P) (φ : TestOn D) :
    MemLp (fieldProc X φ) 2 P :=
  (hX.gaussian.hasGaussianLaw_eval φ).memLp_two

/-- The `L²` class `[X(φ)]`. -/
abbrev IsZBGFFExtOn.vec (hX : IsZBGFFExtOn V D X P) (φ : TestOn D) : Lp ℝ 2 P :=
  (hX.memLp_fieldProc φ).toLp (fieldProc X φ)

lemma IsZBGFFExtOn.inner_vec (hX : IsZBGFFExtOn V D X P) (φ ψ : TestOn D) :
    ⟪hX.vec φ, hX.vec ψ⟫ =
      zeroGFFTestCov V ((V : Set ℂ).indicator φ) ((V : Set ℂ).indicator ψ) := by
  rw [inner_toLp_eq_cov _ _ (hX.centered φ)]
  exact hX.covariance_eq φ ψ

/-- `‖X(φ) − X(Δ̃f)‖_{L²(P)} = ‖v_φ − ∇f‖_{H₀¹(V)}`. -/
lemma IsZBGFFExtOn.norm_vec_sub_cmTestOn (hX : IsZBGFFExtOn V D X P) (hD : ZBAdmissible D)
    (hVD : V ≤ D) (φ : TestOn D) (f : zsSub (V : Set ℂ)) :
    ‖hX.vec φ - hX.vec (testIncl V D (cmTestOn f))‖ =
      ‖rieszFun V ((V : Set ℂ).indicator φ) - gradFeat V f‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  set a := hX.vec φ
  set b := hX.vec (testIncl V D (cmTestOn f))
  set v := rieszFun V ((V : Set ℂ).indicator φ)
  set w := gradFeat (V : Set ℂ) f
  have hw : rieszFun V ((V : Set ℂ).indicator (testIncl V D (cmTestOn f))) = w :=
    rieszFun_indicator_cmTestOn hD hVD f
  have h1 : ⟪a, a⟫ = ⟪v, v⟫ := by
    rw [hX.inner_vec, zeroGFFTestCov_indicator_eq_inner hD hVD]
  have h2 : ⟪a, b⟫ = ⟪v, w⟫ := by
    rw [hX.inner_vec, zeroGFFTestCov_indicator_eq_inner hD hVD, hw]
  have h3 : ⟪b, b⟫ = ⟪w, w⟫ := by
    rw [hX.inner_vec, zeroGFFTestCov_indicator_eq_inner hD hVD, hw]
  rw [norm_sub_sq_real, norm_sub_sq_real, ← real_inner_self_eq_norm_sq a,
    ← real_inner_self_eq_norm_sq b, ← real_inner_self_eq_norm_sq v,
    ← real_inner_self_eq_norm_sq w, h1, h2, h3]

/-- `⟪X(φ), X(Δ̃f)⟫ = ∫ f φ = 0` when `f φ ≡ 0`. -/
lemma IsZBGFFExtOn.inner_vec_cmTestOn_eq_zero (hX : IsZBGFFExtOn V D X P)
    (hD : ZBAdmissible D) (hVD : V ≤ D) (φ : TestOn D) (f : zsSub (V : Set ℂ))
    (hfφ : ∀ x, f.1 x * φ x = 0) : ⟪hX.vec φ, hX.vec (testIncl V D (cmTestOn f))⟫ = 0 := by
  rw [hX.inner_vec, zeroGFFTestCov_indicator_eq_inner hD hVD, rieszFun_indicator_cmTestOn hD hVD]
  exact inner_rieszFun_indicator_gradFeat_eq_zero hD hVD φ f.2 hfφ

/-- The closed span of the Dirichlet pairings `X(Δ̃f)`, `f ∈ C_c^∞(V)`. -/
def IsZBGFFExtOn.lapSpace (hX : IsZBGFFExtOn V D X P) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (range fun f : zsSub (V : Set ℂ) =>
    hX.vec (testIncl V D (cmTestOn f)))).topologicalClosure

/-- **Density of the Dirichlet pairings**: every `X(φ)`, `φ ∈ 𝓓(D)`, is an `L²` limit of
Dirichlet pairings `X(Δ̃fₖ)`, `fₖ ∈ C_c^∞(V)`. -/
theorem IsZBGFFExtOn.vec_mem_lapSpace (hX : IsZBGFFExtOn V D X P) (hD : ZBAdmissible D)
    (hVD : V ≤ D) (φ : TestOn D) : hX.vec φ ∈ hX.lapSpace := by
  set v : gradClosure (V : Set ℂ) (zeroSpace V) :=
    ⟨rieszFun V ((V : Set ℂ).indicator φ), rieszFun_mem V _⟩
  obtain ⟨g, hg, hlim⟩ := mem_closure_iff_seq_limit.1 (denseRange_gradLin V v)
  choose f hf using hg
  refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (b := atTop) (f := fun n =>
    hX.vec (testIncl V D (cmTestOn (f n)))) ?_ (Eventually.of_forall fun n =>
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f n, rfl⟩))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hn : ∀ n, ‖hX.vec (testIncl V D (cmTestOn (f n))) - hX.vec φ‖ = ‖g n - v‖ := by
    intro n
    rw [norm_sub_rev, hX.norm_vec_sub_cmTestOn hD hVD, ← hf n, norm_sub_rev]
    rfl
  simp_rw [hn]
  exact (tendsto_iff_norm_sub_tendsto_zero).1 hlim

/-! ### The germ subspaces `𝒦_U` -/

/-- The closed span `𝒦_U ⊆ L²(P)` of the pairings `X(φ)` with `supp φ ⊆ U`. -/
def IsZBGFFExtOn.germSpace (hX : IsZBGFFExtOn V D X P) (U : Opens ℂ) :
    Submodule ℝ (Lp ℝ 2 P) :=
  gaussSpace (fun b : TestOn U => fieldProc X (testIncl U D b))
    fun b => hX.memLp_fieldProc (testIncl U D b)

omit [IsProbabilityMeasure P] in
lemma IsZBGFFExtOn.germSpace_le_gaussSpace (hX : IsZBGFFExtOn V D X P) (U : Opens ℂ) :
    hX.germSpace U ≤ gaussSpace (fieldProc X) hX.memLp_fieldProc :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (range_subset_iff.2 fun b =>
    ⟨testIncl U D b, rfl⟩))

lemma testIncl_testIncl_eq {U' U D : Opens ℂ} (hU'U : U' ≤ U) (hUD : U ≤ D) (b : TestOn U') :
    testIncl U D (testIncl U' U b) = testIncl U' D b :=
  TestFunction.ext fun x => by
    rw [coe_testIncl hUD, coe_testIncl hU'U, coe_testIncl (hU'U.trans hUD)]

omit [IsProbabilityMeasure P] in
lemma IsZBGFFExtOn.germSpace_mono (hX : IsZBGFFExtOn V D X P) {U' U : Opens ℂ} (hU'U : U' ≤ U)
    (hUD : U ≤ D) : hX.germSpace U' ≤ hX.germSpace U := by
  refine Submodule.topologicalClosure_mono (Submodule.span_mono (range_subset_iff.2 fun b =>
    ⟨testIncl U' U b, ?_⟩))
  show hX.vec (testIncl U D (testIncl U' U b)) = hX.vec (testIncl U' D b)
  rw [testIncl_testIncl_eq hU'U hUD]

omit [IsProbabilityMeasure P] in
lemma IsZBGFFExtOn.vec_mem_germSpace (hX : IsZBGFFExtOn V D X P) (U : Opens ℂ) (b : TestOn U) :
    hX.vec (testIncl U D b) ∈ hX.germSpace U :=
  toLp_mem_gaussSpace (fun b : TestOn U => hX.memLp_fieldProc (testIncl U D b)) b

omit [IsProbabilityMeasure P] in
instance IsZBGFFExtOn.completeSpace_germSpace (hX : IsZBGFFExtOn V D X P) (U : Opens ℂ) :
    CompleteSpace (hX.germSpace U) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- **The intersection of the germ subspaces is orthogonal to the Gaussian space.** If every
compact subset of `V` is eventually disjoint from `Uₙ`, then every `u ∈ ⋂ₙ 𝒦_{Uₙ}` is orthogonal
to every pairing `X(ψ)`. -/
theorem IsZBGFFExtOn.inner_vec_eq_zero_of_forall_mem (hX : IsZBGFFExtOn V D X P)
    (hD : ZBAdmissible D) (hVD : V ≤ D) {U : ℕ → Opens ℂ} (hUD : ∀ n, U n ≤ D)
    (hsep : ∀ C : Set ℂ, IsCompact C → C ⊆ V → ∃ n, Disjoint C (U n)) {u : Lp ℝ 2 P}
    (hu : ∀ n, u ∈ hX.germSpace (U n)) (ψ : TestOn D) : ⟪hX.vec ψ, u⟫ = 0 := by
  have hgen : ∀ f : zsSub (V : Set ℂ), ⟪hX.vec (testIncl V D (cmTestOn f)), u⟫ = 0 := by
    intro f
    obtain ⟨n, hn⟩ := hsep _ f.2.2.1.isCompact f.2.2.2
    have horth : hX.germSpace (U n) ≤ (ℝ ∙ hX.vec (testIncl V D (cmTestOn f)))ᗮ := by
      refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      refine hX.inner_vec_cmTestOn_eq_zero hD hVD _ f fun x => ?_
      rw [coe_testIncl (hUD n)]
      by_cases hx : x ∈ tsupport b
      · rw [image_eq_zero_of_notMem_tsupport fun h => Set.disjoint_left.1 hn h
          (b.tsupport_subset hx), zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    have := horth (hu n)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at this
    rw [real_inner_comm]
    exact this
  have hle : hX.lapSpace ≤ (ℝ ∙ u)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact hgen f
  have := hle (hX.vec_mem_lapSpace hD hVD ψ)
  rwa [Submodule.mem_orthogonal_singleton_iff_inner_left] at this

/-- **The projections onto the germ subspaces tend to `0`**: `Π_{𝒦_{Uₙ}} X(ψ) → 0` in `L²(P)`. -/
theorem IsZBGFFExtOn.tendsto_starProjection_germSpace (hX : IsZBGFFExtOn V D X P)
    (hD : ZBAdmissible D) (hVD : V ≤ D) {U : ℕ → Opens ℂ} (hU : Antitone U)
    (hUD : ∀ n, U n ≤ D)
    (hsep : ∀ C : Set ℂ, IsCompact C → C ⊆ V → ∃ n, Disjoint C (U n)) (ψ : TestOn D) :
    Tendsto (fun n => (hX.germSpace (U n)).starProjection (hX.vec ψ)) atTop (𝓝 0) := by
  obtain ⟨y, hy, hyK⟩ := exists_tendsto_starProjection_antitone (fun n => hX.germSpace (U n))
    (fun m n hmn => hX.germSpace_mono (hU hmn) (hUD m)) (hX.vec ψ)
  have hxy : ⟪hX.vec ψ, y⟫ = 0 := hX.inner_vec_eq_zero_of_forall_mem hD hVD hUD hsep hyK ψ
  have hproj : ∀ n, ⟪(hX.germSpace (U n)).starProjection (hX.vec ψ), y⟫ = ⟪hX.vec ψ, y⟫ := by
    intro n
    have h1 := Submodule.inner_left_of_mem_orthogonal (hyK n)
      (Submodule.sub_starProjection_mem_orthogonal (K := hX.germSpace (U n)) (hX.vec ψ))
    rw [inner_sub_left, sub_eq_zero] at h1
    exact h1.symm
  have hlim : Tendsto (fun n => ⟪(hX.germSpace (U n)).starProjection (hX.vec ψ), y⟫) atTop
      (𝓝 ⟪y, y⟫) := hy.inner tendsto_const_nhds
  simp_rw [hproj, hxy] at hlim
  have hy0 : y = 0 := inner_self_eq_zero.1 (tendsto_nhds_unique hlim tendsto_const_nhds)
  rwa [hy0] at hy

end Process

/-! ### Independence of the germ σ-algebra -/

section Indep

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {V D : Opens ℂ} {X : Ω → DistOn D}

omit mΩ [IsProbabilityMeasure P] in
/-- `σ(X|_U)` is generated by the pairings `X(φ)`, `supp φ ⊆ U`. -/
lemma restrictSigma_le_comap_pairings (U : Opens ℂ) (X : Ω → DistOn D) :
    restrictSigma U X ≤
      MeasurableSpace.comap (fun ω (b : TestOn U) => X ω (testIncl U D b)) inferInstance := by
  refine Measurable.comap_le ?_
  refine (@measurable_distOn_iff U Ω (MeasurableSpace.comap
    (fun ω (b : TestOn U) => X ω (testIncl U D b)) inferInstance) _).2 fun b => ?_
  exact (measurable_pi_apply b).comp (comap_measurable _)

omit mΩ [IsProbabilityMeasure P] in
lemma restrictSigma_le_comap_self (U : Opens ℂ) (X : Ω → DistOn D) :
    restrictSigma U X ≤ MeasurableSpace.comap X inferInstance :=
  LateralGerm.comap_le_comap_of_comp (F := X) (measurable_restrictDist U)

/-- `X(ψ) − Π_{𝒦_U} X(ψ)`, `ψ ∈ J`, is independent of `σ(X|_U)` (Janson). -/
theorem IsZBGFFExtOn.indep_comap_sub_starProjection (hX : IsZBGFFExtOn V D X P)
    (U : Opens ℂ) (J : Finset (TestOn D)) :
    Indep (MeasurableSpace.comap (fun ω (j : J) =>
      ((hX.vec j - (hX.germSpace U).starProjection (hX.vec j) : Lp ℝ 2 P) : Ω → ℝ) ω)
      inferInstance) (restrictSigma U X) P := by
  have hW : ∀ j : J, hX.vec j - (hX.germSpace U).starProjection (hX.vec j) ∈
      gaussSpace (fieldProc X) hX.memLp_fieldProc := fun j =>
    sub_mem (toLp_mem_gaussSpace hX.memLp_fieldProc j)
      (hX.germSpace_le_gaussSpace U (Submodule.coe_mem _))
  have horth : ∀ (j : J) (b : TestOn U), ⟪hX.vec j - (hX.germSpace U).starProjection (hX.vec j),
      (hX.memLp_fieldProc (testIncl U D b)).toLp (fieldProc X (testIncl U D b))⟫ = 0 :=
    fun j b => Submodule.inner_left_of_mem_orthogonal (hX.vec_mem_germSpace U b)
      (Submodule.sub_starProjection_mem_orthogonal _)
  have h := indepFun_of_inner_eq_zero (X := fieldProc X) hX.gaussian hX.centered
    hX.memLp_fieldProc (fun j : J => hX.vec j - (hX.germSpace U).starProjection (hX.vec j)) hW
    (testIncl U D) horth
  exact indep_of_indep_of_le_right ((IndepFun_iff_Indep _ _ _).1 h)
    (restrictSigma_le_comap_pairings U X)

omit [IsProbabilityMeasure P] in
lemma integral_sq_coeFn_eq_norm_sq (u : Lp ℝ 2 P) : ∫ ω, (u : Ω → ℝ) ω ^ 2 ∂P = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp [sq]

omit [IsProbabilityMeasure P] in
/-- Finitely many sequences tending to `0` in `L²` tend to `0` almost surely along one
subsequence. -/
lemma exists_subseq_ae_tendsto_zero {ι : Type*} [Fintype ι] {y : ℕ → ι → Lp ℝ 2 P}
    (hy : ∀ i, Tendsto (fun n => y n i) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, ∀ i, ∀ᵐ ω ∂P, Tendsto (fun k => (y (ns k) i : Ω → ℝ) ω) atTop (𝓝 0) := by
  have he : Tendsto (fun n => ∑ i, ‖y n i‖ ^ 2) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ =>
      ((continuous_norm.tendsto _).comp (hy i)).pow 2
    simpa using this
  have hk : ∀ k : ℕ, ∃ n, ∑ i, ‖y n i‖ ^ 2 < (1 / 2 : ℝ) ^ k := fun k =>
    (he.eventually (gt_mem_nhds (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k))).exists
  choose ns hns using hk
  refine ⟨ns, fun i => ?_⟩
  have hbd : ∀ k, ‖y (ns k) i‖ ^ 2 ≤ (1 / 2 : ℝ) ^ k := fun k =>
    (Finset.single_le_sum (f := fun i => ‖y (ns k) i‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i)).trans (hns k).le
  refine LateralGerm.ae_tendsto_zero_of_summable_sq
    (fun k => (Lp.aestronglyMeasurable _).aemeasurable)
    (fun k => (Lp.memLp (y (ns k) i)).integrable_sq) ?_
  simp_rw [integral_sq_coeFn_eq_norm_sq]
  exact Summable.of_nonneg_of_le (fun k => sq_nonneg _) hbd
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

/-- The germ σ-algebra `⋂ₙ σ(X|_{Uₙ})` is independent of every finite family of pairings. -/
theorem IsZBGFFExtOn.indep_iInf_restrictSigma_comap_finset (hX : IsZBGFFExtOn V D X P)
    (hD : ZBAdmissible D) (hVD : V ≤ D) {U : ℕ → Opens ℂ} (hU : Antitone U)
    (hUD : ∀ n, U n ≤ D)
    (hsep : ∀ C : Set ℂ, IsCompact C → C ⊆ V → ∃ n, Disjoint C (U n)) (J : Finset (TestOn D)) :
    Indep (⨅ n, restrictSigma (U n) X)
      (MeasurableSpace.comap (fun ω (j : J) => X ω j) inferInstance) P := by
  obtain ⟨ns, hns⟩ := exists_subseq_ae_tendsto_zero (P := P)
    (y := fun n (j : J) => (hX.germSpace (U n)).starProjection (hX.vec j))
    fun j => hX.tendsto_starProjection_germSpace hD hVD hU hUD hsep j
  have hle : (⨅ n, restrictSigma (U n) X) ≤ mΩ :=
    (iInf_le _ 0).trans (restrictSigma_le _ hX.measurable)
  refine LateralGerm.indep_comap_of_tendsto_ae hle
    (Y := fun k ω (j : J) =>
      ((hX.vec j - (hX.germSpace (U (ns k))).starProjection (hX.vec j) : Lp ℝ 2 P) : Ω → ℝ) ω)
    (fun k => measurable_pi_iff.2 fun j => (Lp.stronglyMeasurable _).measurable)
    (measurable_pi_iff.2 fun j => (measurable_distOn_apply (j : TestOn D)).comp hX.measurable)
    (fun k => (indep_of_indep_of_le_right (hX.indep_comap_sub_starProjection (U (ns k)) J)
      (iInf_le _ (ns k))).symm) ?_
  have h1 : ∀ j : J, ∀ᵐ ω ∂P, ∀ k,
      ((hX.vec j - (hX.germSpace (U (ns k))).starProjection (hX.vec j) : Lp ℝ 2 P) : Ω → ℝ) ω =
        X ω j - ((hX.germSpace (U (ns k))).starProjection (hX.vec j) : Ω → ℝ) ω := by
    intro j
    rw [ae_all_iff]
    intro k
    filter_upwards [Lp.coeFn_sub (hX.vec j) ((hX.germSpace (U (ns k))).starProjection (hX.vec j)),
      (hX.memLp_fieldProc j).coeFn_toLp] with ω e1 e2
    rw [e1, Pi.sub_apply, e2]
  filter_upwards [ae_all_iff.2 h1, ae_all_iff.2 hns] with ω e1 e2
  refine tendsto_pi_nhds.2 fun j => ?_
  simp_rw [e1 j]
  simpa using (tendsto_const_nhds (x := X ω j)).sub (e2 j)

/-- The germ σ-algebra `⋂ₙ σ(X|_{Uₙ})` is independent of `σ(X)`. -/
theorem IsZBGFFExtOn.indep_iInf_restrictSigma (hX : IsZBGFFExtOn V D X P)
    (hD : ZBAdmissible D) (hVD : V ≤ D) {U : ℕ → Opens ℂ} (hU : Antitone U)
    (hUD : ∀ n, U n ≤ D)
    (hsep : ∀ C : Set ℂ, IsCompact C → C ⊆ V → ∃ n, Disjoint C (U n)) :
    Indep (⨅ n, restrictSigma (U n) X) (MeasurableSpace.comap X inferInstance) P := by
  classical
  set m : Finset (TestOn D) → MeasurableSpace Ω := fun J =>
    MeasurableSpace.comap (fun ω (j : J) => X ω j) inferInstance
  have hmono : ∀ J₁ J₂ : Finset (TestOn D), J₁ ⊆ J₂ → m J₁ ≤ m J₂ := by
    intro J₁ J₂ hJ
    exact LateralGerm.comap_le_comap_of_comp (F := fun ω (j : J₂) => X ω j)
      (R := fun (g : J₂ → ℝ) (j : J₁) => g ⟨j, hJ j.2⟩)
      (measurable_pi_iff.2 fun j => measurable_pi_apply _)
  have hdir : Directed (· ≤ ·) m := fun J₁ J₂ =>
    ⟨J₁ ∪ J₂, hmono _ _ Finset.subset_union_left, hmono _ _ Finset.subset_union_right⟩
  have hle : (⨅ n, restrictSigma (U n) X) ≤ mΩ :=
    (iInf_le _ 0).trans (restrictSigma_le _ hX.measurable)
  have hmle : ∀ J, m J ≤ mΩ := fun J => by
    have : Measurable fun ω (j : J) => X ω j :=
      measurable_pi_iff.2 fun j => (measurable_distOn_apply (j : TestOn D)).comp hX.measurable
    exact this.comap_le
  have h := indep_iSup_of_directed_le
    (fun J => (hX.indep_iInf_restrictSigma_comap_finset hD hVD hU hUD hsep J).symm) hmle hle hdir
  refine (indep_of_indep_of_le_left h ?_).symm
  refine Measurable.comap_le ((@measurable_distOn_iff D Ω (⨆ J, m J) X).2 fun φ => ?_)
  have hφ : Measurable[m {φ}] fun ω => X ω φ :=
    (measurable_pi_apply (⟨φ, Finset.mem_singleton_self φ⟩ : ({φ} : Finset (TestOn D)))).comp
      (comap_measurable (fun ω (j : ({φ} : Finset (TestOn D))) => X ω j))
  exact hφ.mono (le_iSup m {φ}) le_rfl

/-- **The germ zero-one law for the zero-boundary GFF.** Let `X` be a zero-boundary GFF on the
open set `V ⊆ D` extended by zero to `D` (`D` admissible), and `U₀ ⊇ U₁ ⊇ ⋯` open subsets of `D`
such that every compact subset of `V` is disjoint from some `Uₙ`. Then the germ σ-algebra
`⋂ₙ σ(X|_{Uₙ})` is trivial. -/
theorem IsZBGFFExtOn.isTrivialSigma_iInf_restrictSigma (hX : IsZBGFFExtOn V D X P)
    (hD : ZBAdmissible D) (hVD : V ≤ D) {U : ℕ → Opens ℂ} (hU : Antitone U)
    (hUD : ∀ n, U n ≤ D)
    (hsep : ∀ C : Set ℂ, IsCompact C → C ⊆ V → ∃ n, Disjoint C (U n)) :
    IsTrivialSigma (⨅ n, restrictSigma (U n) X) P :=
  isTrivialSigma_of_indep_self (indep_of_indep_of_le_right
    (hX.indep_iInf_restrictSigma hD hVD hU hUD hsep)
    ((iInf_le _ 0).trans (restrictSigma_le_comap_self (U 0) X)))

end Indep

end GFF
end InteractingSLE
