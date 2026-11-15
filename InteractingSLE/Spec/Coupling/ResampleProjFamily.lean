import InteractingSLE.Spec.Coupling.ResampleProjChain

/-!
# Projection independence by Gaussian resampling: the protected kernels and the finite families (Theorem 1.1)

Packet PROVE-T11-PROJ (Astra §1, pp. 5–6, (1.9)–(1.10)).

* `ae_integral_couplingMean_mul_lapTest_eq_zero` : at a protected stop the coupling mean annihilates the Dirichlet
  directions of the protected region (the mixture of the protected Gaussian laws is the time-zero field law, whose mean
  `𝔥₀` is harmonic; a characteristic-function argument for the tested mean);
* `isShiftLaw_secMeas_of_protected` : the integrated protected kernels satisfy the Gaussian shift rule;
* `exists_stageChainProj` : PROVE-T11-KER's `exists_stageChain` run through `exists_chainProj`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

namespace InteractingSLE

namespace Coupling

open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovHarm GFF LocalSets QuantumZipper.K3 QuantumZipper.Thm11Asm Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-! ### Covers -/

section Cover

variable {V : Opens ℂ} {P' : Measure Ω} [IsFiniteMeasure P']

omit [IsFiniteMeasure P'] in
theorem secMeas_empty {X : Type*} [MeasurableSpace X] (η : Kernel Ω X) : secMeas P' (∅ : Set Ω) η = 0 := by
  rw [secMeas, Measure.restrict_empty, Measure.compProd_zero_left, Measure.map_zero]

/-- Projection independence on the pieces of a finite disjoint cover gives it on the union. -/
theorem isProjIndepMeasure_secMeas_of_cover {η : Kernel Ω (DistOn upperHalfPlaneOpens)} [IsMarkovKernel η]
    {J : Type*} [Fintype J] {A : Set Ω} {D : J → Set Ω} (hD : ∀ j, MeasurableSet (A ∩ D j))
    (hdisj : Pairwise (Function.onFun Disjoint fun j => A ∩ D j)) (hA : MeasurableSet A)
    (hcov : A ⊆ ⋃ j, A ∩ D j) (h : ∀ j, IsProjIndepMeasure V (secMeas P' (A ∩ D j) η)) :
    IsProjIndepMeasure V (secMeas P' A η) := by
  have hsum : secMeas P' A η = ∑ j, secMeas P' (A ∩ D j) η := by
    ext B hB
    rw [Measure.coe_finsetSum, Finset.sum_apply, secMeas_apply hA hB]
    simp_rw [secMeas_apply (hD _) hB]
    have hAeq : A = ⋃ j, A ∩ D j := Set.Subset.antisymm hcov (Set.iUnion_subset fun j => inter_subset_left)
    have hU : A ×ˢ B = ⋃ j, (A ∩ D j) ×ˢ B := by
      conv_lhs => rw [hAeq]
      exact Set.iUnion_prod_const
    rw [hU, measure_iUnion (fun i j hij => Set.disjoint_prod.2 (Or.inl (hdisj hij)))
      (fun j => (hD j).prod hB), tsum_fintype]
  intro f Ξ
  have hint : ∀ (Ψ : TestOn upperHalfPlaneOpens) (j : J), Integrable
      (fun x : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (x Ψ : ℂ)))
      (secMeas P' (A ∩ D j) η) := fun Ψ j =>
    Integrable.of_bound (measurable_exp_I_mul (measurable_distOn_apply Ψ)).aestronglyMeasurable 1
      (Eventually.of_forall fun x => (Complex.norm_exp_I_mul_ofReal _).le)
  rw [hsum, integral_finsetSum_measure fun j _ => hint _ j, integral_finsetSum_measure fun j _ => hint _ j,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => h j f Ξ

end Cover

/-! ### Protected kernels -/

section Protected

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
  (u : Ω → ℝ≥0 → ℂ → ℝ)
  (hu : ∀ ω s, IsBoundedHarmonicExtension
    (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
    (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
  {u₀ : ℂ → ℝ}
  (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
include hE hκ hu hu₀

/-- **The mean of a protected kernel annihilates the Dirichlet directions.** For a stopping time `s` of the usual
augmentation with `s < ζ` and `V ∩ K_s = ∅` almost surely, and `f ∈ C_c^∞(V)`, almost surely
`∫ 𝔥_s · (−Δf/2π) = 0`. Proof: by optional stopping (`integral_cfAt_eq_of_stoppingTime`) and since the Green energy
of `−Δf/2π` is `‖∇f‖²` at every protected time, `E[exp(iθ X)] = 1` for every `θ`, `X = ∫ 𝔥_s (−Δf/2π)`; hence the
law of `X` is `δ₀`. -/
theorem ae_integral_couplingMean_mul_lapTest_eq_zero {s : Ω → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (s ω : WithTop ℝ≥0))
    {V : Opens ℂ} (hVH : (V : Set ℂ) ⊆ H)
    (hsV : ∀ᵐ ω ∂P, (s ω : ℝ≥0∞) < ζ ω ∧ Disjoint (V : Set ℂ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s ω)))
    (f : zsSub (V : Set ℂ)) :
    ∀ᵐ ω ∂P, ∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (s ω) (u ω (s ω)) z * lapTest V f z = 0 := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hVH' : V ≤ upperHalfPlaneOpens := hVH
  set L := lapTest V f with hL
  have hLV : tsupport L ⊆ V := (tsupport_lapTest_subset hVH' f).trans f.2.2.2
  have hsψ : ∀ᵐ ω ∂P, (s ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (tsupport L) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s ω)) := by
    filter_upwards [hsV] with ω h
    exact ⟨h.1, h.2.mono_left hLV⟩
  set X : Ω → ℝ := fun ω => ∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (s ω) (u ω (s ω)) z * L z
    with hX
  have hXm : AEMeasurable X P := (aemeasurable_mean_energy_of_stoppingTime hE hκ u hu hs L hsψ).1
  set σ2 : ℝ := ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 with hσ2
  have hcoe : (toTestH V (cmTestOn f) : ℂ → ℝ) = cmTestOn f := coe_toTestH hVH (cmTestOn f)
  -- the Green energy of the Dirichlet direction at a protected time
  have hEn : ∀ᵐ ω ∂P, loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (s ω) L = σ2 := by
    filter_upwards [hsV, hE.2.2.2.2] with ω h hp
    have hw := continuousOn_rpath hp.2.2.2.1 h.1
    have h1 := zeroGFFTestCov_hullDom hw hp.1 hVH h.2 (cmTestOn f)
    rw [← hcoe] at h1
    have hD := hullDom_subset_H (W · ω) (s ω)
    rw [show toTestH V (cmTestOn f) = L from rfl] at h1
    rw [show (fun r : ℝ => W r.toNNReal ω) = rpath (W · ω) from rfl, ← h1,
      zeroGFFTestCov_eq_inner_covVec (hullDom (W · ω) (s ω)).isOpen hD, real_inner_self_eq_norm_sq,
      hL, covVec_lapTest hVH' (hullDom (W · ω) (s ω)).isOpen hD (le_hullDom hw hVH h.2) f,
      norm_gradFeat_eq (le_hullDom hw hVH h.2) f.2]
  have hG0 : greenEnergy0 L = σ2 := by
    rw [greenEnergy0_eq_zeroGFFTestCov, zeroGFFTestCov_eq_inner_covVec upperHalfPlaneOpens.isOpen subset_rfl,
      real_inner_self_eq_norm_sq, hL, covVec_lapTest hVH' upperHalfPlaneOpens.isOpen subset_rfl hVH f,
      norm_gradFeat_eq (V := (upperHalfPlaneOpens : Set ℂ)) hVH f.2]
  have hu0 : ∫ z, u₀ z * L z = 0 := by
    rw [hL, coe_lapTest hVH']
    exact HarmLoc.integral_mul_cmTest_of_harmonic isOpen_H hu₀.1 (zsTest f.2) (f.2.2.2.trans hVH)
  -- `E[exp(iθX)] = 1`
  have hone : ∀ θ : ℝ, ∫ ω, Complex.exp (Complex.I * θ * (X ω : ℂ)) ∂P = 1 := by
    intro θ
    have hI := integral_cfAt_eq_of_stoppingTime hE hκ u hu hu₀ L hs hsψ θ
    rw [hu0, hG0] at hI
    have hcf : ∀ᵐ ω ∂P, cfAt κ W u L θ s ω = Complex.exp (Complex.I * θ * (X ω : ℂ)) *
        Complex.exp (-(θ : ℂ) ^ 2 * (σ2 : ℂ) / 2) := by
      filter_upwards [hEn] with ω h
      rw [cfAt, h, ← Complex.exp_add]
      congr 1
      ring
    rw [integral_congr_ae hcf, integral_mul_const] at hI
    have hne : Complex.exp (-(θ : ℂ) ^ 2 * (σ2 : ℂ) / 2) ≠ 0 := Complex.exp_ne_zero _
    have e2 : Complex.exp (Complex.I * θ * ((0 : ℝ) : ℂ) - (θ : ℂ) ^ 2 * (σ2 : ℂ) / 2) =
        Complex.exp (-(θ : ℂ) ^ 2 * (σ2 : ℂ) / 2) := by
      congr 1; push_cast; ring
    rw [e2] at hI
    exact mul_right_cancel₀ hne (hI.trans (one_mul _).symm)
  -- the law of `X` is `δ₀`
  have hlaw : P.map X = Measure.dirac 0 := by
    refine Measure.ext_of_charFun (funext fun θ => ?_)
    rw [charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero, charFun_apply_real,
      integral_map hXm (by fun_prop)]
    rw [← hone θ]
    congr 1
    funext ω
    congr 1
    ring
  have hae : ∀ᵐ x ∂(P.map X), x = 0 := by
    rw [hlaw, ae_dirac_eq]
    exact Filter.eventually_pure.2 rfl
  exact (ae_map_iff hXm (measurableSet_singleton 0)).1 hae

/-- **The protected kernels satisfy the Gaussian shift rule**, integrated over every event. -/
theorem isShiftLaw_secMeas_of_protected {s : Ω → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (s ω : WithTop ℝ≥0))
    {V : Opens ℂ} (hVH : (V : Set ℂ) ⊆ H)
    (hsV : ∀ᵐ ω ∂P, (s ω : ℝ≥0∞) < ζ ω ∧ Disjoint (V : Set ℂ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s ω)))
    {Q : Kernel Ω (DistOn V)} [IsMarkovKernel Q]
    (hQcf : ∀ᵐ ω ∂P, ∀ ψ : TestOn V,
      ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(Q ω) = cfAt κ W u ψ 1 s ω)
    {A : Set Ω} (hA : MeasurableSet A) : IsShiftLaw V (secMeas P A Q) := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  intro ψ f
  have hb : ∀ (φ : TestOn V) (g : DistOn V), ‖Complex.exp (Complex.I * (g φ : ℂ))‖ ≤ 1 := fun φ g =>
    (Complex.norm_exp_I_mul_ofReal _).le
  rw [integral_secMeas (measurable_exp_I_mul (measurable_distOn_apply _)) (hb _),
    integral_secMeas (measurable_exp_I_mul (measurable_distOn_apply _)) (hb _), ← integral_const_mul]
  refine setIntegral_congr_ae hA ?_
  filter_upwards [hQcf, hsV, hE.2.2.2.2,
    ae_integral_couplingMean_mul_lapTest_eq_zero hE hκ u hu hu₀ hs hVH hsV f] with ω hcf h hp hm _
  rw [hcf, hcf]
  have hw := continuousOn_rpath hp.2.2.2.1 h.1
  set D := hullDom (W · ω) (s ω) with hDdef
  have hD : (D : Set ℂ) ⊆ H := hullDom_subset_H _ _
  have hVD : V ≤ D := le_hullDom hw hVH h.2
  set m := meanDist κ (W · ω) (s ω) (u ω (s ω)) V with hmdef
  have hM : ∀ φ : TestOn V,
      ∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (s ω) (u ω (s ω)) z * φ z = m φ := fun φ =>
    (meanDist_apply κ hw (hu ω (s ω)).1 hVH h.2 φ).symm
  have hEn : ∀ φ : TestOn V, loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (s ω) φ =
      ‖covVec (D : Set ℂ) (toTestH V φ)‖ ^ 2 := fun φ => by
    rw [show (fun r : ℝ => W r.toNNReal ω) = rpath (W · ω) from rfl,
      ← zeroGFFTestCov_hullDom hw hp.1 hVH h.2 φ, ← coe_toTestH hVH φ,
      zeroGFFTestCov_eq_inner_covVec D.isOpen hD, real_inner_self_eq_norm_sq]
  have hm0 : m (cmTestOn f) = 0 := by
    rw [← hM, ← coe_toTestH hVH (cmTestOn f), toTestH_cmTestOn]
    exact hm
  simp only [cfAt]
  rw [hM, hM, hEn, hEn, map_sub m ψ (cmTestOn f), hm0, sub_zero,
    show toTestH V (ψ - cmTestOn f) = toTestH V ψ - lapTest V f from map_sub _ ψ (cmTestOn f),
    norm_covVec_sub_lapTest_sq D.isOpen hD hVD f, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Protected

/-! ### The stage chain with resampling -/

section StageChain

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
  (u : Ω → ℝ≥0 → ℂ → ℝ)
  (hu : ∀ ω s, IsBoundedHarmonicExtension
    (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
    (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
  {u₀ : ℂ → ℝ}
  (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
include hE hκ hu hu₀

/-- **The stage chain with resampling**: PROVE-T11-KER's `exists_stageChain` (the protected stage kernels and one
field kernel with the field marginal `fieldLaw0 u₀` and the stage restriction laws), run through `exists_chainProj`, so
that the field kernel is in addition projection-independent at every stage region on every event of the stage
σ-algebra inside that region. -/
theorem exists_stageChainProj {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : ι → TopologicalSpace.Opens ℂ) (hUH : ∀ i, U i ≤ upperHalfPlaneOpens) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ i ω : WithTop ℝ≥0))
    (hτU : ∀ i, ∀ᵐ ω ∂P, (τ i ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (U i : Set ℂ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (τ i ω))) :
    ∃ (Q : ℕ → (T : Finset ι) → Kernel Ω (DistOn (unionOpens U T))),
      (∀ k T, IsMarkovKernel (Q k T)) ∧
      (∀ k T, ∀ᵐ ω ∂P, ∀ ψ : TestOn (unionOpens U T),
        ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(Q k T ω) = cfAt κ W u ψ 1 (stageStop τ k T) ω) ∧
      ∃ η : Kernel Ω (DistOn upperHalfPlaneOpens), IsMarkovKernel η ∧
        (∀ S, MeasurableSet S → ∫⁻ ω, η ω S ∂P = fieldLaw0 u₀ S) ∧
        (∀ k, 1 ≤ k → k ≤ Fintype.card ι → ∀ T,
          RectAgree (isStoppingTime_ordStat hτ k).measurableSpace P {ω | stageSet τ k ω = T}
            (η.map (restrictDist (unionOpens U T))) (Q k T)) ∧
        ∀ k, 1 ≤ k → k ≤ Fintype.card ι → ∀ T A,
          MeasurableSet[(isStoppingTime_ordStat hτ k).measurableSpace] A → A ⊆ {ω | stageSet τ k ω = T} →
            IsProjIndepMeasure (unionOpens U T) (secMeas P A η) := by
  classical
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hσ := isStoppingTime_ordStat (𝓖 := usualAugmentation 𝓕 P) hτ
  have hρ := isStoppingTime_stageStop (𝓖 := usualAugmentation 𝓕 P) hτ
  set V := unionOpens U with hVdef
  have hVH : ∀ T, V T ≤ upperHalfPlaneOpens := unionOpens_le U hUH
  have hr : ∀ T, Measurable (restrictDist (V T) (D := upperHalfPlaneOpens)) := fun T =>
    measurable_restrictDist (V T)
  -- protection at the stage stops
  have hprot : ∀ k T, ∀ᵐ ω ∂P, (stageStop τ k T ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (V T : Set ℂ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (stageStop τ k T ω)) := by
    intro k T
    filter_upwards [ae_all_iff.2 hτU] with ω hω
    obtain ⟨i₀, hi₀⟩ := ordStat_le_exists τ k ω
    refine ⟨lt_of_le_of_lt (by exact_mod_cast (stageStop_le_ordStat k T ω).trans hi₀) (hω i₀).1, ?_⟩
    rw [hVdef, coe_unionOpens]
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    simp only [mem_iUnion] at hz
    obtain ⟨i, hi, hzU⟩ := hz
    have hzH : z ∈ H := hUH i hzU
    have hzi : z ∈ H \ fwdHull (fun r : ℝ => W r.toNNReal ω) (τ i ω) :=
      ⟨hzH, fun h => (hω i).2.ne_of_mem hzU h rfl⟩
    exact (mem_diff_fwdHull_of_le hzi (by exact_mod_cast stageStop_le_of_mem k hi ω)).2 hzK
  choose Q hQM hQcf using fun k T => exists_protectedKernel hE hκ u hu (hρ k T)
    (show (V T : Set ℂ) ⊆ H from hVH T) (hprot k T)
  refine ⟨Q, hQM, hQcf, ?_⟩
  -- the stage σ-algebras
  let 𝒜 : ℕ → MeasurableSpace Ω := fun k => match k with
    | 0 => ⊥
    | k + 1 => (hσ (k + 1)).measurableSpace
  have h𝒜s : ∀ k, 𝒜 (k + 1) = (hσ (k + 1)).measurableSpace := fun k => rfl
  have h𝒜 : Monotone 𝒜 := by
    intro a b hab
    rcases a with _ | a
    · exact bot_le
    · rcases b with _ | b
      · omega
      · exact (hσ (a + 1)).measurableSpace_mono (hσ (b + 1)) fun ω =>
          WithTop.coe_le_coe.2 (ordStat_mono hab ω)
  have h𝒜m : ∀ k, 𝒜 k ≤ mΩ := by
    intro k
    rcases k with _ | k
    · exact bot_le
    · exact (hσ (k + 1)).measurableSpace_le
  have hlt : ∀ k j, MeasurableSet[𝒜 (k + 1)] {ω | ordStat τ (k + 1) ω < τ j ω} := by
    intro k j
    have h := (hτ j).measurableSet_stopping_time_le (hσ (k + 1))
    have : {ω | ordStat τ (k + 1) ω < τ j ω} =
        {ω | (τ j ω : WithTop ℝ≥0) ≤ (ordStat τ (k + 1) ω : WithTop ℝ≥0)}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_le_coe, not_le]
    rw [this]
    exact h.compl
  have hconst : ∀ (k : ℕ) (T : Finset ι), MeasurableSet[𝒜 k] {_ω : Ω | (Finset.univ : Finset ι) = T} :=
    fun k T => by
      by_cases h : (Finset.univ : Finset ι) = T
      · simp only [h, ofPred_true]; exact @MeasurableSet.univ Ω (𝒜 k)
      · simp only [h, ofPred_false]; exact @MeasurableSet.empty Ω (𝒜 k)
  have hR : ∀ k T, MeasurableSet[𝒜 k] {ω | stageSet τ (k + 1) ω = T} := by
    intro k T
    rcases k with _ | k
    · exact hconst 0 T
    · have : {ω | stageSet τ (k + 2) ω = T} =
          ⋂ j, {ω | (ordStat τ (k + 1) ω < τ j ω ↔ j ∈ T)} := by
        ext ω
        simp only [stageSet, mem_ofPred_eq, mem_iInter, Finset.ext_iff, Finset.mem_filter,
          Finset.mem_univ, true_and]
      rw [this]
      refine MeasurableSet.iInter fun j => ?_
      by_cases hj : j ∈ T
      · simp only [hj, iff_true]; exact hlt k j
      · simp only [hj, iff_false]; exact (hlt k j).compl
  have hR0 : ∀ T, MeasurableSet[𝒜 0] {ω | stageSet τ 0 ω = T} := fun T => hconst 0 T
  have hbot : ∀ {A : Set Ω}, MeasurableSet[𝒜 0] A → A = ∅ ∨ A = univ := fun hA =>
    MeasurableSpace.measurableSet_bot_iff.1 hA
  -- (1.8) between consecutive stages
  have hmart : ∀ k T, RectAgree (𝒜 k) P {ω | stageSet τ (k + 1) ω = T} (Q (k + 1) T) (Q k T) := by
    intro k T A hA hAE B hB
    have := hQM k T
    have := hQM (k + 1) T
    have hA' : MeasurableSet[(hρ k T).measurableSpace] A := by
      rcases k with _ | k
      · rcases hbot hA with rfl | rfl
        · exact @MeasurableSet.empty Ω (hρ 0 T).measurableSpace
        · exact @MeasurableSet.univ Ω (hρ 0 T).measurableSpace
      · have h1 := (hσ (k + 1)).measurableSet_inter_le (hρ (k + 1) T) A hA
        have hAeq : A ∩ {ω | (ordStat τ (k + 1) ω : WithTop ℝ≥0) ≤ (stageStop τ (k + 1) T ω : WithTop ℝ≥0)}
            = A := by
          refine inter_eq_left.2 fun ω hω => ?_
          have hT := hAE hω
          simp only [mem_ofPred_eq] at hT
          rw [mem_ofPred_eq, WithTop.coe_le_coe, stageStop_eq_ordStat fun i hi => ?_]
          rw [← hT] at hi
          simp only [stageSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact (ordStat_mono (Nat.le_succ _) ω).trans (ordStat_succ_le_of_lt hi)
        rw [hAeq] at h1
        refine measurableSet_stopping_congr rfl ?_ _ (hρ (k + 1) T) h1
        funext ω
        exact min_eq_right (WithTop.coe_le_coe.2 (stageStop_le_ordStat _ T ω))
    exact compProd_prod_eq_of_protected hE hκ u hu (hρ k T) (hρ (k + 1) T)
      (fun ω => stageStop_mono (Nat.le_succ k) T ω) (show (V T : Set ℂ) ⊆ H from hVH T)
      (hprot (k + 1) T) (hQcf k T) (hQcf (k + 1) T) hA' hB
  -- consistency of the kernels of nested regions at the same stage
  have hcons : ∀ k T T', T ⊆ T' → RectAgree (𝒜 k) P
      ({ω | stageSet τ k ω = T'} ∩ {ω | stageSet τ (k + 1) ω = T})
      ((Q k T').map (restrictDist (V T))) (Q k T) := by
    intro k T T' hTT'
    have := hQM k T
    have := hQM k T'
    have hrT : Measurable (restrictDist (V T) (D := V T')) := measurable_restrictDist (V T)
    have := Kernel.IsMarkovKernel.map (Q k T') hrT
    refine RectAgree.of_ae_eq (h𝒜m k) ?_
    filter_upwards [hQcf k T', hQcf k T] with ω h1 h2 hω
    rw [Kernel.map_apply _ hrT]
    refine eq_of_integral_cexp fun ψ => ?_
    rw [integral_cexp_map_restrictDist, h1, h2]
    have hst : stageStop τ k T' ω = stageStop τ k T ω := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [stageStop_zero, stageStop_zero]
      · have hle : ∀ i ∈ T', ordStat τ k ω ≤ τ i ω := fun i hi => by
          rw [← hω.1] at hi
          exact ordStat_le_of_mem_stageSet hk hi
        rw [stageStop_eq_ordStat hle, stageStop_eq_ordStat fun i hi => hle i (hTT' hi)]
    rw [coe_testIncl (unionOpens_mono U hTT') ψ]
    exact cfAt_congr u 1 hst
  -- the start
  set η₀ : Kernel Ω (DistOn upperHalfPlaneOpens) := Kernel.const Ω (fieldLaw0 u₀) with hη₀
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have h0 : ∀ T, RectAgree (𝒜 0) P {ω | stageSet τ 0 ω = T}
      (η₀.map (restrictDist (V T))) (Q 0 T) := by
    intro T A hA hAE B hB
    have := hQM 0 T
    have := Kernel.IsMarkovKernel.map η₀ (hr T)
    rcases hbot hA with rfl | rfl
    · simp
    refine compProd_prod_eq_of_setIntegral_cexp MeasurableSet.univ (fun ψ => ?_) hB
    rw [setIntegral_univ, setIntegral_univ]
    have hψ' : (toTestH (V T) ψ : ℂ → ℝ) = ψ := coe_toTestH (hVH T) ψ
    have hτs : ∀ᵐ ω ∂P, (stageStop τ 0 T ω : ℝ≥0∞) < ζ ω ∧
        Disjoint (tsupport (toTestH (V T) ψ)) (fwdHull (fun s : ℝ => W s.toNNReal ω) (stageStop τ 0 T ω)) := by
      filter_upwards [hprot 0 T] with ω h
      refine ⟨h.1, h.2.mono_left ?_⟩
      rw [hψ']
      exact ψ.tsupport_subset
    have hI := integral_cfAt_eq_of_stoppingTime hE hκ u hu hu₀ (toTestH (V T) ψ) (hρ 0 T) hτs 1
    rw [hψ'] at hI
    rw [integral_congr_ae ((hQcf 0 T).mono fun ω h => h ψ), hI]
    have hconst : ∀ ω, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂((η₀.map (restrictDist (V T))) ω) =
        Complex.exp (Complex.I * ((∫ z, u₀ z * (toTestH (V T) ψ) z : ℝ) : ℂ) -
          (zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) (toTestH (V T) ψ) (toTestH (V T) ψ) : ℂ) / 2) :=
      fun ω => by
        rw [Kernel.map_apply _ (hr T), hη₀, Kernel.const_apply, integral_cexp_map_restrictDist,
          integral_cexp_fieldLaw0 hu₀c]
    simp_rw [hconst]
    have hg : greenEnergy0 ⇑ψ = zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ := by
      rw [← hψ', greenEnergy0_eq_zeroGFFTestCov]
    rw [integral_const, probReal_univ, one_smul, hψ', hg]
    congr 1
    push_cast
    ring
  -- the Gaussian shift rule of the stage kernels
  have hshift : ∀ k T A, MeasurableSet[𝒜 k] A → A ⊆ {ω | stageSet τ k ω = T} →
      IsShiftLaw (V T) (secMeas P A (Q k T)) := fun k T A hA _ => by
    have := hQM k T
    exact isShiftLaw_secMeas_of_protected hE hκ u hu hu₀ (hρ k T) (hVH T) (hprot k T) (hQcf k T)
      (h𝒜m k A hA)
  obtain ⟨η, hηM, -, hmarg, hinv, hproj⟩ := exists_chainProj P V hVH (fun T T' h => unionOpens_mono U h)
    𝒜 h𝒜 h𝒜m (stageSet τ) hR0 hR stageSet_succ_subset Q (hQ := hQM) hu₀.1 h0 hmart hcons hshift
    (Fintype.card ι)
  refine ⟨η, hηM, fun S hS => ?_, fun k hk hkN T => ?_, fun k hk hkN T A hA hAT => ?_⟩
  · have h := hmarg univ (@MeasurableSet.univ Ω (𝒜 0)) subset_rfl S hS
    rw [Measure.compProd_apply_prod MeasurableSet.univ hS,
      Measure.compProd_apply_prod MeasurableSet.univ hS] at h
    simp only [Measure.restrict_univ, Kernel.const_apply, lintegral_const, measure_univ,
      mul_one] at h
    exact h
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
    exact hinv (k' + 1) hkN T
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
    exact hproj (k' + 1) hkN T A hA hAT

/-- **Finite families of protected pairs: one coupling with projection independence** (Astra §1, (1.10), both
halves). As PROVE-T11-KER's `exists_finiteFamilyKernel`, and in addition, for every pair, the field law integrated over
every event of `𝓖_{τ i}` is projection-independent at `U i` (`P_{U_i} h ⫫ (h − P_{U_i} h, 𝓖_{τ_i})`). For
finitely many open `U i ⊆ ℍ` and stopping times `τ i` of the usual augmentation with `τ i < ζ` and
`U i ∩ K_{τ i} = ∅` almost surely, there is a Markov kernel `η : Ω → 𝒟'(ℍ)` (the field given the driving history)
whose field marginal is `fieldLaw0 u₀` (the law of `𝔥₀ + h⁰`) and which satisfies, for every pair, every test
function `ψ` supported in `U i` and every `A ∈ 𝓖_{τ i}`,
`∫_A ∫ exp(i h(ψ)) dη dP = ∫_A exp(i (𝔥_{τ i}, ψ) − E_{τ i}(ψ)/2) dP`. -/
theorem exists_finiteFamilyKernelProj {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : ι → TopologicalSpace.Opens ℂ) (hUH : ∀ i, U i ≤ upperHalfPlaneOpens) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ i ω : WithTop ℝ≥0))
    (hτU : ∀ i, ∀ᵐ ω ∂P, (τ i ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (U i : Set ℂ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (τ i ω))) :
    ∃ η : Kernel Ω (DistOn upperHalfPlaneOpens), IsMarkovKernel η ∧
      (∀ S, MeasurableSet S → ∫⁻ ω, η ω S ∂P = fieldLaw0 u₀ S) ∧
      (∀ i (ψ : TestOn upperHalfPlaneOpens), tsupport ψ ⊆ U i → ∀ A,
        MeasurableSet[(hτ i).measurableSpace] A →
          ∫ ω in A, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(η ω) ∂P =
            ∫ ω in A, cfAt κ W u ψ 1 (τ i) ω ∂P) ∧
      ∀ i A, MeasurableSet[(hτ i).measurableSpace] A → IsProjIndepMeasure (U i) (secMeas P A η) := by
  classical
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  obtain ⟨Q, hQM, hQcf, η, hηM, hmarg, hstage, hproj⟩ :=
    exists_stageChainProj hE hκ u hu hu₀ U hUH τ hτ hτU
  have hboth : ∀ i A, MeasurableSet[(hτ i).measurableSpace] A →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U i →
        ∫ ω in A, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(η ω) ∂P =
          ∫ ω in A, cfAt κ W u ψ 1 (τ i) ω ∂P) ∧ IsProjIndepMeasure (U i) (secMeas P A η) := by
    intro i A hA
    have hσ := isStoppingTime_ordStat (𝓖 := usualAugmentation 𝓕 P) hτ
    set N := Fintype.card ι with hN
    set V := unionOpens U with hVdef
    have hVH : ∀ T, V T ≤ upperHalfPlaneOpens := unionOpens_le U hUH
    have hA' : MeasurableSet A := (hτ i).measurableSpace_le A hA
    -- the stage pieces
    set G : ℕ → Set Ω := fun m => {ω | ordStat τ (m + 1) ω = τ i ω ∧
      (m = 0 ∨ ordStat τ m ω < ordStat τ (m + 1) ω)} with hG
    set D : Fin N × Finset ι → Set Ω := fun j => G j.1 ∩ {ω | stageSet τ (j.1 + 1) ω = j.2} with hD
    -- measurability of the pieces of `A` in the stage σ-algebra
    have hpiece : ∀ j : Fin N × Finset ι,
        MeasurableSet[(hσ (j.1 + 1)).measurableSpace] (A ∩ D j) := by
      intro j
      set m := (j.1 : ℕ)
      have h1 : MeasurableSet[(hσ (m + 1)).measurableSpace]
          (A ∩ {ω | (τ i ω : WithTop ℝ≥0) ≤ (ordStat τ (m + 1) ω : WithTop ℝ≥0)}) :=
        ((hτ i).min (hσ (m + 1))).measurableSpace_mono (hσ (m + 1)) (fun ω => min_le_right _ _) _
          ((hτ i).measurableSet_inter_le (hσ (m + 1)) A hA)
      have h2 := (hσ (m + 1)).measurableSet_le_stopping_time (hτ i)
      have h3 : MeasurableSet[(hσ (m + 1)).measurableSpace]
          {ω | m = 0 ∨ ordStat τ m ω < ordStat τ (m + 1) ω} := by
        rcases Nat.eq_zero_or_pos m with hm0 | hm0
        · simp only [hm0, true_or, ofPred_true]; exact @MeasurableSet.univ Ω _
        · have h4 := (hσ (m + 1)).measurableSet_le_stopping_time (hσ m)
          have : {ω | m = 0 ∨ ordStat τ m ω < ordStat τ (m + 1) ω} =
              {ω | (ordStat τ (m + 1) ω : WithTop ℝ≥0) ≤ (ordStat τ m ω : WithTop ℝ≥0)}ᶜ := by
            ext ω
            simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_le_coe, not_le, Nat.pos_iff_ne_zero.1 hm0,
              false_or]
          rw [this]; exact h4.compl
      have h5 := measurableSet_stageSet_succ hτ m j.2
      have hset : A ∩ D j = (A ∩ {ω | (τ i ω : WithTop ℝ≥0) ≤ (ordStat τ (m + 1) ω : WithTop ℝ≥0)}) ∩
          {ω | (ordStat τ (m + 1) ω : WithTop ℝ≥0) ≤ (τ i ω : WithTop ℝ≥0)} ∩
          {ω | m = 0 ∨ ordStat τ m ω < ordStat τ (m + 1) ω} ∩ {ω | stageSet τ (m + 1) ω = j.2} := by
        ext ω
        simp only [hD, hG, mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe]
        constructor
        · intro h
          exact ⟨⟨⟨⟨h.1, h.2.1.1.ge⟩, h.2.1.1.le⟩, h.2.1.2⟩, h.2.2⟩
        · intro h
          exact ⟨h.1.1.1.1, ⟨le_antisymm h.1.1.2 h.1.1.1.2, h.1.2⟩, h.2⟩
      rw [hset]
      exact ((h1.inter h2).inter h3).inter h5
    have hpiece' : ∀ j : Fin N × Finset ι, MeasurableSet (A ∩ D j) := fun j =>
      (hσ ((j.1 : ℕ) + 1)).measurableSpace_le _ (hpiece j)
    -- the pieces are disjoint and cover `A`
    have hGdisj : ∀ m m', m < m' → ∀ ω, ω ∈ G m → ω ∉ G m' := by
      intro m m' hmm' ω h h'
      rcases h'.2 with h0 | hlt
      · omega
      · have := ordStat_mono (τ := τ) (show m + 1 ≤ m' by omega) ω
        rw [h.1, ← h'.1] at this
        exact absurd hlt (not_lt.2 this)
    have hdisj : Pairwise (Function.onFun Disjoint fun j : Fin N × Finset ι => A ∩ D j) := by
      intro j j' hjj'
      refine Set.disjoint_left.2 fun ω h h' => hjj' ?_
      have hm : (j.1 : ℕ) = j'.1 := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · exact hGdisj _ _ hlt ω h.2.1 h'.2.1
        · exact hGdisj _ _ hlt ω h'.2.1 h.2.1
      have hm' : j.1 = j'.1 := Fin.ext hm
      refine Prod.ext hm' ?_
      have e1 := h.2.2
      have e2 := h'.2.2
      simp only [mem_ofPred_eq] at e1 e2
      rw [← e1, ← e2, hm]
    have hcov : A ⊆ ⋃ j : Fin N × Finset ι, A ∩ D j := by
      intro ω hω
      obtain ⟨m, hmN, heq, hlt⟩ := exists_ordStat_eq (τ := τ) i ω
      refine mem_iUnion.2 ⟨(⟨m, by omega⟩, stageSet τ (m + 1) ω), hω, ⟨heq, ?_⟩, rfl⟩
      rcases hlt with h0 | hlt
      · exact Or.inl h0
      · exact Or.inr (heq ▸ hlt)
    -- membership of `i` in the stage region
    have hiT : ∀ m ω, ω ∈ G m → i ∈ stageSet τ (m + 1) ω := by
      intro m ω hω
      rcases m with _ | m
      · exact Finset.mem_univ i
      · simp only [stageSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hω.2 with h0 | hlt
        · omega
        · rw [← hω.1]; exact hlt
    refine ⟨fun ψ hψU => ?_, ?_⟩
    swap
    · -- projection independence, piece by piece
      refine isProjIndepMeasure_secMeas_of_cover hpiece' hdisj hA' hcov fun j => ?_
      set m := (j.1 : ℕ) with hmdef
      by_cases hiT' : i ∈ j.2
      · have hUV : U i ≤ V j.2 := le_biSup U hiT'
        exact (hproj (m + 1) (by omega) (by omega) j.2 (A ∩ D j) (hpiece j) (fun ω hω => hω.2.2)).mono
          (hVH j.2) hUV
      · have hempty : A ∩ D j = ∅ := by
          ext ω
          simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
          intro _ hω
          exact hiT' (hω.2 ▸ hiT m ω hω.1)
        rw [hempty, secMeas_empty]
        exact isProjIndepMeasure_zero
    -- integrability
    have hfm : Measurable fun g : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (g ψ : ℂ)) :=
      measurable_exp_I_mul (measurable_distOn_apply ψ)
    have hfint : IntegrableOn (fun ω => ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(η ω)) A P := by
      refine (Integrable.of_bound ?_ 1 (Eventually.of_forall fun ω => ?_)).integrableOn
      · exact ((hfm.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right'
          (κ := η)).aestronglyMeasurable
      · refine (norm_integral_le_of_norm_le_const (C := 1)
          (Eventually.of_forall fun g => (Complex.norm_exp_I_mul_ofReal _).le)).trans ?_
        simp
    have hτs : ∀ᵐ ω ∂P, (τ i ω : ℝ≥0∞) < ζ ω ∧
        Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ i ω)) := by
      filter_upwards [hτU i] with ω h
      exact ⟨h.1, h.2.mono_left hψU⟩
    have hgint : IntegrableOn (fun ω => cfAt κ W u ψ 1 (τ i) ω) A P := by
      refine (Integrable.of_bound (aestronglyMeasurable_cfAt_of_stoppingTime hE hκ u hu ψ (hτ i) hτs 1)
        1 ?_).integrableOn
      filter_upwards [hτs, hE.2.2.2.2] with ω h hp
      refine norm_cfAt_le_one u 1 ψ (continuousOn_rpath hp.2.2.2.1 h.1) hp.1 fun z hz => ?_
      exact exists_isForwardSol_of_mem (τ i ω).coe_nonneg
        ⟨tsupport_subset_H ψ hz, fun hzK => h.2.ne_of_mem hz hzK rfl⟩
    refine setIntegral_eq_of_partition hpiece' hdisj hA' hcov hfint hgint fun j => ?_
    rw [inter_eq_right.2 inter_subset_left]
    set m := (j.1 : ℕ) with hmdef
    by_cases hiT' : i ∈ j.2
    · have hUV : U i ≤ V j.2 := le_biSup U hiT'
      set ψT : TestOn (V j.2) := testRestrict ψ (hψU.trans hUV) with hψT
      have := hQM (m + 1) j.2
      have hrT : Measurable (restrictDist (V j.2) (D := upperHalfPlaneOpens)) := measurable_restrictDist _
      have := Kernel.IsMarkovKernel.map η hrT
      have hf : ∀ ω, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(η ω) =
          ∫ g, Complex.exp (Complex.I * (g ψT : ℂ)) ∂((η.map (restrictDist (V j.2))) ω) := fun ω => by
        rw [Kernel.map_apply _ hrT, integral_cexp_map_restrictDist, hψT,
          testIncl_testRestrict (hVH j.2)]
      simp_rw [hf]
      rw [RectAgree.setIntegral_cexp_eq (hσ (m + 1)).measurableSpace_le
        (hstage (m + 1) (by omega) (by omega) j.2) (hpiece j) (fun ω hω => hω.2.2) ψT,
        setIntegral_congr_ae (hpiece' j) ((hQcf (m + 1) j.2).mono fun ω h _ => h ψT)]
      refine setIntegral_congr_fun (hpiece' j) fun ω hω => ?_
      have hT : stageSet τ (m + 1) ω = j.2 := hω.2.2
      have hst : stageStop τ (m + 1) j.2 ω = τ i ω := by
        rw [stageStop_eq_ordStat fun i' hi' => ordStat_le_of_mem_stageSet (by omega) (hT ▸ hi')]
        exact hω.2.1.1
      rw [cfAt_congr u 1 hst]
      rfl
    · have hempty : A ∩ D j = ∅ := by
        ext ω
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        intro _ hω
        exact hiT' (hω.2 ▸ hiT m ω hω.1)
      rw [hempty, Measure.restrict_empty, integral_zero_measure, integral_zero_measure]

  refine ⟨η, hηM, hmarg, fun i ψ hψU A hA => (hboth i A hA).1 ψ hψU, fun i A hA => (hboth i A hA).2⟩

end StageChain

end Coupling

end InteractingSLE
