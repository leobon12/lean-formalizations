import InteractingSLE.Spec.Coupling.ResampleOrder

/-!
# Finite families of protected pairs: one coupling (Theorem 1.1, obligation 3)

Packet PROVE-T11-KER (Astra §1, pp. 5–6, (1.9)–(1.10)). For finitely many protected pairs `(U i, τ i)` (open
`U i ⊆ ℍ`, stopping times `τ i < ζ` of the usual augmentation with `U i ∩ K_{τ i} = ∅`), `exists_finiteFamilyKernel`
gives one field kernel `η : Ω → 𝒟'(ℍ)` (the field sampled given the whole driving history) such that

* the field marginal `∫ η dP` is the law of `𝔥₀ + h⁰`, `h⁰` a zero-boundary GFF on `ℍ` (`fieldLaw0`);
* for every pair, every test function `ψ` supported in `U i` and every `A ∈ 𝓖_{τ i}`,
  `∫_A ∫ exp(i h(ψ)) dη dP = ∫_A exp(i (𝔥_{τ i}, ψ) − E_{τ i}(ψ)/2) dP` (the integrated protected-kernel constraint
  `IsSampledAt` of `StopFamily`, for the coupling `P ⊗ η`).

The stages are the order statistics of the `τ i` (`ResampleOrder`), the stage kernels the protected kernels
(`exists_protectedKernel`) of the unions of the undischarged regions, and the chain is `exists_chain`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

open LQGMetric GFF Ito

section Stops

variable {Ω : Type*} {ι : Type*}

/-- The union of the regions `U i`, `i ∈ T`. -/
def unionOpens (U : ι → TopologicalSpace.Opens ℂ) (T : Finset ι) : TopologicalSpace.Opens ℂ :=
  ⨆ i ∈ T, U i

theorem coe_unionOpens (U : ι → TopologicalSpace.Opens ℂ) (T : Finset ι) :
    (unionOpens U T : Set ℂ) = ⋃ i ∈ T, (U i : Set ℂ) := by
  simp [unionOpens]

theorem unionOpens_mono (U : ι → TopologicalSpace.Opens ℂ) {T T' : Finset ι} (h : T ⊆ T') :
    unionOpens U T ≤ unionOpens U T' :=
  biSup_mono fun _ hi => h hi

theorem unionOpens_le (U : ι → TopologicalSpace.Opens ℂ) (hU : ∀ i, U i ≤ upperHalfPlaneOpens)
    (T : Finset ι) : unionOpens U T ≤ upperHalfPlaneOpens :=
  iSup₂_le fun i _ => hU i

variable [Fintype ι]

/-- The protected stop of the region `T` at stage `k`: `min (σ_k, min_{i ∈ T} τ_i)`. -/
def stageStop (τ : ι → Ω → ℝ≥0) (k : ℕ) (T : Finset ι) (ω : Ω) : ℝ≥0 :=
  T.fold min (ordStat τ k ω) fun i => τ i ω

variable {τ : ι → Ω → ℝ≥0}

theorem stageStop_le_ordStat (k : ℕ) (T : Finset ι) (ω : Ω) : stageStop τ k T ω ≤ ordStat τ k ω :=
  (Finset.fold_min_le _).2 (Or.inl le_rfl)

theorem stageStop_le_of_mem (k : ℕ) {T : Finset ι} {i : ι} (hi : i ∈ T) (ω : Ω) :
    stageStop τ k T ω ≤ τ i ω :=
  (Finset.fold_min_le _).2 (Or.inr ⟨i, hi, le_rfl⟩)

theorem stageStop_eq_ordStat {k : ℕ} {T : Finset ι} {ω : Ω} (h : ∀ i ∈ T, ordStat τ k ω ≤ τ i ω) :
    stageStop τ k T ω = ordStat τ k ω :=
  le_antisymm (stageStop_le_ordStat k T ω) ((Finset.le_fold_min _).2 ⟨le_rfl, h⟩)

theorem stageStop_mono {k k' : ℕ} (h : k ≤ k') (T : Finset ι) (ω : Ω) :
    stageStop τ k T ω ≤ stageStop τ k' T ω :=
  (Finset.le_fold_min _).2 ⟨(stageStop_le_ordStat k T ω).trans (ordStat_mono h ω),
    fun _ hi => stageStop_le_of_mem k hi ω⟩

theorem stageStop_zero (T : Finset ι) (ω : Ω) : stageStop τ 0 T ω = 0 :=
  le_antisymm ((stageStop_le_ordStat 0 T ω).trans (ordStat_zero ω).le) (zero_le (a := stageStop τ 0 T ω))

variable {mΩ : MeasurableSpace Ω} {𝓖 : MeasureTheory.Filtration ℝ≥0 mΩ}

theorem isStoppingTime_stageStop (hτ : ∀ i, IsStoppingTime 𝓖 fun ω => (τ i ω : WithTop ℝ≥0))
    (k : ℕ) (T : Finset ι) : IsStoppingTime 𝓖 fun ω => (stageStop τ k T ω : WithTop ℝ≥0) := by
  intro t
  have : {ω | (stageStop τ k T ω : WithTop ℝ≥0) ≤ t} =
      {ω | (ordStat τ k ω : WithTop ℝ≥0) ≤ t} ∪ ⋃ i ∈ T, {ω | (τ i ω : WithTop ℝ≥0) ≤ t} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, stageStop, Finset.fold_min_le, mem_union,
      mem_iUnion, exists_prop]
  rw [this]
  exact (isStoppingTime_ordStat hτ k t).union (Finset.measurableSet_biUnion _ fun i _ => hτ i t)

end Stops

/-! ### Helpers: agreement from almost-everywhere equality and from characteristic functionals -/

section Helpers

variable {Ω X : Type*} [MeasurableSpace X]

theorem RectAgree.of_ae_eq {𝒜 mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) {P : Measure Ω}
    [IsFiniteMeasure P] {E : Set Ω} {κ₁ κ₂ : Kernel Ω X} [IsMarkovKernel κ₁] [IsMarkovKernel κ₂]
    (h : ∀ᵐ ω ∂P, ω ∈ E → κ₁ ω = κ₂ ω) : RectAgree 𝒜 P E κ₁ κ₂ := by
  intro A hA hAE B hB
  have hA' : MeasurableSet A := h𝒜 A hA
  rw [Measure.compProd_apply_prod hA' hB, Measure.compProd_apply_prod hA' hB]
  refine setLIntegral_congr_fun_ae hA' ?_
  filter_upwards [h] with ω hω hωA
  rw [hω (hAE hωA)]

/-- Equal characteristic functionals give equal kernel values. -/
theorem eq_of_integral_cexp {V : TopologicalSpace.Opens ℂ} {μ ν : Measure (DistOn V)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ ψ : TestOn V, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂μ =
      ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂ν) : μ = ν :=
  ext_of_integral_cexp h

/-- The characteristic functional of an image under restriction. -/
theorem integral_cexp_map_restrictDist {V D : TopologicalSpace.Opens ℂ} (μ : Measure (DistOn D))
    (ψ : TestOn V) :
    ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(μ.map (restrictDist V)) =
      ∫ g, Complex.exp (Complex.I * (g (testIncl V D ψ) : ℂ)) ∂μ := by
  rw [integral_map (measurable_restrictDist V).aemeasurable
    (measurable_exp_I_mul (measurable_distOn_apply ψ)).aestronglyMeasurable]
  rfl

/-- From agreement on rectangles to the integrated characteristic functionals. -/
theorem RectAgree.setIntegral_cexp_eq {V : TopologicalSpace.Opens ℂ} {𝒜 mΩ : MeasurableSpace Ω}
    (h𝒜 : 𝒜 ≤ mΩ) {P : Measure Ω} [IsFiniteMeasure P] {E : Set Ω}
    {κ₁ κ₂ : Kernel Ω (DistOn V)} [IsMarkovKernel κ₁] [IsMarkovKernel κ₂]
    (h : RectAgree 𝒜 P E κ₁ κ₂) {A : Set Ω} (hA : MeasurableSet[𝒜] A) (hAE : A ⊆ E)
    (ψ : TestOn V) :
    ∫ ω in A, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(κ₁ ω) ∂P =
      ∫ ω in A, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(κ₂ ω) ∂P := by
  have hA' : MeasurableSet A := h𝒜 A hA
  have hmeas : Measurable fun g : DistOn V => Complex.exp (Complex.I * (g ψ : ℂ)) :=
    measurable_exp_I_mul (measurable_distOn_apply ψ)
  set m : Kernel Ω (DistOn V) → Measure (DistOn V) := fun κ => ((P.restrict A) ⊗ₘ κ).map Prod.snd
    with hmdef
  have hval : ∀ (κ : Kernel Ω (DistOn V)) [IsMarkovKernel κ] (B : Set (DistOn V)), MeasurableSet B →
      m κ B = (P ⊗ₘ κ) (A ×ˢ B) := by
    intro κ _ B hB
    rw [hmdef, Measure.map_apply measurable_snd hB, show (Prod.snd ⁻¹' B : Set (Ω × DistOn V)) =
      univ ×ˢ B by ext; simp, Measure.compProd_apply_prod MeasurableSet.univ hB,
      Measure.compProd_apply_prod hA' hB, Measure.restrict_univ]
  have heq : m κ₁ = m κ₂ := Measure.ext fun B hB => by
    rw [hval κ₁ B hB, hval κ₂ B hB]; exact h A hA hAE B hB
  have hint : ∀ (κ : Kernel Ω (DistOn V)) [IsMarkovKernel κ],
      ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(m κ) =
        ∫ ω in A, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(κ ω) ∂P := by
    intro κ _
    rw [hmdef, integral_map measurable_snd.aemeasurable hmeas.aestronglyMeasurable,
      Measure.integral_compProd]
    exact Integrable.of_bound (hmeas.comp measurable_snd).aestronglyMeasurable 1
      (Eventually.of_forall fun p => (Complex.norm_exp_I_mul_ofReal _).le)
  rw [← hint κ₁, ← hint κ₂, heq]

end Helpers

/-! ### The field marginal -/

section FieldLaw

/-- The law of `𝔥₀ + h⁰` on `𝒟'(ℍ)`, `h⁰` a zero-boundary GFF on `ℍ` and `𝔥₀ = u₀`. -/
def fieldLaw0 (u₀ : ℂ → ℝ) : Measure (DistOn upperHalfPlaneOpens) :=
  gaussLaw upperHalfPlaneOpens upperHalfPlaneOpens (Distribution.ofFun upperHalfPlaneOpens u₀ volume ⊤)

instance (u₀ : ℂ → ℝ) : IsProbabilityMeasure (fieldLaw0 u₀) := by
  rw [fieldLaw0]; infer_instance

theorem integral_cexp_fieldLaw0 {u₀ : ℂ → ℝ} (hu₀ : ContinuousOn u₀ H) (ψ : TestOn upperHalfPlaneOpens) :
    ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂fieldLaw0 u₀ =
      Complex.exp (Complex.I * ((∫ z, u₀ z * ψ z : ℝ) : ℂ) -
        (zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ : ℂ) / 2) := by
  rw [fieldLaw0, integral_cexp_gaussLaw le_rfl subset_rfl, Distribution.ofFun_apply
    (hu₀.locallyIntegrableOn upperHalfPlaneOpens.isOpen.measurableSet)]
  simp only [smul_eq_mul, mul_comm (ψ _)]

end FieldLaw

/-! ### The finite-family theorem -/

/-! ### Per-pair helpers -/

section PairHelpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open Function in
theorem setIntegral_eq_of_partition {P : Measure Ω} {J : Type*} [Fintype J] {D : J → Set Ω}
    (hD : ∀ j, MeasurableSet (D j)) (hdisj : Pairwise (Disjoint on D)) {A : Set Ω}
    (hA : MeasurableSet A) (hcov : A ⊆ ⋃ j, D j) {f g : Ω → ℂ} (hf : IntegrableOn f A P)
    (hg : IntegrableOn g A P) (h : ∀ j, ∫ ω in A ∩ D j, f ω ∂P = ∫ ω in A ∩ D j, g ω ∂P) :
    ∫ ω in A, f ω ∂P = ∫ ω in A, g ω ∂P := by
  have hU : A = ⋃ j, A ∩ D j := by
    ext ω; simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun hω => by obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov hω); exact ⟨j, hω, hj⟩,
      fun ⟨_, hω, _⟩ => hω⟩
  have hm : ∀ j, MeasurableSet (A ∩ D j) := fun j => hA.inter (hD j)
  have hd : Pairwise (Disjoint on fun j => A ∩ D j) := fun i j hij =>
    (hdisj hij).mono inter_subset_right inter_subset_right
  rw [hU, integral_iUnion hm hd (hU ▸ hf), integral_iUnion hm hd (hU ▸ hg), tsum_fintype,
    tsum_fintype]
  exact Finset.sum_congr rfl fun j _ => h j

/-- A test function on `ℍ` supported in `V`, as a test function on `V`. -/
def testRestrict {V : TopologicalSpace.Opens ℂ} (ψ : TestOn upperHalfPlaneOpens)
    (h : tsupport ψ ⊆ V) : TestOn V where
  toFun := ψ
  contDiff' := ψ.contDiff
  hasCompactSupport' := ψ.hasCompactSupport
  tsupport_subset' := h

@[simp] theorem coe_testRestrict {V : TopologicalSpace.Opens ℂ} (ψ : TestOn upperHalfPlaneOpens)
    (h : tsupport ψ ⊆ V) : ⇑(testRestrict ψ h) = ψ := rfl

theorem testIncl_testRestrict {V : TopologicalSpace.Opens ℂ} (hV : V ≤ upperHalfPlaneOpens)
    (ψ : TestOn upperHalfPlaneOpens) (h : tsupport ψ ⊆ V) :
    testIncl V upperHalfPlaneOpens (testRestrict ψ h) = ψ := by
  ext z
  rw [coe_testIncl hV]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {τ : ι → Ω → ℝ≥0}
  {𝓖 : MeasureTheory.Filtration ℝ≥0 mΩ}

theorem measurableSet_stageSet_succ (hτ : ∀ i, IsStoppingTime 𝓖 fun ω => (τ i ω : WithTop ℝ≥0))
    (k : ℕ) (T : Finset ι) :
    MeasurableSet[(isStoppingTime_ordStat hτ (k + 1)).measurableSpace] {ω | stageSet τ (k + 1) ω = T} := by
  rcases k with _ | k
  · by_cases h : (Finset.univ : Finset ι) = T
    · have : {ω | stageSet τ 1 ω = T} = univ := by ext; simp [stageSet, h]
      rw [this]; exact @MeasurableSet.univ Ω (isStoppingTime_ordStat hτ 1).measurableSpace
    · have : {ω | stageSet τ 1 ω = T} = ∅ := by ext; simp [stageSet, h]
      rw [this]; exact @MeasurableSet.empty Ω (isStoppingTime_ordStat hτ 1).measurableSpace
  · have hlt : ∀ j, MeasurableSet[(isStoppingTime_ordStat hτ (k + 1)).measurableSpace]
        {ω | ordStat τ (k + 1) ω < τ j ω} := by
      intro j
      have h := (hτ j).measurableSet_stopping_time_le (isStoppingTime_ordStat hτ (k + 1))
      have : {ω | ordStat τ (k + 1) ω < τ j ω} =
          {ω | (τ j ω : WithTop ℝ≥0) ≤ (ordStat τ (k + 1) ω : WithTop ℝ≥0)}ᶜ := by
        ext ω
        simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_le_coe, not_le]
      rw [this]
      exact h.compl
    have hset : {ω | stageSet τ (k + 2) ω = T} = ⋂ j, {ω | (ordStat τ (k + 1) ω < τ j ω ↔ j ∈ T)} := by
      ext ω
      simp only [stageSet, mem_ofPred_eq, mem_iInter, Finset.ext_iff, Finset.mem_filter,
        Finset.mem_univ, true_and]
    have hmeas : MeasurableSet[(isStoppingTime_ordStat hτ (k + 1)).measurableSpace]
        {ω | stageSet τ (k + 2) ω = T} := by
      rw [hset]
      refine MeasurableSet.iInter fun j => ?_
      by_cases hj : j ∈ T
      · simp only [hj, iff_true]; exact hlt j
      · simp only [hj, iff_false]; exact (hlt j).compl
    exact (isStoppingTime_ordStat hτ (k + 1)).measurableSpace_mono (isStoppingTime_ordStat hτ (k + 2))
      (fun ω => WithTop.coe_le_coe.2 (ordStat_mono (Nat.le_succ _) ω)) _ hmeas

end PairHelpers

section Family

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

theorem ordStat_le_exists {ι : Type*} [Fintype ι] [Nonempty ι] (τ : ι → Ω → ℝ≥0) (k : ℕ) (ω : Ω) :
    ∃ i, ordStat τ k ω ≤ τ i ω := by
  classical
  obtain ⟨S, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
    (n := min k (Fintype.card ι)) (by rw [Finset.card_univ]; exact min_le_right _ _)
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ι) Finset.univ_nonempty
    fun i => τ i ω
  refine ⟨i, (ordStat_le_iff k ω _).2 ⟨S, hS.2, fun j _ => ?_⟩⟩
  rw [← hi]
  exact Finset.le_sup (f := fun i => τ i ω) (Finset.mem_univ j)

section Main

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
  (u : Ω → ℝ≥0 → ℂ → ℝ)
  (hu : ∀ ω s, IsBoundedHarmonicExtension
    (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
    (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
  {u₀ : ℂ → ℝ}
  (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
include hE hκ hu hu₀

/-- The stage kernels, their σ-algebras and the chain hypotheses (the construction part of
`exists_finiteFamilyKernel`). -/
theorem exists_stageChain {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
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
        ∀ k, 1 ≤ k → k ≤ Fintype.card ι → ∀ T,
          RectAgree (isStoppingTime_ordStat hτ k).measurableSpace P {ω | stageSet τ k ω = T}
            (η.map (restrictDist (unionOpens U T))) (Q k T) := by
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
  have hη₀m : Measurable[𝒜 0] fun ω => η₀ ω := measurable_const
  obtain ⟨η, hηM, -, hmarg, hinv⟩ := exists_chain P V hVH (fun T T' h => unionOpens_mono U h) 𝒜
    h𝒜 h𝒜m (stageSet τ) hR0 hR stageSet_succ_subset Q (hQ := hQM) η₀ hη₀m h0 hmart hcons
    (Fintype.card ι)
  refine ⟨η, hηM, fun S hS => ?_, fun k hk hkN T => ?_⟩
  · have h := hmarg univ (@MeasurableSet.univ Ω (𝒜 0)) subset_rfl S hS
    rw [Measure.compProd_apply_prod MeasurableSet.univ hS,
      Measure.compProd_apply_prod MeasurableSet.univ hS] at h
    simp only [Measure.restrict_univ, hη₀, Kernel.const_apply, lintegral_const, measure_univ,
      mul_one] at h
    exact h
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
    exact hinv (k' + 1) hkN T

/-- **Finite families of protected pairs: one coupling** (Astra §1, (1.10), the protected-kernel constraint). For
finitely many open `U i ⊆ ℍ` and stopping times `τ i` of the usual augmentation with `τ i < ζ` and
`U i ∩ K_{τ i} = ∅` almost surely, there is a Markov kernel `η : Ω → 𝒟'(ℍ)` (the field given the driving history)
whose field marginal is `fieldLaw0 u₀` (the law of `𝔥₀ + h⁰`) and which satisfies, for every pair, every test
function `ψ` supported in `U i` and every `A ∈ 𝓖_{τ i}`,
`∫_A ∫ exp(i h(ψ)) dη dP = ∫_A exp(i (𝔥_{τ i}, ψ) − E_{τ i}(ψ)/2) dP`. -/
theorem exists_finiteFamilyKernel {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : ι → TopologicalSpace.Opens ℂ) (hUH : ∀ i, U i ≤ upperHalfPlaneOpens) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ i ω : WithTop ℝ≥0))
    (hτU : ∀ i, ∀ᵐ ω ∂P, (τ i ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (U i : Set ℂ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (τ i ω))) :
    ∃ η : Kernel Ω (DistOn upperHalfPlaneOpens), IsMarkovKernel η ∧
      (∀ S, MeasurableSet S → ∫⁻ ω, η ω S ∂P = fieldLaw0 u₀ S) ∧
      ∀ i (ψ : TestOn upperHalfPlaneOpens), tsupport ψ ⊆ U i → ∀ A,
        MeasurableSet[(hτ i).measurableSpace] A →
          ∫ ω in A, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(η ω) ∂P =
            ∫ ω in A, cfAt κ W u ψ 1 (τ i) ω ∂P := by
  classical
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  obtain ⟨Q, hQM, hQcf, η, hηM, hmarg, hstage⟩ := exists_stageChain hE hκ u hu hu₀ U hUH τ hτ hτU
  refine ⟨η, hηM, hmarg, fun i ψ hψU A hA => ?_⟩
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

end Main

end Family

end Coupling

end InteractingSLE
