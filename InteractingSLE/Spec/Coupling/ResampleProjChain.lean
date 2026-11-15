import InteractingSLE.Spec.Coupling.ResampleProjCore

/-!
# Projection independence by Gaussian resampling: one stage and the chain (Theorem 1.1)

Packet PROVE-T11-PROJ (Astra §1, pp. 5–6, (1.9)). The stage of PROVE-T11-KER (`exists_stage_on`) followed by the
resampling of the projection onto `H(V)` (`resampleKernel`):

* `exists_stageProj_on` : as `exists_stage_on`, with in addition projection independence at `V` on every event of
  the new stage σ-algebra. The old history–field law is unchanged because the old law is already projection-independent
  at `V` (`resample_eq_of_isProjIndepMeasure`); the new restricted law is unchanged because the new protected kernel
  satisfies the Gaussian shift rule (`integral_cexp_resample_eq_of_shift`);
* `exists_chainProj` : `exists_chain` started at the time-zero field law, with projection independence at every stage
  region on every event of every stage σ-algebra.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

namespace InteractingSLE

namespace Coupling

open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovHarm GFF LocalSets QuantumZipper.K3 QuantumZipper.Thm11Asm

/-! ### Linearity in the integrated law -/

section Linear

variable {V : Opens ℂ}

theorem isProjIndepMeasure_zero : IsProjIndepMeasure V 0 := fun f Ξ => by simp

theorem IsProjIndepMeasure.smul {μ : Measure (DistOn upperHalfPlaneOpens)} (h : IsProjIndepMeasure V μ)
    (c : ℝ≥0∞) : IsProjIndepMeasure V (c • μ) := fun f Ξ => by
  rw [integral_smul_measure, integral_smul_measure, h f Ξ]
  rw [Complex.real_smul, Complex.real_smul]
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

theorem secMeas_eq_sum_of_partition {X : Type*} [MeasurableSpace X] {η : Kernel Ω X} [IsMarkovKernel η]
    {J : Type*} [Fintype J] {S : Ω → J} (hS : ∀ j, MeasurableSet {ω | S ω = j}) {A : Set Ω}
    (hA : MeasurableSet A) : secMeas P A η = ∑ j, secMeas P (A ∩ {ω | S ω = j}) η := by
  ext B hB
  rw [Measure.coe_finsetSum, Finset.sum_apply, secMeas_apply hA hB]
  simp_rw [secMeas_apply (hA.inter (hS _)) hB]
  have hU : A ×ˢ B = ⋃ j, (A ∩ {ω | S ω = j}) ×ˢ B := by
    ext p
    simp only [mem_prod, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨S p.1, ⟨h.1, rfl⟩, h.2⟩, fun ⟨_, h1, h2⟩ => ⟨h1.1, h2⟩⟩
  rw [hU, measure_iUnion (fun i j hij => Set.disjoint_prod.2 (Or.inl (Set.disjoint_left.2
      fun ω hi hj => hij (hi.2.symm.trans hj.2))))
    (fun j => (hA.inter (hS j)).prod hB), tsum_fintype]

/-- Projection independence on every piece of a finite measurable partition gives it on the union. -/
theorem isProjIndepMeasure_secMeas_of_partition {η : Kernel Ω (DistOn upperHalfPlaneOpens)} [IsMarkovKernel η]
    {J : Type*} [Fintype J] {S : Ω → J} (hS : ∀ j, MeasurableSet {ω | S ω = j}) {A : Set Ω}
    (hA : MeasurableSet A) (h : ∀ j, IsProjIndepMeasure V (secMeas P (A ∩ {ω | S ω = j}) η)) :
    IsProjIndepMeasure V (secMeas P A η) := by
  intro f Ξ
  have hint : ∀ (Ψ : TestOn upperHalfPlaneOpens) (j : J), Integrable
      (fun x : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (x Ψ : ℂ)))
      (secMeas P (A ∩ {ω | S ω = j}) η) := fun Ψ j =>
    Integrable.of_bound (measurable_exp_I_mul (measurable_distOn_apply Ψ)).aestronglyMeasurable 1
      (Eventually.of_forall fun x => (Complex.norm_exp_I_mul_ofReal _).le)
  rw [secMeas_eq_sum_of_partition hS hA, integral_finsetSum_measure fun j _ => hint _ j,
    integral_finsetSum_measure fun j _ => hint _ j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => h j f Ξ

end Linear

/-! ### Restriction of characteristic functionals -/

section Restrict

variable {V : Opens ℂ}

/-- The Dirichlet direction `−Δf/2π` as a test function on `V`. -/
theorem toTestH_cmTestOn (f : zsSub (V : Set ℂ)) : toTestH V (cmTestOn f) = lapTest V f := rfl

theorem integral_cexp_toTestH (μ : Measure (DistOn upperHalfPlaneOpens)) (ψ : TestOn V) :
    ∫ x, Complex.exp (Complex.I * (x (toTestH V ψ) : ℂ)) ∂μ =
      ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(μ.map (restrictDist V)) :=
  (integral_cexp_map_restrictDist μ ψ).symm

/-- The shift rule at `ψ ∈ 𝓓(V)` only depends on the restricted law. -/
theorem isProjShiftMeasure_toTestH {μ : Measure (DistOn upperHalfPlaneOpens)} {ψ : TestOn V}
    (h : ∀ f : zsSub (V : Set ℂ),
      ∫ g, Complex.exp (Complex.I * (g (ψ - cmTestOn f) : ℂ)) ∂(μ.map (restrictDist V)) =
        Complex.exp (((-(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 +
          ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) (toTestH V ψ)⟫ : ℝ) : ℂ)) *
          ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(μ.map (restrictDist V))) :
    IsProjShiftMeasure V μ (toTestH V ψ) := by
  intro f
  rw [← toTestH_cmTestOn, ← map_sub, integral_cexp_toTestH, integral_cexp_toTestH]
  exact h f

end Restrict

/-! ### One stage with resampling -/

section Stage

variable {Ω : Type*}

/-- **The Gaussian shift rule of a restricted law on `𝒟'(V)`** (the form in which the protected kernels enter):
removing `−Δf/2π` from `ψ ∈ 𝓓(V)` multiplies the characteristic functional by `exp(−‖∇f‖²/2 + ⟪∇f, covVec_V ψ⟫)`. -/
def IsShiftLaw (V : Opens ℂ) (ν : Measure (DistOn V)) : Prop :=
  ∀ (ψ : TestOn V) (f : zsSub (V : Set ℂ)),
    ∫ g, Complex.exp (Complex.I * (g (ψ - cmTestOn f) : ℂ)) ∂ν =
      Complex.exp (((-(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 +
        ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) (toTestH V ψ)⟫ : ℝ) : ℂ)) *
        ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂ν

/-- **One stage of the forward construction with resampling of the projection onto `H(V)`** (Astra pp. 5–6). As
`exists_stage_on`, for an old field kernel `η` whose integrated laws on `E` are absolutely continuous with respect to
the time-zero field law and projection-independent at `V` on every event of `𝒜` inside `E`, and a new protected kernel
`Q'` with the Gaussian shift rule on the events of `𝒜'`: the new kernel is in addition projection-independent at `V` on
every event of `𝒜'` inside `E`. -/
theorem exists_stageProj_on {𝒜 𝒜' mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ 𝒜') (h𝒜' : 𝒜' ≤ mΩ)
    (P : Measure Ω) [IsFiniteMeasure P] {E : Set Ω} (hE : MeasurableSet[𝒜] E)
    (η : Kernel Ω (DistOn upperHalfPlaneOpens)) [IsMarkovKernel η]
    (hη : Measurable[𝒜] fun ω => η ω) (V : Opens ℂ) (hVH : (V : Set ℂ) ⊆ H) (Q Q' : Kernel Ω (DistOn V))
    [IsMarkovKernel Q] [IsMarkovKernel Q'] (hηQ : RectAgree 𝒜 P E (η.map (restrictDist V)) Q)
    (hQQ' : RectAgree 𝒜 P E Q' Q) {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hac : secMeas P E η ≪ fieldLaw0 u₀)
    (hproj : ∀ A, MeasurableSet[𝒜] A → A ⊆ E → IsProjIndepMeasure V (secMeas P A η))
    (hshift : ∀ A, MeasurableSet[𝒜'] A → A ⊆ E → IsShiftLaw V (secMeas P A Q')) :
    ∃ η'' : Kernel Ω (DistOn upperHalfPlaneOpens), IsMarkovKernel η'' ∧
      Measurable[𝒜'] (fun ω => η'' ω) ∧ RectAgree 𝒜 P E η'' η ∧
      RectAgree 𝒜' P E (η''.map (restrictDist V)) Q' ∧
      ∀ A, MeasurableSet[𝒜'] A → A ⊆ E → IsProjIndepMeasure V (secMeas P A η'') := by
  have h𝒜m : 𝒜 ≤ mΩ := h𝒜.trans h𝒜'
  have hEm : MeasurableSet E := h𝒜m E hE
  have hr : Measurable (restrictDist V (D := upperHalfPlaneOpens)) := measurable_restrictDist V
  obtain ⟨η', hη'M, hη'm, hc, hd⟩ := exists_stage_on h𝒜 h𝒜' P hE η hη V Q Q' hηQ hQQ'
  obtain ⟨G, hGm, hGd⟩ := exists_markovMap_zbLaw V hVH
  set c := meanH u₀ with hcdef
  set η'' := resampleKernel G c η' with hη''
  have hη''M : IsMarkovKernel η'' := isMarkovKernel_resampleKernel hGm c η'
  have : IsMarkovKernel (η'.map (restrictDist V)) := Kernel.IsMarkovKernel.map η' hr
  have : IsMarkovKernel (η''.map (restrictDist V)) := Kernel.IsMarkovKernel.map η'' hr
  -- absolute continuity of the integrated laws of the new kernel on `E`
  have hac' : ∀ A, MeasurableSet A → A ⊆ E → secMeas P A η' ≪ fieldLaw0 u₀ := fun A hA hAE =>
    (Measure.absolutelyContinuous_of_le (secMeas_mono hA hEm hAE)).trans
      ((RectAgree.secMeas_eq h𝒜m hc hE subset_rfl).symm ▸ hac)
  have hsec : ∀ A, MeasurableSet A → secMeas P A η'' = resample G c (secMeas P A η') := fun A hA =>
    secMeas_resampleKernel hGm c η' hA
  refine ⟨η'', hη''M, ?_, ?_, ?_, ?_⟩
  · -- measurability for the new σ-algebra
    refine @Measure.measurable_of_measurable_coe _ _ _ 𝒜' _ fun B hB => ?_
    have hR := measurable_resampleMap hGm c
    have hRB : MeasurableSet (resampleMap G c ⁻¹' B) := hR hB
    have e : (fun ω => η'' ω B) = fun ω =>
        ∫⁻ x, zbLaw upperHalfPlaneOpens (Prod.mk x ⁻¹' (resampleMap G c ⁻¹' B)) ∂(η' ω) := by
      funext ω
      rw [hη'', resampleKernel_apply hGm, resample, Measure.map_apply hR hB, Measure.prod_apply hRB]
    rw [e]
    exact (Measure.measurable_lintegral (measurable_measure_prodMk_left hRB)).comp hη'm
  · -- the old joint law is unchanged
    intro A hA hAE B hB
    have hA' : MeasurableSet A := h𝒜m A hA
    have h1 : secMeas P A η' = secMeas P A η := RectAgree.secMeas_eq h𝒜m hc hA hAE
    have h2 : secMeas P A η'' = secMeas P A η := by
      rw [hsec A hA', h1]
      exact resample_eq_of_isProjIndepMeasure hGm hGd hVH hu₀
        ((Measure.absolutelyContinuous_of_le (secMeas_mono hA' hEm hAE)).trans hac) (hproj A hA hAE)
    rw [← secMeas_apply hA' hB, ← secMeas_apply hA' hB, h2]
  · -- the new restricted law is unchanged
    intro A hA hAE B hB
    have hA' : MeasurableSet A := h𝒜' A hA
    have hμ := hac' A hA' hAE
    have hres : (secMeas P A η').map (restrictDist V) = secMeas P A Q' := by
      rw [← secMeas_map hA' hr]
      exact RectAgree.secMeas_eq h𝒜' hd hA hAE
    have hkey : (secMeas P A η'').map (restrictDist V) = (secMeas P A η').map (restrictDist V) := by
      refine ext_of_integral_cexp fun ψ => ?_
      rw [← integral_cexp_toTestH, ← integral_cexp_toTestH, hsec A hA']
      refine integral_cexp_resample_eq_of_shift hGm hGd hVH hu₀ hμ (isProjShiftMeasure_toTestH ?_)
      intro f
      rw [hres]
      exact hshift A hA hAE ψ f
    rw [← secMeas_apply hA' hB, ← secMeas_apply hA' hB, secMeas_map hA' hr, hkey, hres]
  · -- projection independence on the new events
    intro A hA hAE
    have hA' : MeasurableSet A := h𝒜' A hA
    rw [hsec A hA']
    exact isProjIndepMeasure_resample hGm hGd hVH hu₀ (hac' A hA' hAE)

end Stage

/-! ### The chain with resampling -/

section Chain

variable {Ω : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The chain of stages with resampling** (Astra pp. 5–6, (1.9)): `exists_chain` started at the time-zero field
law `fieldLaw0 u₀`, for protected kernels with the Gaussian shift rule; the final kernel is in addition
projection-independent at `V T` on every event of `𝒜 k` inside `{R k = T}`, for every stage `k ≤ N`. -/
theorem exists_chainProj {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    (V : Finset ι → TopologicalSpace.Opens ℂ) (hVH : ∀ T, V T ≤ upperHalfPlaneOpens)
    (hV : ∀ T T', T ⊆ T' → V T ≤ V T')
    (𝒜 : ℕ → MeasurableSpace Ω) (h𝒜 : Monotone 𝒜) (h𝒜m : ∀ k, 𝒜 k ≤ mΩ)
    (R : ℕ → Ω → Finset ι) (hR0 : ∀ T, MeasurableSet[𝒜 0] {ω | R 0 ω = T})
    (hR : ∀ k T, MeasurableSet[𝒜 k] {ω | R (k + 1) ω = T})
    (hRmono : ∀ k ω, R (k + 1) ω ⊆ R k ω)
    (Q : ℕ → (T : Finset ι) → Kernel Ω (DistOn (V T))) [hQ : ∀ k T, IsMarkovKernel (Q k T)]
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (h0 : ∀ T, RectAgree (𝒜 0) P {ω | R 0 ω = T}
      ((Kernel.const Ω (fieldLaw0 u₀)).map (restrictDist (V T))) (Q 0 T))
    (hmart : ∀ k T, RectAgree (𝒜 k) P {ω | R (k + 1) ω = T} (Q (k + 1) T) (Q k T))
    (hcons : ∀ k T T', T ⊆ T' → RectAgree (𝒜 k) P ({ω | R k ω = T'} ∩ {ω | R (k + 1) ω = T})
      ((Q k T').map (restrictDist (V T))) (Q k T))
    (hshift : ∀ k T A, MeasurableSet[𝒜 k] A → A ⊆ {ω | R k ω = T} → IsShiftLaw (V T) (secMeas P A (Q k T)))
    (N : ℕ) :
    ∃ η : Kernel Ω (DistOn upperHalfPlaneOpens), IsMarkovKernel η ∧
      Measurable[𝒜 N] (fun ω => η ω) ∧ RectAgree (𝒜 0) P univ η (Kernel.const Ω (fieldLaw0 u₀)) ∧
      (∀ k ≤ N, ∀ T, RectAgree (𝒜 k) P {ω | R k ω = T} (η.map (restrictDist (V T))) (Q k T)) ∧
      ∀ k ≤ N, ∀ T A, MeasurableSet[𝒜 k] A → A ⊆ {ω | R k ω = T} →
        IsProjIndepMeasure (V T) (secMeas P A η) := by
  have hr : ∀ T, Measurable (restrictDist (V T) (D := upperHalfPlaneOpens)) := fun T =>
    measurable_restrictDist (V T)
  have hRk : ∀ k T, MeasurableSet[𝒜 k] {ω | R k ω = T} := by
    intro k T
    cases k with
    | zero => exact hR0 T
    | succ k => exact h𝒜 (Nat.le_succ k) _ (hR k T)
  set η₀ : Kernel Ω (DistOn upperHalfPlaneOpens) := Kernel.const Ω (fieldLaw0 u₀) with hη₀
  induction N with
  | zero =>
    refine ⟨η₀, inferInstance, measurable_const, fun A _ _ B _ => rfl, fun k hk T => ?_,
      fun k hk T A hA _ => ?_⟩
    · obtain rfl : k = 0 := Nat.le_zero.1 hk
      exact h0 T
    · obtain rfl : k = 0 := Nat.le_zero.1 hk
      rw [hη₀, secMeas_const (h𝒜m 0 A hA)]
      exact (isProjIndepMeasure_fieldLaw0 hu₀ (hVH T)).smul _
  | succ N ih =>
    obtain ⟨η, hηM, hηm, hmarg, hinv, hproj⟩ := ih
    -- the restriction of `η` to the next region
    have hηQ : ∀ T, RectAgree (𝒜 N) P {ω | R (N + 1) ω = T}
        (η.map (restrictDist (V T))) (Q N T) := by
      intro T
      have : IsMarkovKernel (η.map (restrictDist (V T))) := Kernel.IsMarkovKernel.map η (hr T)
      refine RectAgree.of_partition (h𝒜m N) (S := R N) (hRk N) fun T' => ?_
      · by_cases hTT' : T ⊆ T'
        · have hm : (η.map (restrictDist (V T))) =
              (η.map (restrictDist (V T'))).map (restrictDist (V T) (D := V T')) := by
            rw [← Kernel.map_comp_right _ (hr T') (measurable_restrictDist (V T))]
            congr 1
            funext h
            exact (restrictDist_restrictDist (hV T T' hTT') (hVH T') h).symm
          have : IsMarkovKernel (η.map (restrictDist (V T'))) := Kernel.IsMarkovKernel.map η (hr T')
          rw [hm]
          refine (((hinv N le_rfl T').map (h𝒜m N) (measurable_restrictDist (V T))).mono le_rfl
            fun ω hω => hω.2).trans ((hcons N T T' hTT').mono le_rfl fun ω hω => ⟨hω.2, hω.1⟩)
        · refine RectAgree.of_empty ?_ _ _
          ext ω
          simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          intro h1 h2
          exact hTT' (h1 ▸ h2 ▸ hRmono N ω)
    -- the old kernel is projection-independent at the next regions
    have hprojN : ∀ T A, MeasurableSet[𝒜 N] A → A ⊆ {ω | R (N + 1) ω = T} →
        IsProjIndepMeasure (V T) (secMeas P A η) := by
      intro T A hA hAT
      refine isProjIndepMeasure_secMeas_of_partition (S := R N) (fun T' => h𝒜m N _ (hRk N T'))
        (h𝒜m N A hA) fun T' => ?_
      by_cases hTT' : T ⊆ T'
      · exact (hproj N le_rfl T' _ (hA.inter (hRk N T')) inter_subset_right).mono (hVH T')
          (hV T T' hTT')
      · have hempty : A ∩ {ω | R N ω = T'} = ∅ := by
          ext ω
          simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          intro h1 h2
          exact hTT' (h2 ▸ (hAT h1 : R (N + 1) ω = T) ▸ hRmono N ω)
        rw [hempty]
        have : secMeas P (∅ : Set Ω) η = 0 := by
          rw [secMeas, Measure.restrict_empty, Measure.compProd_zero_left, Measure.map_zero]
        rw [this]
        exact isProjIndepMeasure_zero
    -- absolute continuity of the integrated laws
    have hac : ∀ E, MeasurableSet E → secMeas P E η ≪ fieldLaw0 u₀ := by
      intro E hE
      have h1 : secMeas P univ η = secMeas P univ η₀ :=
        RectAgree.secMeas_eq (h𝒜m 0) hmarg (@MeasurableSet.univ Ω (𝒜 0)) subset_rfl
      rw [hη₀, secMeas_const MeasurableSet.univ] at h1
      refine (Measure.absolutelyContinuous_of_le (secMeas_mono hE MeasurableSet.univ (subset_univ E))).trans ?_
      rw [h1]
      exact Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl _) _
    -- one stage on each event `{R (N+1) = T}`
    have hstage : ∀ T, ∃ η' : Kernel Ω (DistOn upperHalfPlaneOpens), IsMarkovKernel η' ∧
        Measurable[𝒜 (N + 1)] (fun ω => η' ω) ∧ RectAgree (𝒜 N) P {ω | R (N + 1) ω = T} η' η ∧
        RectAgree (𝒜 (N + 1)) P {ω | R (N + 1) ω = T} (η'.map (restrictDist (V T))) (Q (N + 1) T) ∧
        ∀ A, MeasurableSet[𝒜 (N + 1)] A → A ⊆ {ω | R (N + 1) ω = T} →
          IsProjIndepMeasure (V T) (secMeas P A η') :=
      fun T => exists_stageProj_on (h𝒜 (Nat.le_succ N)) (h𝒜m (N + 1)) P (hR N T) η hηm (V T) (hVH T)
        (Q N T) (Q (N + 1) T) (hηQ T) (hmart N T) hu₀ (hac _ (h𝒜m N _ (hR N T))) (hprojN T)
        (hshift (N + 1) T)
    choose η' hη'M hη'm hc hd hp using hstage
    have : ∀ T, IsMarkovKernel (η' T) := hη'M
    have hRm : ∀ T, MeasurableSet {ω | R (N + 1) ω = T} := fun T => h𝒜m N _ (hR N T)
    set η₁ := kernelGlue (R (N + 1)) hRm η' with hη₁
    have hη₁M : IsMarkovKernel η₁ := isMarkovKernel_kernelGlue _ _ _
    have hη₁m : Measurable[𝒜 (N + 1)] fun ω => η₁ ω :=
      measurable_glue (fun T => h𝒜 (Nat.le_succ N) _ (hR N T)) hη'm
    have hon : ∀ T, ∀ ω ∈ {ω | R (N + 1) ω = T}, η₁ ω = η' T ω := fun T ω hω => by
      rw [hη₁, kernelGlue_apply]
      rw [mem_ofPred_eq] at hω
      rw [hω]
    have key : RectAgree (𝒜 N) P univ η₁ η := by
      refine RectAgree.of_partition (h𝒜m N) (S := R (N + 1)) (hR N) fun T => ?_
      intro A hA hAE B hB
      rw [compProd_prod_congr (h𝒜m N A hA) (fun ω hω => (hAE hω).2) (hon T) hB]
      exact hc T A hA (fun ω hω => (hAE hω).2) B hB
    refine ⟨η₁, hη₁M, hη₁m, (key.mono (h𝒜 (Nat.zero_le N)) subset_rfl).trans hmarg,
      fun k hk T => ?_, fun k hk T A hA hAT => ?_⟩
    · have : IsMarkovKernel (η₁.map (restrictDist (V T))) := Kernel.IsMarkovKernel.map η₁ (hr T)
      have : IsMarkovKernel (η.map (restrictDist (V T))) := Kernel.IsMarkovKernel.map η (hr T)
      rcases Nat.lt_or_ge k (N + 1) with hkN | hkN
      · have hkN' : k ≤ N := Nat.lt_succ_iff.1 hkN
        exact ((key.map (h𝒜m N) (hr T)).mono (h𝒜 hkN') (subset_univ _)).trans (hinv k hkN' T)
      · obtain rfl : k = N + 1 := le_antisymm hk hkN
        intro A hA hAE B hB
        have : IsMarkovKernel ((η' T).map (restrictDist (V T))) :=
          Kernel.IsMarkovKernel.map (η' T) (hr T)
        have hcg : (P ⊗ₘ η₁.map (restrictDist (V T))) (A ×ˢ B) =
            (P ⊗ₘ (η' T).map (restrictDist (V T))) (A ×ˢ B) :=
          compProd_prod_congr (h𝒜m (N + 1) A hA) hAE (fun ω hω => by
            simp only [Kernel.map_apply _ (hr T), hon T ω hω]) hB
        rw [hcg]
        exact hd T A hA hAE B hB
    · rcases Nat.lt_or_ge k (N + 1) with hkN | hkN
      · have hkN' : k ≤ N := Nat.lt_succ_iff.1 hkN
        rw [RectAgree.secMeas_eq (h𝒜m N) key (h𝒜 hkN' A hA) (subset_univ _)]
        exact hproj k hkN' T A hA hAT
      · obtain rfl : k = N + 1 := le_antisymm hk hkN
        have hA' : MeasurableSet A := h𝒜m (N + 1) A hA
        have e : secMeas P A η₁ = secMeas P A (η' T) := Measure.ext fun B hB => by
          rw [secMeas_apply hA' hB, secMeas_apply hA' hB]
          exact compProd_prod_congr hA' hAT (hon T) hB
        rw [e]
        exact hp T A hA hAT

end Chain

end Coupling

end InteractingSLE
