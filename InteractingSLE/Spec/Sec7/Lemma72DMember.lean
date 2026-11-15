/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.Locality11
import InteractingSLE.Spec.Coupling.WholeField8Local
import InteractingSLE.Spec.Coupling.ResampleProjCore
import InteractingSLE.Spec.Sec7.LocalExtLLocQ

/-!
# Locality at general stopping times, I: the member identity from a Gaussian kernel; hulls as random sets

Packet PROVE-LEMMA72D (ruling R37: Lemma 6.2's locality is available at path-form stops only; the locality of the
mapped hulls is needed at every stopping time of the pocket filtration). The passage follows Theorem 1.1's locality
proof (Astra p. 7, `Coupling.isLocalSet_hull_of_isFamilyLocal`), with the members supplied by Gaussian kernels at
deterministic times instead of a resampling construction:

* `setIntegral_lapTest_of_kernel` (**the member identity**): if, given `𝒦`, the field has the Gaussian kernel
  `exp(i M(χ) − ½ G_V(χ, χ))` (`WholeField.rangeKerCF`) with `M` harmonic on the random open set `V`, then on every
  `𝒦`-event `D` on which `U ⊆ V`, for `f ∈ C_c^∞(U)` and every test `Ξ`,
  `∫_D e^{i X(−Δf/2π + Ξ)} = projFactor U f Ξ · ∫_D e^{i X(Ξ)}`
  (the mean annihilates `−Δf/2π`, and the Gram data of `C_c^∞(U)` do not depend on `V ⊇ U`);
* `exists_stopped_disjoint`, `exists_hittingVersion_hull_of_adapted`: for a driver adapted (before its lifetime) to a
  filtration `𝓗` and a stopping time `τ` of the usual augmentation of `𝓗`, the hull `K_τ` has a hitting-measurable
  version whose avoidance events are, up to null sets, events of the stopped σ-algebra (the proofs of
  `Coupling.exists_drivingStopped_disjoint` and `Coupling.exists_hittingVersion_hull`, for a general filtration).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

namespace InteractingSLE.Sec7.Lemma72D

open QuantumZipper LQGMetric LQGMetric.MarkovZB LocalSets Coupling Ito QuantumZipper.K3 QuantumZipper.Thm11Asm

/-! ### The member identity -/

section Member

variable {Ω : Type*} {𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The member identity from a Gaussian kernel on an event.** Given `𝒦`, let the field `X` have the kernel
`rangeKerCF (M ω) (V ω)`. On a `𝒦`-event `D` on which `V` is an open subset of `ℍ` containing `U` with `M` harmonic on
`V`, the Dirichlet direction `−Δf/2π`, `f ∈ C_c^∞(U)`, enters with the factor of the projection onto `H(U)`. -/
theorem setIntegral_lapTest_of_kernel (h𝒦 : 𝒦 ≤ mΩ) {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    {M : Ω → DistOn upperHalfPlaneOpens} {V : Ω → Set ℂ}
    (hker : ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      P[fun ω' => Complex.exp (Complex.I * (X ω' χ : ℂ)) | 𝒦] ω = WholeField.rangeKerCF (M ω) (V ω) χ)
    {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens) {D : Set Ω} (hD : MeasurableSet[𝒦] D)
    (hDV : ∀ᵐ ω ∂P, ω ∈ D → IsOpen (V ω) ∧ V ω ⊆ H ∧ (U : Set ℂ) ⊆ V ω ∧ IsHarmonicDistOn (M ω) (V ω))
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
      Coupling.projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P := by
  have hint : ∀ χ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Complex.exp (Complex.I * (X ω χ : ℂ))) P := fun χ =>
    GFF.integrable_exp_I_mul ((measurable_distOn_apply χ).comp hXm)
  rw [← setIntegral_condExp h𝒦 (hint _) hD, ← setIntegral_condExp h𝒦 (hint _) hD, ← integral_const_mul]
  have hDm : MeasurableSet D := h𝒦 _ hD
  refine setIntegral_congr_ae hDm ?_
  filter_upwards [hker (lapTest U f + Ξ), hker Ξ, hDV] with ω h1 h2 h3 hωD
  rw [h1, h2]
  obtain ⟨hVo, hVH, hUV, hMω⟩ := h3 hωD
  have h0 := IsHarmonicDistOn.apply_lapTest_eq_zero hVo hMω hU hUV f
  have eM : M ω (lapTest U f + Ξ) = M ω Ξ := by rw [map_add, h0, zero_add]
  have eV := zeroGFFTestCov_lapTest_sub_add hU hVo hVH hUV Ξ f 0
  rw [LocalExt.lapTest_zero hU, sub_zero, LocalExt.gradFeat_zsSub_zero, sub_zero] at eV
  simp only [WholeField.rangeKerCF, Coupling.projFactor]
  rw [eM, eV, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Member

/-! ### The hull at a stopping time of a general filtration -/

section Hull

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓗 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Avoidance of a compact set at a stopping time of the usual augmentation is an event of `𝓓_τ`, up to a null
set**, for a driver adapted (before `ζ`) to `𝓗` (`Coupling.exists_drivingStopped_disjoint` for a general
filtration). -/
theorem exists_stopped_disjoint (hWa : AdaptedBefore 𝓗 ζ W)
    (hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (usualAugmentation 𝓗 P) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    ∃ E' : Set Ω, MeasurableSet[hτ.measurableSpace] E' ∧
      E' ⊆ {ω | Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))} ∧
      ∀ᵐ ω ∂P, Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) → ω ∈ E' := by
  set 𝓓 := usualAugmentation 𝓗 P with h𝓓
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  have hτf : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := hτζ.mono fun _ h => ne_top_of_lt_zeta h
  have hτ' : IsStoppingTime 𝓓 fun ω => (τ' ω : WithTop ℝ≥0) := isStoppingTime_untopD (𝓕 := 𝓗) hτ hτf
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[𝓓 0] s := fun s hs h0 =>
    measurableSet_usualAugmentation_of_null (𝓕 := 𝓗) hs h0 0
  have hσeq : hτ.measurableSpace = hτ'.measurableSpace := measurableSpace_untopD_eq hnull hτ hτf hτ'
  obtain ⟨m, hm, hKm⟩ := exists_pos_le_im_of_isCompact hK hKH
  set σ₀ : ℕ → Ω → ℝ≥0 := fun n ω => min (τ' ω) n with hσ₀_def
  have hσ₀ : ∀ n : ℕ, IsStoppingTime 𝓓 fun ω => (σ₀ n ω : WithTop ℝ≥0) := fun n => by
    have h := hτ'.min_const (n : ℝ≥0)
    convert h using 2 with ω
    simp only [hσ₀_def, WithTop.coe_min]
  have hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω := fun ω n n' h =>
    min_le_min le_rfl (by exact_mod_cast h)
  have hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω := fun n => by
    filter_upwards [hτζ] with ω h
    exact lt_of_le_of_lt (by exact_mod_cast min_le_left _ _) (coe_untopD_lt_zeta h)
  obtain ⟨ρ, hρst, hρle, hρmono, hρsafe, hρex⟩ := exists_safeSeq_of_adapted (𝓗 := 𝓗) (P := P)
    hWa hpath hK hKH hm hKm hσ₀ hσ₀m hσ₀ζ
  set good : Ω → Prop := fun ω => ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
    (∀ n : ℕ, IsSafeAt K (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) (ρ n ω)) ∧
    ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω →
      (∀ z ∈ K, ∃ u, IsForwardSol (rpath (W · ω)) z t u) → ∀ᶠ n in atTop, t ≤ ρ n ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, ae_all_iff.2 hρsafe, hρex] with ω h1 h3 h4
    exact ⟨h1.1, h3, h4⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG0 : MeasurableSet[𝓓 0] G := by
    have := (hnull _ hGm.compl hGc).compl
    rwa [compl_compl] at this
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  set F : ℕ → Set Ω := fun n => G ∩ {ω | ρ n ω = τ' ω} with hFdef
  have hGτ : MeasurableSet[hτ'.measurableSpace] G := by
    have h0 := IsStoppingTime.measurableSpace_mono (isStoppingTime_const 𝓓 (0 : ℝ≥0)) hτ'
      (fun ω => WithTop.coe_le_coe.2 (zero_le (a := τ' ω)))
    rw [IsStoppingTime.measurableSpace_const] at h0
    exact h0 _ hG0
  have hF : ∀ n, MeasurableSet[hτ'.measurableSpace] (F n) := fun n => by
    have h := IsStoppingTime.measurableSet_eq_stopping_time hτ' (hρst n)
    have e : {ω | ρ n ω = τ' ω} = {ω | (τ' ω : WithTop ℝ≥0) = (ρ n ω : WithTop ℝ≥0)} := by
      ext ω; simp only [mem_ofPred_eq, WithTop.coe_inj, eq_comm]
    rw [hFdef]; simp only
    rw [e]
    exact hGτ.inter h
  refine ⟨⋃ n, F n, ?_, ?_, ?_⟩
  · rw [hσeq]; exact MeasurableSet.iUnion hF
  · rintro ω ⟨_, ⟨n, rfl⟩, hω, heq⟩
    have hs := (hGgood ω hω).2.1 n
    rw [heq] at hs
    have hw := (hGgood ω hω).1
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    exact notMem_fwdHull_of_alive hw hs.1 (hKH hz) (hs.2.2.2 z hz).1 hzK
  · filter_upwards [hGae] with ω hω hdis
    obtain ⟨-, -, hexh⟩ := hGgood ω hω
    have halive : ∀ z ∈ K, ∃ u, IsForwardSol (rpath (W · ω)) z (τ' ω) u := fun z hz =>
      exists_isForwardSol_of_mem (τ' ω).coe_nonneg ⟨hKH hz, Set.disjoint_left.1 hdis hz⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, τ' ω ≤ (j : ℝ≥0) := by
      obtain ⟨j, hj⟩ := exists_nat_ge (τ' ω); exact ⟨j, hj⟩
    have hτj : τ' ω ≤ σ₀ j ω := le_min le_rfl hj
    obtain ⟨n, hn⟩ := (hexh j (τ' ω) hτj halive).exists
    exact mem_iUnion.2 ⟨n, hω, le_antisymm ((hρle n ω).trans (min_le_left _ _)) hn⟩

end Hull

end InteractingSLE.Sec7.Lemma72D
