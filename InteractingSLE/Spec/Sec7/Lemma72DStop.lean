/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72DMember
import InteractingSLE.Spec.Coupling.SafeFamily
import InteractingSLE.Foundations.Loewner.HullRightCont
import InteractingSLE.Spec.Sec7.Lemma71DUsual
import InteractingSLE.Spec.Coupling.MartMeans2Lemma71

/-!
# Locality at general stopping times, II: from kernels at deterministic times to every stopping time

Packet PROVE-LEMMA72D (ruling R37). Setting: a driver `W` adapted before its lifetime `ζ` to a filtration `𝓗`,
continuous before `ζ` with `W₀ = 0`; `𝓖 = usualAugmentation 𝓗 P`; a zero-boundary GFF `X`. At every rational time `s`
there is a σ-algebra `𝒦_s` given which `X` has a Gaussian kernel `rangeKerCF (M_s) (V_s)` with `V_s ⊇ ℍ ∖ K_s` open and
`M_s` harmonic on `V_s` (on `{s < ζ}`); the events of `𝓖_r`, `r < s`, are (up to null sets) events of `𝒦_s`, and the
safety events `{s < ζ, F ∩ K_s = ∅}` of compact unions of rational balls `F` are (up to null sets) events of `𝒦_s`.

* `exists_hittingVersion_hull_of_adapted`: the hull `K_τ` at a stopping time of `𝓖` has a hitting-measurable version
  with avoidance events in `𝓖_τ` (`Coupling.exists_hittingVersion_hull` for a general filtration);
* `setIntegral_lapTest_stopped` (**the member identity on stopped events**): for `D ∈ 𝓖_τ` on which `K_τ` avoids the
  compact union of rational balls `F`, the projection identity at `U = ⋃ open balls of F` holds on `D`. Proof: cut `D`
  along the dyadic upper approximations `τ_n = (⌈2ⁿτ⌉ + 1)/2ⁿ` (the piece `{⌈2ⁿτ⌉ = k}` of `D` is an event of
  `𝓖_{k/2ⁿ}`, hence of `𝒦_{(k+1)/2ⁿ}`), apply the member identity of the kernel at the deterministic time `τ_n` on the
  safe part, and let `n → ∞` (hull right-continuity: a compact set avoiding `K_τ` avoids `K_{τ+δ}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

namespace InteractingSLE.Sec7.Lemma72D

open QuantumZipper LQGMetric LQGMetric.MarkovZB LocalSets Coupling Ito QuantumZipper.K3 QuantumZipper.Thm11Asm

/-! ### The hull as a random set -/

section Version

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓗 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

open scoped Classical in
/-- **A hitting-measurable version of the hull at a stopping time of the usual augmentation**, with avoidance events
of the stopped σ-algebra up to null sets (`Coupling.exists_hittingVersion_hull` for a general filtration). -/
theorem exists_hittingVersion_hull_of_adapted (hWa : AdaptedBefore 𝓗 ζ W)
    (hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (usualAugmentation 𝓗 P) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    ∃ A : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧
      A =ᵐ[P] (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
      ∀ V : Set ℂ, IsOpen V → V ⊆ H → ∃ E' : Set Ω, MeasurableSet[hτ.measurableSpace] E' ∧
        {ω | Disjoint (A ω) V} =ᵐ[P] E' := by
  set Kτ : Ω → Set ℂ := fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) with hKτ
  have hb : ∀ b : ℚ × ℚ × ℚ, ∃ E' : Set Ω, MeasurableSet[hτ.measurableSpace] E' ∧
      (ratCBall b ⊆ H → ∀ᵐ ω ∂P, (Disjoint (ratCBall b) (Kτ ω) ↔ ω ∈ E')) := by
    intro b
    by_cases hbH : ratCBall b ⊆ H
    · obtain ⟨E', hE'm, hE'sub, hE'ae⟩ :=
        exists_stopped_disjoint hWa hpath (isCompact_ratCBall b) hbH hτ hτζ
      exact ⟨E', hE'm, fun _ => hE'ae.mono fun ω hω => ⟨hω, fun h => hE'sub h⟩⟩
    · exact ⟨∅, @MeasurableSet.empty _ hτ.measurableSpace, fun h => absurd h hbH⟩
  choose E hEm hEae using hb
  have hEm' : ∀ b, MeasurableSet (E b) := fun b => hτ.measurableSpace_le _ (hEm b)
  set good : Ω → Prop := fun ω => ∀ b, ratCBall b ⊆ H → (Disjoint (ratCBall b) (Kτ ω) ↔ ω ∈ E b)
    with hgood_def
  have hgood : ∀ᵐ ω ∂P, good ω := ae_all_iff.2 fun b => by
    by_cases hbH : ratCBall b ⊆ H
    · filter_upwards [hEae b hbH] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hbH
  set S : Set Ω := toMeasurable P {ω | ¬ good ω} with hS
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  have hS0 : P S = 0 := by rw [hS, measure_toMeasurable]; exact ae_iff.1 hgood
  have hSc : ∀ ω, ω ∉ S → good ω := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hSae : ∀ᵐ ω ∂P, ω ∉ S := measure_eq_zero_iff_ae_notMem.1 hS0
  set A : Ω → Set ℂ := fun ω => if ω ∈ S then ∅ else Kτ ω with hA
  have hAae : A =ᵐ[P] Kτ := by
    filter_upwards [hSae] with ω hω
    simp [hA, hω]
  have havoid : ∀ V : Set ℂ, IsOpen V → V ⊆ H → ∀ ω, ω ∉ S →
      (Disjoint (A ω) V ↔ ω ∈ ⋂ b, ⋂ (_ : ratCBall b ⊆ V), E b) := by
    intro V hV hVH ω hω
    simp only [hA, hω, ↓reduceIte, mem_iInter]
    rw [disjoint_iff_forall_ratCBall hV]
    exact forall_congr' fun b => forall_congr' fun hb => hSc ω hω b (hb.trans hVH)
  refine ⟨A, ?_, hAae, fun V hV hVH => ⟨⋂ b, ⋂ (_ : ratCBall b ⊆ V), E b, ?_, ?_⟩⟩
  · refine @measurable_generateFrom _ _ _ _ _ ?_
    rintro _ ⟨U, hU, hUH, rfl⟩
    have e : A ⁻¹' {T : Set ℂ | (T ∩ U).Nonempty} = Sᶜ ∩ (⋂ b, ⋂ (_ : ratCBall b ⊆ U), E b)ᶜ := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
      by_cases hω : ω ∈ S
      · simp [hA, hω]
      · rw [← havoid U hU hUH ω hω, ← not_disjoint_iff_nonempty_inter]
        simp [hω]
    rw [e]
    exact hSm.compl.inter (MeasurableSet.iInter fun b => MeasurableSet.iInter fun _ => hEm' b).compl
  · exact @MeasurableSet.iInter _ _ hτ.measurableSpace _ _ fun b =>
      @MeasurableSet.iInter _ _ hτ.measurableSpace _ _ fun _ => hEm b
  · filter_upwards [hSae] with ω hω
    exact propext (havoid V hV hVH ω hω)

end Version

/-! ### The member identity on stopped events -/

section Stopped

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓗 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens}
  {𝒦 : ℚ≥0 → MeasurableSpace Ω} {M : ℚ≥0 → Ω → DistOn upperHalfPlaneOpens} {V : ℚ≥0 → Ω → Set ℂ}

omit [IsProbabilityMeasure P] in
/-- The ceiling pieces of a stopping time: `D ∩ {⌈2ⁿτ⌉ = k}` is an event of `𝓖_{k/2ⁿ}` for `D ∈ 𝓖_τ`. -/
theorem measurableSet_inter_ceil_eq {𝓖 : Filtration ℝ≥0 mΩ} {τ' : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓖 fun ω => (τ' ω : WithTop ℝ≥0)) {D : Set Ω} (hD : MeasurableSet[hτ.measurableSpace] D)
    (n k : ℕ) :
    MeasurableSet[𝓖 ((k : ℝ≥0) / 2 ^ n)] (D ∩ {ω | ⌈(2 : ℝ≥0) ^ n * τ' ω⌉₊ = k}) := by
  have hp := Lemma71D.two_pow_pos_nnreal n
  have hle : ∀ j : ℕ, {ω | ⌈(2 : ℝ≥0) ^ n * τ' ω⌉₊ ≤ j} = {ω | (τ' ω : WithTop ℝ≥0) ≤ ((j : ℝ≥0) / 2 ^ n : ℝ≥0)} := by
    intro j
    ext ω
    simp only [mem_ofPred_eq, Nat.ceil_le, WithTop.coe_le_coe, le_div_iff₀ hp, mul_comm (τ' ω)]
  have hDle := (IsStoppingTime.measurableSet hτ D).1 hD
  rcases k with _ | j
  · have e : D ∩ {ω | ⌈(2 : ℝ≥0) ^ n * τ' ω⌉₊ = 0} =
        D ∩ {ω | (τ' ω : WithTop ℝ≥0) ≤ (((0 : ℕ) : ℝ≥0) / 2 ^ n : ℝ≥0)} := by
      rw [← hle 0]; simp only [nonpos_iff_eq_zero]
    rw [e]
    exact hDle.2 _
  · have e : D ∩ {ω | ⌈(2 : ℝ≥0) ^ n * τ' ω⌉₊ = j + 1} =
        (D ∩ {ω | (τ' ω : WithTop ℝ≥0) ≤ (((j + 1 : ℕ) : ℝ≥0) / 2 ^ n : ℝ≥0)}) \
          {ω | (τ' ω : WithTop ℝ≥0) ≤ (((j : ℕ) : ℝ≥0) / 2 ^ n : ℝ≥0)} := by
      rw [← hle (j + 1), ← hle j]
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff, not_le]
      constructor
      · rintro ⟨hω, h⟩; refine ⟨⟨hω, h.le⟩, ?_⟩; rw [h]; exact Nat.lt_succ_self j
      · rintro ⟨⟨hω, h1⟩, h2⟩; exact ⟨hω, le_antisymm h1 h2⟩
    rw [e]
    have hjj : ((j : ℝ≥0) / 2 ^ n : ℝ≥0) ≤ (((j + 1 : ℕ) : ℝ≥0) / 2 ^ n : ℝ≥0) := by
      gcongr; exact_mod_cast Nat.le_succ j
    exact (hDle.2 _).diff (𝓖.mono hjj _ (hτ _))

/-- **The member identity on stopped events.** Kernels at rational times as in the module docstring; `τ'` a stopping
time of `𝓖 = usualAugmentation 𝓗 P` with `τ' < ζ`; `U ⊆ F` with `F` a compact union of rational closed balls in `ℍ`.
For every `D ∈ 𝓖_τ` on which `F ∩ K_τ = ∅`, the projection identity at `U` holds on `D`. -/
theorem setIntegral_lapTest_stopped (hXm : Measurable X) (h𝒦 : ∀ s, 𝒦 s ≤ mΩ)
    (hker : ∀ (s : ℚ≥0) (χ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      P[fun ω' => Complex.exp (Complex.I * (X ω' χ : ℂ)) | 𝒦 s] ω = WholeField.rangeKerCF (M s ω) (V s ω) χ)
    (hV : ∀ s : ℚ≥0, ∀ᵐ ω ∂P, (((s : ℝ≥0) : ℝ≥0∞) < ζ ω) → IsOpen (V s ω) ∧ V s ω ⊆ H ∧
      H \ fwdHull (fun r : ℝ => W r.toNNReal ω) ((s : ℝ≥0) : ℝ) ⊆ V s ω ∧ IsHarmonicDistOn (M s ω) (V s ω))
    (hev : ∀ r s : ℚ≥0, r < s → ∀ D, MeasurableSet[usualAugmentation 𝓗 P (r : ℝ≥0)] D →
      ∃ D', MeasurableSet[𝒦 s] D' ∧ D =ᵐ[P] D')
    (hsafe : ∀ (s : ℚ≥0) (F : Finset (ℚ × ℚ × ℚ)), ballsK F ⊆ H → ∃ D', MeasurableSet[𝒦 s] D' ∧
      {ω | ((s : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        Disjoint (ballsK F) (fwdHull (fun r : ℝ => W r.toNNReal ω) ((s : ℝ≥0) : ℝ))} =ᵐ[P] D')
    (hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    {τ' : Ω → ℝ≥0} (hτ : IsStoppingTime (usualAugmentation 𝓗 P) fun ω => (τ' ω : WithTop ℝ≥0))
    (hτζ : ∀ᵐ ω ∂P, (τ' ω : ℝ≥0∞) < ζ ω)
    {F : Finset (ℚ × ℚ × ℚ)} (hFH : ballsK F ⊆ H) {U : Opens ℂ} (hUF : (U : Set ℂ) ⊆ ballsK F)
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens)
    {D : Set Ω} (hD : MeasurableSet[hτ.measurableSpace] D)
    (hDF : ∀ᵐ ω ∂P, ω ∈ D → Disjoint (ballsK F) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ' ω))) :
    ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
      projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P := by
  set 𝓖 := usualAugmentation 𝓗 P with h𝓖
  have hU : U ≤ upperHalfPlaneOpens := hUF.trans hFH
  set F₁ : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) with hF₁
  set F₂ : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω Ξ : ℂ)) with hF₂
  have hF₁m : Measurable F₁ := GFF.measurable_exp_I_mul ((measurable_distOn_apply _).comp hXm)
  have hF₂m : Measurable F₂ := GFF.measurable_exp_I_mul ((measurable_distOn_apply _).comp hXm)
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x =>
    (Complex.norm_exp_I_mul_ofReal x).le
  have hF₁i : Integrable F₁ P := Integrable.of_bound hF₁m.aestronglyMeasurable 1 (ae_of_all _ fun _ => hnorm _)
  have hF₂i : Integrable F₂ P := Integrable.of_bound hF₂m.aestronglyMeasurable 1 (ae_of_all _ fun _ => hnorm _)
  have hDm : MeasurableSet D := hτ.measurableSpace_le _ hD
  -- the times
  set sq : ℕ → ℕ → ℚ≥0 := fun n k => ((k : ℚ≥0) + 1) / 2 ^ n with hsq
  set rq : ℕ → ℕ → ℚ≥0 := fun n k => (k : ℚ≥0) / 2 ^ n with hrq
  have hrs : ∀ n k, rq n k < sq n k := fun n k => by
    simp only [hrq, hsq]; gcongr; exact lt_add_one _
  have hsq' : ∀ n k, ((sq n k : ℚ≥0) : ℝ≥0) = ((k : ℝ≥0) + 1) / 2 ^ n := fun n k => by
    simp only [hsq]; push_cast; rfl
  have hrq' : ∀ n k, ((rq n k : ℚ≥0) : ℝ≥0) = (k : ℝ≥0) / 2 ^ n := fun n k => by
    simp only [hrq]; push_cast; rfl
  -- the pieces and their versions
  set S : ℕ → ℕ → Set Ω := fun n k => D ∩ {ω | ⌈(2 : ℝ≥0) ^ n * τ' ω⌉₊ = k} with hSdef
  have hS𝓖 : ∀ n k, MeasurableSet[𝓖 ((rq n k : ℚ≥0) : ℝ≥0)] (S n k) := fun n k => by
    rw [hrq' n k]; exact measurableSet_inter_ceil_eq hτ hD n k
  have hSm : ∀ n k, MeasurableSet (S n k) := fun n k => 𝓖.le _ _ (hS𝓖 n k)
  choose S' hS'm hSS' using fun n k => hev (rq n k) (sq n k) (hrs n k) (S n k) (hS𝓖 n k)
  choose Sf hSfm hSf using fun n k => hsafe (sq n k) F hFH
  -- the identity on each piece
  have hpiece : ∀ n k, ∫ ω in S n k ∩ Sf n k, F₁ ω ∂P = projFactor U f Ξ * ∫ ω in S n k ∩ Sf n k, F₂ ω ∂P := by
    intro n k
    have hae : S n k ∩ Sf n k =ᵐ[P] S' n k ∩ Sf n k := (hSS' n k).inter EventuallyEq.rfl
    rw [setIntegral_congr_set hae, setIntegral_congr_set hae]
    refine setIntegral_lapTest_of_kernel (h𝒦 _) hXm (hker (sq n k)) hU ((hS'm n k).inter (hSfm n k)) ?_ f Ξ
    filter_upwards [hSf n k, hV (sq n k)] with ω hω hVω hmem
    have hsafeω : ω ∈ {ω | ((sq n k : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        Disjoint (ballsK F) (fwdHull (fun r : ℝ => W r.toNNReal ω) ((sq n k : ℝ≥0) : ℝ))} := by
      have := hω.symm ▸ hmem.2
      exact this
    obtain ⟨hlt, hdis⟩ := hsafeω
    obtain ⟨hVo, hVH, hsub, hharm⟩ := hVω hlt
    refine ⟨hVo, hVH, fun z hz => hsub ⟨hFH (hUF hz), fun hzK => ?_⟩, hharm⟩
    exact Set.disjoint_left.1 hdis (hUF hz) hzK
  -- summing over the pieces
  set G : ℕ → Set Ω := fun n => ⋃ k, S n k ∩ Sf n k with hGdef
  have hdisj : ∀ n, Pairwise (Function.onFun Disjoint fun k => S n k ∩ Sf n k) := fun n i j hij =>
    Set.disjoint_left.2 fun ω hi hj => hij (hi.1.2.symm.trans hj.1.2)
  have hPm : ∀ n k, MeasurableSet (S n k ∩ Sf n k) := fun n k => (hSm n k).inter (h𝒦 _ _ (hSfm n k))
  have hG : ∀ n, ∫ ω in G n, F₁ ω ∂P = projFactor U f Ξ * ∫ ω in G n, F₂ ω ∂P := by
    intro n
    have h1 := hasSum_integral_iUnion (hPm n) (hdisj n) hF₁i.integrableOn
    have h2 := (hasSum_integral_iUnion (hPm n) (hdisj n) hF₂i.integrableOn).mul_left (projFactor U f Ξ)
    exact h1.unique (h2.congr_fun fun k => hpiece n k)
  have hGD : ∀ n, G n ⊆ D := fun n => iUnion_subset fun k => inter_subset_left.trans inter_subset_left
  have hGm : ∀ n, MeasurableSet (G n) := fun n => MeasurableSet.iUnion (hPm n)
  -- every point of `D` is eventually in the pieces
  have hev' : ∀ᵐ ω ∂P, ω ∈ D → ∀ᶠ n in atTop, ω ∈ G n := by
    filter_upwards [hpath, hτζ, hDF, ae_all_iff.2 fun n => ae_all_iff.2 fun k => hSf n k] with ω hw hτω hdis hSfω hωD
    obtain ⟨δ, hδ, hδζ, hδdis⟩ := HullRightCont.exists_pos_disjoint_fwdHull_rpath hw hτω (isCompact_ballsK F) hFH
      (hdis hωD)
    have h2 := Lemma71D.tendsto_two_div_two_pow
    filter_upwards [(h2.eventually (gt_mem_nhds hδ))] with n hn
    set k := ⌈(2 : ℝ≥0) ^ n * τ' ω⌉₊ with hk
    have hdy : ((sq n k : ℚ≥0) : ℝ≥0) = Lemma71D.dyR n (τ' ω) := by rw [hsq' n k]; rfl
    have hle : Lemma71D.dyR n (τ' ω) ≤ τ' ω + δ :=
      (Lemma71D.dyR_le n (τ' ω)).trans (add_le_add_right hn.le _)
    refine mem_iUnion.2 ⟨k, ⟨hωD, hk.symm⟩, ?_⟩
    have hmem : ω ∈ {ω | ((sq n k : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        Disjoint (ballsK F) (fwdHull (fun r : ℝ => W r.toNNReal ω) ((sq n k : ℝ≥0) : ℝ))} := by
      refine ⟨?_, ?_⟩
      · rw [hdy]; exact lt_of_le_of_lt (by exact_mod_cast hle) hδζ
      · rw [hdy]; exact hδdis _ hle
    have := hSfω n k
    rw [← this]
    exact hmem
  -- passing to the limit
  have hlim : ∀ g : Ω → ℂ, Measurable g → (∀ ω, ‖g ω‖ ≤ 1) →
      Tendsto (fun n => ∫ ω in G n, g ω ∂P) atTop (𝓝 (∫ ω in D, g ω ∂P)) := by
    intro g hgm hgb
    simp_rw [← integral_indicator (hGm _), ← integral_indicator hDm]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (hgm.indicator (hGm n)).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => ?_) ?_
    · by_cases hω : ω ∈ G n
      · rw [indicator_of_mem hω]; exact hgb ω
      · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
    · filter_upwards [hev'] with ω hω
      by_cases hωD : ω ∈ D
      · rw [indicator_of_mem hωD]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hω hωD] with n hn
        rw [indicator_of_mem hn]
      · rw [indicator_of_notMem hωD]
        refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
        show 0 = (G n).indicator g ω
        rw [indicator_of_notMem fun h => hωD (hGD n h)]
  have L1 := hlim F₁ hF₁m fun ω => hnorm _
  have L2 := (hlim F₂ hF₂m fun ω => hnorm _).const_mul (projFactor U f Ξ)
  simp_rw [← hG] at L2
  exact tendsto_nhds_unique L1 L2

end Stopped

/-! ### Locality at every stopping time -/

section Local

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓗 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens}
  {𝒦 : ℚ≥0 → MeasurableSpace Ω} {M : ℚ≥0 → Ω → DistOn upperHalfPlaneOpens} {V : ℚ≥0 → Ω → Set ℂ}

/-- **Locality of the hull at every stopping time from Gaussian kernels at deterministic times** (ruling R37; the
proof of `Coupling.isLocalSet_hull_of_isFamilyLocal` with the members of `setIntegral_lapTest_stopped`). `X` a
zero-boundary GFF on `ℍ`; `W` adapted before `ζ` to `𝓗`, continuous before `ζ`, `W₀ = 0`; kernels at rational times
as in `setIntegral_lapTest_stopped`. Then `K_τ` is a local set of `X` at every stopping time `τ < ζ` of the usual
augmentation of `𝓗`. -/
theorem isLocalSet_hull_of_kernels (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P)
    (hWa : AdaptedBefore 𝓗 ζ W)
    (hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0)
    (h𝒦 : ∀ s, 𝒦 s ≤ mΩ)
    (hker : ∀ (s : ℚ≥0) (χ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      P[fun ω' => Complex.exp (Complex.I * (X ω' χ : ℂ)) | 𝒦 s] ω = WholeField.rangeKerCF (M s ω) (V s ω) χ)
    (hV : ∀ s : ℚ≥0, ∀ᵐ ω ∂P, (((s : ℝ≥0) : ℝ≥0∞) < ζ ω) → IsOpen (V s ω) ∧ V s ω ⊆ H ∧
      H \ fwdHull (fun r : ℝ => W r.toNNReal ω) ((s : ℝ≥0) : ℝ) ⊆ V s ω ∧ IsHarmonicDistOn (M s ω) (V s ω))
    (hev : ∀ r s : ℚ≥0, r < s → ∀ D, MeasurableSet[usualAugmentation 𝓗 P (r : ℝ≥0)] D →
      ∃ D', MeasurableSet[𝒦 s] D' ∧ D =ᵐ[P] D')
    (hsafe : ∀ (s : ℚ≥0) (F : Finset (ℚ × ℚ × ℚ)), ballsK F ⊆ H → ∃ D', MeasurableSet[𝒦 s] D' ∧
      {ω | ((s : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        Disjoint (ballsK F) (fwdHull (fun r : ℝ => W r.toNNReal ω) ((s : ℝ≥0) : ℝ))} =ᵐ[P] D')
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (usualAugmentation 𝓗 P) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) X P := by
  classical
  set 𝓖 := usualAugmentation 𝓗 P with h𝓖
  have hhm := hX.measurable
  have hpath' : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := hpath.mono fun ω h => h.1
  obtain ⟨A, hAm, hAK, hAev⟩ := exists_hittingVersion_hull_of_adapted hWa hpath hτ hτζ
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  have hτf : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := hτζ.mono fun _ h => ne_top_of_lt_zeta h
  have hτ𝓖 : IsStoppingTime 𝓖 fun ω => (τ' ω : WithTop ℝ≥0) := isStoppingTime_untopD (𝓕 := 𝓗) hτ hτf
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s := fun s hs h0 =>
    measurableSet_usualAugmentation_of_null (𝓕 := 𝓗) hs h0 0
  have hσeq : hτ.measurableSpace = hτ𝓖.measurableSpace := measurableSpace_untopD_eq hnull hτ hτf hτ𝓖
  have hτζ' : ∀ᵐ ω ∂P, (τ' ω : ℝ≥0∞) < ζ ω := hτζ.mono fun ω h => coe_untopD_lt_zeta h
  have hζ0 : ∀ᵐ ω ∂P, (0 : ℝ≥0∞) < ζ ω := hτζ'.mono fun ω h => lt_of_le_of_lt (by positivity) h
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [ae_hull_subset_isOpen hpath' hτζ', hAK] with ω h1 h2
    rw [h2]
    exact h1
  have hnorm1 : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x =>
    (Complex.norm_exp_I_mul_ofReal x).le
  -- the avoidance events of the rational-ball compacts at `τ`
  have hFav : ∀ F : Finset (ℚ × ℚ × ℚ), ∃ E' : Set Ω, MeasurableSet[hτ𝓖.measurableSpace] E' ∧
      (ballsK F ⊆ H → E' ⊆ {ω | Disjoint (ballsK F) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ' ω))} ∧
        ∀ᵐ ω ∂P, Disjoint (ballsK F) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ' ω)) → ω ∈ E') := by
    intro F
    by_cases hFH : ballsK F ⊆ H
    · obtain ⟨E', hE'm, hE'sub, hE'ae⟩ := exists_stopped_disjoint hWa hpath (isCompact_ballsK F) hFH hτ𝓖
        (hτζ'.mono fun ω h => h)
      refine ⟨E', hE'm, fun _ => ⟨fun ω hω => ?_, ?_⟩⟩
      · have := hE'sub hω
        simpa only [mem_ofPred_eq, WithTop.untopD_coe] using this
      · filter_upwards [hE'ae] with ω hω hdis
        exact hω (by simpa only [WithTop.untopD_coe] using hdis)
    · exact ⟨∅, @MeasurableSet.empty _ hτ𝓖.measurableSpace, fun h => absurd h hFH⟩
  choose Eav hEavm hEav using hFav
  -- the time-zero stopping time (for the constant of the criterion)
  have h0 : IsStoppingTime 𝓖 fun _ : Ω => ((0 : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const 𝓖 0
  have hav : IsAvoidanceLocal A X P := by
    refine isAvoidanceLocal_of_setIntegral_lapTest hX hAm fun V' hV'H => ?_
    have hV' : V' ≤ upperHalfPlaneOpens := hV'H
    obtain ⟨GV, hGV, hGVd⟩ := exists_markovMap V' hV'H
    have hdV := hGVd hX
    refine ⟨GV, hGV, hdV, fun f Ψ => ?_⟩
    set E : Set Ω := {ω | Disjoint (A ω) (V' : Set ℂ)} with hEdef
    have hEm : MeasurableSet E := hAm (measurableSet_avoid V'.isOpen hV'H)
    obtain ⟨E', hE'm, hEE'⟩ := hAev V' V'.isOpen hV'H
    have hEτ : MeasurableSet[hτ𝓖.measurableSpace] E :=
      measurableSet_stopped_of_ae_eq hτ𝓖 hEm (hσeq ▸ hE'm) hEE'
    set Kf : Set ℂ := tsupport f.1 with hKf
    have hKfV : Kf ⊆ V' := f.2.2.2
    have hKfc : IsCompact Kf := f.2.2.1.isCompact
    set Φ : TestOn upperHalfPlaneOpens := lapTest V' f with hΦ
    set c : ℂ := ∫ ω, Complex.exp (Complex.I * (X ω Φ : ℂ)) ∂P with hc_def
    have hQVm : Measurable fun ω => markovCompl GV (X ω) := (measurable_markovCompl hGV).comp hhm
    set b : Ω → ℝ := fun ω => markovCompl GV (X ω) Ψ with hb_def
    have hbm : Measurable b := (measurable_distOn_apply Ψ).comp hQVm
    have hhΦm : Measurable fun ω => X ω Φ := (measurable_distOn_apply Φ).comp hhm
    have hF₂m : Measurable fun ω => Complex.exp (Complex.I * (b ω : ℂ)) := GFF.measurable_exp_I_mul hbm
    have hF₁m : Measurable fun ω => Complex.exp (Complex.I * (X ω Φ : ℂ)) *
        Complex.exp (Complex.I * (b ω : ℂ)) := (GFF.measurable_exp_I_mul hhΦm).mul hF₂m
    have hF₁i : Integrable (fun ω => Complex.exp (Complex.I * (X ω Φ : ℂ)) *
        Complex.exp (Complex.I * (b ω : ℂ))) P :=
      Integrable.of_bound hF₁m.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
        rw [norm_mul, Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal, one_mul])
    have hF₂i : Integrable (fun ω => Complex.exp (Complex.I * (b ω : ℂ))) P :=
      Integrable.of_bound hF₂m.aestronglyMeasurable 1 (Eventually.of_forall fun ω => hnorm1 _)
    -- the Dirichlet approximation of the complementary projection
    obtain ⟨g, hg, hgL2⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hV' hdV Ψ
    set Ξ : ℕ → TestOn upperHalfPlaneOpens := fun n => Ψ - lapTest V' (g n) with hΞ
    set a : ℕ → Ω → ℝ := fun n ω => X ω (Ξ n) with ha_def
    have ham : ∀ n, Measurable (a n) := fun n => (measurable_distOn_apply _).comp hhm
    have hab : ∀ n ω, a n ω - b ω = GV (X ω) Ψ - X ω (lapTest V' (g n)) := fun n ω => by
      simp only [a, b, hΞ, map_sub, markovCompl, sub_apply]
      ring
    have hmem : ∀ n, MemLp (fun ω => a n ω - b ω) 2 P := fun n => by
      have h1 := memLp_markov_sub_lapTest hV' hdV Ψ (g n)
      convert h1 using 1
      funext ω
      exact hab n ω
    have hlim : Tendsto (fun n => ∫ ω, (a n ω - b ω) ^ 2 ∂P) atTop (𝓝 0) := by
      refine hgL2.congr fun n => integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hab n ω]
    set C : Finset (ℚ × ℚ × ℚ) → Set Ω := fun F =>
      if Kf ⊆ ballsU F ∧ ballsK F ⊆ V' then E ∩ Eav F else ∅ with hC
    have hCm : ∀ F, MeasurableSet[hτ𝓖.measurableSpace] (C F) := fun F => by
      by_cases hi : Kf ⊆ ballsU F ∧ ballsK F ⊆ V'
      · simp only [hC, hi, and_self, ↓reduceIte]
        exact @MeasurableSet.inter Ω hτ𝓖.measurableSpace _ _ hEτ (hEavm F)
      · simp only [hC, hi, ↓reduceIte]; exact @MeasurableSet.empty Ω hτ𝓖.measurableSpace
    have hCE : ∀ F, C F ⊆ E := fun F => by
      by_cases hi : Kf ⊆ ballsU F ∧ ballsK F ⊆ V'
      · simp only [hC, hi, and_self, ↓reduceIte]; exact inter_subset_left
      · simp only [hC, hi, ↓reduceIte]; exact empty_subset _
    have hEC : ∀ᵐ ω ∂P, ω ∈ E → ∃ F, ω ∈ C F := by
      filter_upwards [hAK, hτζ', hpath', ae_all_iff.2 fun F => (show ∀ᵐ ω ∂P, ballsK F ⊆ H →
          Disjoint (ballsK F) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ' ω)) → ω ∈ Eav F from by
        by_cases hFH : ballsK F ⊆ H
        · filter_upwards [(hEav F hFH).2] with ω hω _ using hω
        · exact Eventually.of_forall fun ω h => absurd h hFH)] with ω hAω hτω hwω hFω hωE
      have hdis : Disjoint (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ' ω)) (V' : Set ℂ) := by
        have h1 : Disjoint (A ω) (V' : Set ℂ) := hωE
        rwa [hAω] at h1
      have hO : IsOpen ((V' : Set ℂ) ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (τ' ω))) :=
        V'.isOpen.inter (MartMeans2.isOpen_H_diff_fwdHull_rpath hwω hτω)
      have hKO : Kf ⊆ (V' : Set ℂ) ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (τ' ω)) := fun z hz =>
        ⟨hKfV hz, hV'H (hKfV hz), fun hzK => Set.disjoint_left.1 hdis hzK (hKfV hz)⟩
      obtain ⟨F, hKF, hFO⟩ := exists_rationalBalls hKfc hO hKO
      have hFV : ballsK F ⊆ V' := hFO.trans inter_subset_left
      have hFH : ballsK F ⊆ H := hFV.trans hV'H
      have hFdis : Disjoint (ballsK F) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ' ω)) :=
        Set.disjoint_left.2 fun z hz hzK => ((hFO hz).2).2 hzK
      refine ⟨F, ?_⟩
      simp only [hC, hKF, hFV, and_self, ↓reduceIte]
      exact ⟨hωE, hFω F hFH hFdis⟩
    have hpiece : ∀ F D, MeasurableSet[hτ𝓖.measurableSpace] D → D ⊆ C F →
        ∫ ω in D, Complex.exp (Complex.I * (X ω Φ : ℂ)) * Complex.exp (Complex.I * (b ω : ℂ)) ∂P =
          c * ∫ ω in D, Complex.exp (Complex.I * (b ω : ℂ)) ∂P := by
      intro F D hD hDC
      by_cases hi : Kf ⊆ ballsU F ∧ ballsK F ⊆ V'
      swap
      · have hD0 : D = ∅ := Set.subset_empty_iff.1 (hDC.trans (by simp only [hC, hi, ↓reduceIte]; rfl))
        simp [hD0]
      have hDC' : D ⊆ E ∩ Eav F := by simpa only [hC, hi, and_self, ↓reduceIte] using hDC
      have hFH : ballsK F ⊆ H := hi.2.trans hV'H
      have hDF : ∀ᵐ ω ∂P, ω ∈ D → Disjoint (ballsK F) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ' ω)) :=
        Eventually.of_forall fun ω hω => (hEav F hFH).1 (hDC' hω).2
      have hDm : MeasurableSet D := hτ𝓖.measurableSpace_le _ hD
      set U : Opens ℂ := ⟨ballsU F, isOpen_ballsU F⟩ with hUdef
      have hUF : (U : Set ℂ) ⊆ ballsK F := ballsU_subset_ballsK F
      have hUV : (U : Set ℂ) ⊆ V' := hUF.trans hi.2
      have hUi : U ≤ upperHalfPlaneOpens := hUV.trans hV'H
      set f' : zsSub (U : Set ℂ) := ⟨f.1, ⟨f.2.1, f.2.2.1, hi.1⟩⟩ with hf'
      have hΦ' : Φ = lapTest U f' := by
        ext z
        rw [hΦ, coe_lapTest hV', coe_lapTest hUi]
        rfl
      have hmembD : ∀ Ξ' : TestOn upperHalfPlaneOpens,
          ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest U f' + Ξ') : ℂ)) ∂P =
            projFactor U f' Ξ' * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ' : ℂ)) ∂P := fun Ξ' =>
        setIntegral_lapTest_stopped hhm h𝒦 hker hV hev hsafe hpath' hτ𝓖 hτζ' hFH hUF f' Ξ' hD hDF
      set r : ℕ → ℝ := fun n => -(1 / 2) * ‖gradFeat (U : Set ℂ) f'.1‖ ^ 2 -
        ⟪gradFeat (U : Set ℂ) f'.1, covVec (U : Set ℂ) (Ξ n)⟫ with hr_def
      -- the member identity along the approximations
      have hmemb : ∀ n, ∫ ω in D, Complex.exp (Complex.I * (X ω Φ : ℂ)) *
          Complex.exp (Complex.I * (a n ω : ℂ)) ∂P =
            Complex.exp ((r n : ℝ) : ℂ) * ∫ ω in D, Complex.exp (Complex.I * (a n ω : ℂ)) ∂P := by
        intro n
        have key := hmembD (Ξ n)
        rw [← hΦ'] at key
        rw [show Complex.exp ((r n : ℝ) : ℂ) = projFactor U f' (Ξ n) from rfl, ← key]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [a, map_add, Complex.ofReal_add, mul_add, Complex.exp_add]
      -- the exponents converge
      have hfV : f'.1 ∈ zeroSpace (U : Set ℂ) := f'.2
      have hinner : ∀ n, ⟪gradFeat (U : Set ℂ) f'.1, covVec (U : Set ℂ) (Ξ n)⟫ =
          ⟪gradFeat (V' : Set ℂ) f.1, covVec (V' : Set ℂ) Ψ⟫ - ⟪gradFeat (V' : Set ℂ) f.1,
            gradFeat (V' : Set ℂ) (g n).1⟫ := fun n => by
        rw [hΞ, covVec_sub U.isOpen hUi, inner_sub_right,
          ← inner_gradFeat_covVec_eq U.isOpen V'.isOpen hV'H hUV hfV Ψ,
          ← inner_gradFeat_covVec_eq U.isOpen V'.isOpen hV'H hUV hfV (lapTest V' (g n)),
          covVec_lapTest hV' V'.isOpen hV'H subset_rfl (g n)]
      have hr : Tendsto r atTop (𝓝 (-(1 / 2) * ‖gradFeat (U : Set ℂ) f'.1‖ ^ 2)) := by
        have h1 : Tendsto (fun n => ⟪gradFeat (V' : Set ℂ) f.1, gradFeat (V' : Set ℂ) (g n).1⟫) atTop
            (𝓝 ⟪gradFeat (V' : Set ℂ) f.1, covVec (V' : Set ℂ) Ψ⟫) :=
          tendsto_const_nhds.inner hg
        have h2 : Tendsto (fun n => ⟪gradFeat (U : Set ℂ) f'.1, covVec (U : Set ℂ) (Ξ n)⟫) atTop
            (𝓝 0) := by
          simp_rw [hinner]
          simpa using (tendsto_const_nhds (x := ⟪gradFeat (V' : Set ℂ) f.1, covVec (V' : Set ℂ) Ψ⟫)).sub h1
        have h3 := (tendsto_const_nhds (x := -(1 / 2) * ‖gradFeat (U : Set ℂ) f'.1‖ ^ 2)).sub h2
        rw [sub_zero] at h3
        exact h3
      -- the constant `c`, from the member identity at time `0`
      have hc : c = Complex.exp (((-(1 / 2) * ‖gradFeat (U : Set ℂ) f'.1‖ ^ 2 : ℝ) : ℂ)) := by
        have hD0 : ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) → Disjoint (ballsK F)
            (fwdHull (fun s : ℝ => W s.toNNReal ω) (((fun _ : Ω => (0 : ℝ≥0)) ω : ℝ≥0) : ℝ)) := by
          filter_upwards [hpath', hζ0] with ω hw hz _
          have e := MartMeans2.fwdHull_rpath_zero hw hz
          simp only [NNReal.coe_zero]
          rw [show (fun s : ℝ => W s.toNNReal ω) = rpath (W · ω) from rfl, e]
          exact disjoint_empty _
        have key := setIntegral_lapTest_stopped hhm h𝒦 hker hV hev hsafe hpath' h0
          (hζ0.mono fun ω h => by exact_mod_cast h) hFH hUF f' 0 (@MeasurableSet.univ _ h0.measurableSpace) hD0
        rw [← hΦ', add_zero] at key
        simp only [Measure.restrict_univ] at key
        rw [hc_def, key, projFactor, covVec_zero _ U.isOpen hUi, inner_zero_right, sub_zero]
        simp
      -- the limits
      have hZ1 : ∀ ω, ‖D.indicator (fun ω => Complex.exp (Complex.I * (X ω Φ : ℂ))) ω‖ ≤ 1 := fun ω => by
        by_cases hω : ω ∈ D
        · rw [indicator_of_mem hω]; exact hnorm1 _
        · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
      have hZ2 : ∀ ω, ‖D.indicator (fun _ => (1 : ℂ)) ω‖ ≤ 1 := fun ω => by
        by_cases hω : ω ∈ D
        · rw [indicator_of_mem hω, norm_one]
        · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
      have hZ1m : Measurable (D.indicator fun ω => Complex.exp (Complex.I * (X ω Φ : ℂ))) :=
        (GFF.measurable_exp_I_mul hhΦm).indicator hDm
      have hZ2m : Measurable (D.indicator fun _ => (1 : ℂ)) := measurable_const.indicator hDm
      have e1 : ∀ x : Ω → ℝ, ∫ ω in D, Complex.exp (Complex.I * (X ω Φ : ℂ)) *
          Complex.exp (Complex.I * (x ω : ℂ)) ∂P = ∫ ω, Complex.exp (Complex.I * (x ω : ℂ)) *
            D.indicator (fun ω => Complex.exp (Complex.I * (X ω Φ : ℂ))) ω ∂P := fun x => by
        rw [← setIntegral_eq_integral_indicator_mul hDm]
        exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
      have e2 : ∀ x : Ω → ℝ, ∫ ω in D, Complex.exp (Complex.I * (x ω : ℂ)) ∂P =
          ∫ ω, Complex.exp (Complex.I * (x ω : ℂ)) * D.indicator (fun _ => (1 : ℂ)) ω ∂P := fun x => by
        rw [← setIntegral_eq_integral_indicator_mul hDm]
        exact integral_congr_ae (Eventually.of_forall fun ω => (mul_one _).symm)
      have hL1 := tendsto_integral_cexp_mul_of_tendsto_integral_sq hmem hlim hZ1
        (fun n => ((GFF.measurable_exp_I_mul (ham n)).mul hZ1m).aestronglyMeasurable)
        ((GFF.measurable_exp_I_mul hbm).mul hZ1m).aestronglyMeasurable
      have hL2 := tendsto_integral_cexp_mul_of_tendsto_integral_sq hmem hlim hZ2
        (fun n => ((GFF.measurable_exp_I_mul (ham n)).mul hZ2m).aestronglyMeasurable)
        ((GFF.measurable_exp_I_mul hbm).mul hZ2m).aestronglyMeasurable
      simp_rw [← e1] at hL1
      simp_rw [← e2] at hL2
      have hR := ((Complex.continuous_exp.comp Complex.continuous_ofReal).tendsto _).comp hr
      have hRL := hR.mul hL2
      simp_rw [Function.comp_apply, ← hmemb] at hRL
      rw [hc]
      exact tendsto_nhds_unique hL1 hRL
    exact setIntegral_eq_mul_of_pieces hτ𝓖.measurableSpace_le hF₁i hF₂i c C hCm hCE hEC hpiece
  have hloc : IsLocalSet A X P := ((isLocalSet_tfae hX hAm hAc).out 1 4).1 hav
  exact IsLocalSet.congr_set hloc hAK.symm

end Local

end InteractingSLE.Sec7.Lemma72D
