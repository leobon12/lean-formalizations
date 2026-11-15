/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedK2Clause

/-!
# The stopped K2, part 3: locality of `K_τ` from stopped member identities

Packet PROVE-STOPPEDK2. `DomainMarkov.isLocalSet_hull_of_members` proves the locality of the hull `K_τ` at a stopping
time `τ < ζ` from member identities at rational times, which it only uses through two consequences: the member identity
on the events of `𝓕_τ` inside `{ballsK F ∩ K_τ = ∅}` (`DomainMarkov.setIntegral_lapTest_stopped_of_members`) and the
identity at time `0` (the constant of the criterion). **`isLocalSet_hull_of_stoppedMembers`** is that proof with these
two identities as hypotheses (copied with this modification from `Restart/DomainMarkovLocCrit.lean`), so that it
applies at a stopping time `τ ≤ V` of a process killed at `V`, where the member identity at `τ` comes from below
(`StoppedK2ClauseMember.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

namespace InteractingSLE.Restart.StoppedK2

open QuantumZipper LQGMetric LQGMetric.MarkovZB LocalSets Coupling Ito QuantumZipper.K3 QuantumZipper.Thm11Asm
open Sec7.Lemma72D DomainMarkov

section Local

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓗 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens}

/-- **Locality of the hull at a stopping time from the stopped member identities** (the proof of
`DomainMarkov.isLocalSet_hull_of_members`, with its two uses of the rational member identities replaced by the
hypotheses `hmτ`, the member identity on the events of `𝓕_τ` avoiding `K_τ`, and `hm0`, the identity at time `0`). -/
theorem isLocalSet_hull_of_stoppedMembers (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P)
    (hWa : AdaptedBefore 𝓗 ζ W)
    (hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (usualAugmentation 𝓗 P) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    (hmτ : ∀ F : Finset (ℚ × ℚ × ℚ), ballsK F ⊆ H → ∀ (f : zsSub (ballsU F)) (Ξ : TestOn upperHalfPlaneOpens)
      (D : Set Ω), MeasurableSet[hτ.measurableSpace] D →
      (∀ᵐ ω ∂P, ω ∈ D → Disjoint (ballsK F) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))) →
      ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest (ballsOpen F) f + Ξ) : ℂ)) ∂P =
        projFactor (ballsOpen F) f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P)
    (hm0 : ∀ F : Finset (ℚ × ℚ × ℚ), ballsK F ⊆ H → ∀ f : zsSub (ballsU F),
      ∫ ω in (univ : Set Ω), Complex.exp (Complex.I * (X ω (lapTest (ballsOpen F) f + 0) : ℂ)) ∂P =
        projFactor (ballsOpen F) f 0 * ∫ ω in (univ : Set Ω), Complex.exp (Complex.I * (X ω 0 : ℂ)) ∂P) :
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
        V'.isOpen.inter (Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath hwω hτω)
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
      set U : Opens ℂ := ballsOpen F with hUdef
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
        hmτ F hFH f' Ξ' D (hσeq ▸ hD) hDF
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
        have key := hm0 F hFH f'
        rw [← hΦ', add_zero] at key
        simp only [Measure.restrict_univ] at key
        rw [hc_def, key, projFactor, covVec_zero _ U.isOpen hUi, inner_zero_right, sub_zero]
        simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
          integral_const, Complex.real_smul, mul_one]
        simp
        rfl
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

/-! ### The member identity at a stopping time `τ ≤ V`, from below -/

section Member

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ν : Measure Ω}
  {X : Ω → DistOn upperHalfPlaneOpens}

omit mΩ in
theorem untopD_min_le {a b : WithTop ℝ≥0} (ha : a ≠ ⊤) : (min a b).untopD 0 ≤ a.untopD 0 := by
  obtain ⟨a', rfl⟩ := WithTop.ne_top_iff_exists.1 ha
  induction b using WithTop.recTopCoe with
  | top => rw [min_eq_left le_top]
  | coe b' => rw [← WithTop.coe_min, WithTop.untopD_coe, WithTop.untopD_coe]; exact min_le_left _ _

/-- **Set integrals give conditional expectations on an event.** If `∫_D Y₁ = c ∫_D Y₂` for every `D ∈ m` inside
`E ∈ m`, then `E[Y₁ | m] = c E[Y₂ | m]` almost everywhere on `E`. -/
theorem ae_condExp_eq_mul_of_setIntegral [IsFiniteMeasure ν] (hm : 𝒢 ≤ mΩ) {E : Set Ω}
    (hE : MeasurableSet[𝒢] E) {Y₁ Y₂ : Ω → ℂ} (h1 : Integrable Y₁ ν) (h2 : Integrable Y₂ ν) (c : ℂ)
    (h : ∀ D, MeasurableSet[𝒢] D → D ⊆ E → ∫ ω in D, Y₁ ω ∂ν = c * ∫ ω in D, Y₂ ω ∂ν) :
    ∀ᵐ ω ∂ν, ω ∈ E → ν[Y₁ | 𝒢] ω = c * ν[Y₂ | 𝒢] ω := by
  have hEm : MeasurableSet[mΩ] E := hm E hE
  have key : E.indicator (ν[Y₁ | 𝒢]) =ᵐ[ν] E.indicator (fun ω => c * ν[Y₂ | 𝒢] ω) := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm
      (fun _ _ _ => (integrable_condExp.indicator hEm).integrableOn)
      (fun _ _ _ => ((integrable_condExp.const_mul c).indicator hEm).integrableOn) (fun s hs _ => ?_)
      ((stronglyMeasurable_condExp.indicator hE).aestronglyMeasurable)
      (((stronglyMeasurable_condExp.const_mul c).indicator hE).aestronglyMeasurable)
    rw [setIntegral_indicator hEm, setIntegral_indicator hEm, integral_const_mul,
      setIntegral_condExp hm h1 (hs.inter hE), setIntegral_condExp hm h2 (hs.inter hE)]
    exact h _ (hs.inter hE) inter_subset_right
  filter_upwards [key] with ω hω hωE
  simpa only [indicator_of_mem hωE] using hω

open Sec7.Lemma72D in
/-- **The member identity at every stopping time `τ ≤ V`, from below.** For the driving filtration of `(W, VL, VR)`
killed at `V`, with member identities at rational times (`HasRatMembers`, lifetime `V`) and stopping times `σₙ < V`
announcing `V`: on every event `D ∈ 𝓕_τ` on which `ballsK F` avoids `K_τ`,
`∫_D e^{i X(−Δf/2π + Ξ)} = projFactor f Ξ · ∫_D e^{i X(Ξ)}`. At `τ ∧ σₙ < V` the identity holds on the events of
`𝓕_{τ ∧ σₙ}` avoiding `K_{τ ∧ σₙ}` (`setIntegral_lapTest_stopped_of_members`), hence for the conditional expectations
on that avoidance event; Lévy's upward theorem along `τ ∧ σₙ` passes it to `𝓕_τ` on the avoidance event at `τ`. -/
theorem setIntegral_lapTest_le_stop [IsProbabilityMeasure ν] (hX : IsMeasurableKilledDriving W VL VR V)
    (hXm : Measurable X) (hmb : HasRatMembers ν (killedDrivingFiltration hX) W V X)
    (hpath : ∀ᵐ ω ∂ν, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < V ω} ∧ W 0 ω = 0)
    {σ : ℕ → Ω → WithTop ℝ≥0} (hσ : ∀ n, IsStoppingTime (drivingFiltration ν hX) (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω) (hσV : ∀ᵐ ω ∂ν, ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂ν, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration ν hX) τ)
    (hτV : ∀ᵐ ω ∂ν, (τ ω : ℝ≥0∞) ≤ V ω ∧ τ ω ≠ ⊤)
    {F : Finset (ℚ × ℚ × ℚ)} (hFH : ballsK F ⊆ H) (f : zsSub (ballsU F)) (Ξ : TestOn upperHalfPlaneOpens)
    {D : Set Ω} (hD : MeasurableSet[hτ.measurableSpace] D)
    (hDF : ∀ᵐ ω ∂ν, ω ∈ D → Disjoint (ballsK F) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))) :
    ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest (ballsOpen F) f + Ξ) : ℂ)) ∂ν =
      projFactor (ballsOpen F) f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂ν := by
  set 𝓚 := killedDrivingFiltration hX with h𝓚
  set c := projFactor (ballsOpen F) f Ξ with hc
  set Y₁ : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω (lapTest (ballsOpen F) f + Ξ) : ℂ)) with hY₁
  set Y₂ : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω Ξ : ℂ)) with hY₂
  have hY₁i : Integrable Y₁ ν := Integrable.of_bound
    (GFF.measurable_exp_I_mul ((measurable_distOn_apply _).comp hXm)).aestronglyMeasurable 1
    (ae_of_all _ fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  have hY₂i : Integrable Y₂ ν := Integrable.of_bound
    (GFF.measurable_exp_I_mul ((measurable_distOn_apply _).comp hXm)).aestronglyMeasurable 1
    (ae_of_all _ fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  have hnull : ∀ s : Set Ω, MeasurableSet s → ν s = 0 → MeasurableSet[drivingFiltration ν hX 0] s :=
    fun s hs h0 => measurableSet_usualAugmentation_of_null (𝓕 := 𝓚) hs h0 0
  -- the identity at `τ ∧ σₙ`, for the conditional expectations on the avoidance event
  have hn : ∀ n, ∀ᵐ ω ∂ν, Disjoint (ballsK F)
      (fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (τ ω) (σ n ω)).untopD 0 : ℝ≥0)) →
      ν[Y₁ | (hτ.min (hσ n)).measurableSpace] ω = c * ν[Y₂ | (hτ.min (hσ n)).measurableSpace] ω := by
    intro n
    have hfin : ∀ᵐ ω ∂ν, min (τ ω) (σ n ω) ≠ ⊤ := by
      filter_upwards [hτV] with ω hω h
      exact hω.2 (eq_top_iff.2 (h ▸ min_le_left _ _))
    have hτn := isStoppingTime_untopD (𝓕 := 𝓚) (hτ.min (hσ n)) hfin
    have hσeq := measurableSpace_untopD_eq hnull (hτ.min (hσ n)) hfin hτn
    have hlt : ∀ᵐ ω ∂ν, ((((min (τ ω) (σ n ω)).untopD 0 : ℝ≥0)) : ℝ≥0∞) < V ω := by
      filter_upwards [hσV, hfin] with ω hω hf
      obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hf
      rw [← hb, WithTop.untopD_coe]
      have := lt_of_le_of_lt (min_le_right (τ ω) (σ n ω)) (hω n)
      rw [← hb] at this
      exact this
    obtain ⟨E, hEm, hEsub, hEae⟩ := exists_stopped_disjoint (adaptedBefore_killedDriving_W hX) hpath
      (isCompact_ballsK F) hFH hτn (hlt.mono fun ω h => h)
    have hid := ae_condExp_eq_mul_of_setIntegral hτn.measurableSpace_le hEm hY₁i hY₂i c fun D' hD' hD'E =>
      setIntegral_lapTest_stopped_of_members hXm hmb (hpath.mono fun ω h => h.1) hτn hlt hFH f Ξ hD'
        (ae_of_all _ fun ω hω => by simpa only [mem_ofPred_eq, WithTop.untopD_coe] using hEsub (hD'E hω))
    have hid' : ∀ᵐ ω ∂ν, ω ∈ E → ν[Y₁ | (hτ.min (hσ n)).measurableSpace] ω =
        c * ν[Y₂ | (hτ.min (hσ n)).measurableSpace] ω := by
      rw [hσeq]; exact hid
    filter_upwards [hid', hEae] with ω h1 h2 hdis
    exact h1 (h2 (by simpa only [WithTop.untopD_coe] using hdis))
  -- Lévy's upward theorem along `τ ∧ σₙ`
  have hl₁ := ae_tendsto_condExp_stopMin hX hτ hσ hσm hσlim hY₁i
  have hl₂ := ae_tendsto_condExp_stopMin hX hτ hσ hσm hσlim hY₂i
  have hlim : ∀ᵐ ω ∂ν, Disjoint (ballsK F)
      (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      ν[Y₁ | hτ.measurableSpace] ω = c * ν[Y₂ | hτ.measurableSpace] ω := by
    filter_upwards [ae_all_iff.2 hn, hl₁, hl₂, hτV] with ω hnω h1 h2 hτω hdis
    have hdn : ∀ n, Disjoint (ballsK F)
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (τ ω) (σ n ω)).untopD 0 : ℝ≥0)) := fun n =>
      hdis.mono_right (QuantumZipper.fwdHull_mono.1 (by exact_mod_cast untopD_min_le hτω.2))
    refine tendsto_nhds_unique h1 ?_
    exact (h2.const_mul c).congr fun n => (hnω n (hdn n)).symm
  have hDm : MeasurableSet D := hτ.measurableSpace_le _ hD
  rw [← setIntegral_condExp hτ.measurableSpace_le hY₁i hD, ← setIntegral_condExp hτ.measurableSpace_le hY₂i hD,
    ← integral_const_mul]
  refine setIntegral_congr_ae hDm ?_
  filter_upwards [hlim, hDF] with ω h1 h2 hωD
  exact h1 (h2 hωD)

/-- **Locality of `K_τ` at every stopping time `τ ≤ V`, from below.** For the driving filtration of `(W, VL, VR)`
killed at `V`, a zero-boundary GFF `X` with member identities at rational times (`HasRatMembers`, lifetime `V`), a
driver continuous on all of `ℝ≥0` and adapted to the killed filtration at every time (the process frozen after `V`),
`V > 0`, and stopping times `σₙ < V` announcing `V`: the hull `K_τ` is a local set of `X` at every stopping time
`τ ≤ V`, `τ < ∞` (`isLocalSet_hull_of_stoppedMembers` with lifetime `⊤`, the member identity at `τ` from
`setIntegral_lapTest_le_stop`, the one at `0` from `setIntegral_lapTest_stopped_of_members`). -/
theorem isLocalSet_hull_le_stop [IsProbabilityMeasure ν] (hX : IsMeasurableKilledDriving W VL VR V)
    (hXgff : IsZeroBoundaryGFF upperHalfPlaneOpens X ν) (hmb : HasRatMembers ν (killedDrivingFiltration hX) W V X)
    (hpath : ∀ᵐ ω ∂ν, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < V ω} ∧ W 0 ω = 0)
    (hV0 : ∀ᵐ ω ∂ν, 0 < V ω) (hWa : AdaptedBefore (killedDrivingFiltration hX) (fun _ => ⊤) W)
    (hcont : ∀ᵐ ω ∂ν, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ⊤} ∧ W 0 ω = 0)
    {σ : ℕ → Ω → WithTop ℝ≥0} (hσ : ∀ n, IsStoppingTime (drivingFiltration ν hX) (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω) (hσV : ∀ᵐ ω ∂ν, ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂ν, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration ν hX) τ)
    (hτV : ∀ᵐ ω ∂ν, (τ ω : ℝ≥0∞) ≤ V ω ∧ τ ω ≠ ⊤) :
    IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) X ν := by
  have hXm := hXgff.measurable
  have h0 := isStoppingTime_const (usualAugmentation (killedDrivingFiltration hX) ν) (0 : ℝ≥0)
  refine isLocalSet_hull_of_stoppedMembers (𝓗 := killedDrivingFiltration hX) (ζ := fun _ => ⊤) hXgff hWa hcont hτ
    (hτV.mono fun ω h => lt_top_iff_ne_top.2 h.2)
    (fun F hFH f Ξ D hD hDF => setIntegral_lapTest_le_stop hX hXm hmb hpath hσ hσm hσV hσlim hτ hτV hFH f Ξ hD hDF)
    (fun F hFH f => ?_)
  have hD0 : ∀ᵐ ω ∂ν, ω ∈ (univ : Set Ω) → Disjoint (ballsK F)
      (fwdHull (fun s : ℝ => W s.toNNReal ω) (((fun _ : Ω => (0 : ℝ≥0)) ω : ℝ≥0) : ℝ)) := by
    filter_upwards [hpath, hV0] with ω hw hz _
    have e := Coupling.MartMeans2.fwdHull_rpath_zero hw.1 hz
    simp only [NNReal.coe_zero]
    rw [show (fun s : ℝ => W s.toNNReal ω) = rpath (W · ω) from rfl, e]
    exact disjoint_empty _
  exact setIntegral_lapTest_stopped_of_members hXm hmb (hpath.mono fun ω h => h.1) (τ' := fun _ => 0) h0
    (hV0.mono fun ω h => by exact_mod_cast h) hFH f 0 (@MeasurableSet.univ _ h0.measurableSpace) hD0

end Member

end InteractingSLE.Restart.StoppedK2
