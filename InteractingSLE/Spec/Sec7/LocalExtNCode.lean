/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtNMarks
import InteractingSLE.Spec.Sec7.LocalExtNIndep

/-!
# Aux. lemma 54, (Loc) after the stop: history-marked locality of the stopped coupling at its stop

Packet PROVE-LOCEXT-N. For a stopped seed coupling through its stop `S` and the centred field `X = h − T₀`, the projection
`G X` onto `H(U)` is independent of the complementary projection `X − G X` together with the **marked avoidance events**
`{y ∈ N} ∩ {K_S ∩ V = ∅}` (`y` the two-seed history at `S`, `N` a pre-stop mark `{t < y.1, truncH t y ∈ Γ}` or everything,
`V ⊇ U` open in `ℍ`; `markSigmaQ`). This is the history-marked locality at `S` (step (P4) of PROVE-LOCEXT-L's plan).

Proof. On a generator the projection identity is the limit `t₂ → ∞` of PROVE-LOCEXT-L's pre-stop identity on
`{t < S, truncH t y ∈ Γ, C ∩ K_{t₂ ∧ S} = ∅}` (coding stops below `S`; `setIntegral_lapTest_mark`): on a regular stop the
events agree for `t₂ ≥ S`. The identity on the whole space is the Markov decomposition of the GFF
(`integral_lapTest_eq_of_isMarkovDecomposition`), so it extends to the generated σ-algebra (Dynkin), and
`indep_markov_of_setIntegral_lapTest` gives the independence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric LQGMetric.MarkovZB Coupling LocalSets Ito QuantumZipper.K3 QuantumZipper.Thm11Asm

section Code

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-! ### The projection identity on the marked avoidance events at the stop -/

/-- Set integrals of a bounded function over events that eventually agree with a limit event almost surely
converge. -/
theorem tendsto_setIntegral_of_ae_eventually {P : Measure Ω} [IsFiniteMeasure P] {E : ℕ → Set Ω} {m : Set Ω}
    (hE : ∀ n, MeasurableSet (E n)) (hm : MeasurableSet m) (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (ω ∈ E n ↔ ω ∈ m))
    {F : Ω → ℂ} (hF : AEStronglyMeasurable F P) (hFb : ∀ ω, ‖F ω‖ ≤ 1) :
    Tendsto (fun n => ∫ ω in E n, F ω ∂P) atTop (𝓝 (∫ ω in m, F ω ∂P)) := by
  simp_rw [← integral_indicator (hE _), ← integral_indicator hm]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => hF.indicator (hE n))
    (integrable_const _) (fun n => Eventually.of_forall fun ω => ?_) ?_
  · by_cases hω : ω ∈ E n
    · rw [indicator_of_mem hω]; exact hFb ω
    · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
  · filter_upwards [hev] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hω] with n hn
    by_cases hωm : ω ∈ m
    · rw [indicator_of_mem hωm, indicator_of_mem (hn.2 hωm)]
    · rw [indicator_of_notMem hωm, indicator_of_notMem (fun h' => hωm (hn.1 h'))]

/-- **The projection identity of the stopped coupling on a marked avoidance event at the stop**:
`{t₁ < S, truncH t₁ Y ∈ Γ, C ∩ K_S = ∅}` (`U ⊆ C` compact in `ℍ`). The limit `t₂ → ∞` of the pre-stop identity
`IsStoppedSeedCoupling.setIntegral_lapTest_pre`. -/
theorem IsStoppedSeedCoupling.setIntegral_lapTest_mark [IsProbabilityMeasure Q] (hr : 0 < r)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h) {T₀ : DistOn upperHalfPlaneOpens}
    (hT₀ : IsHarmonicDistOn T₀ H) (t₁ : ℚ≥0) {Γ : Set TwoSeedHist} (hΓ : MeasurableSet Γ)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) {U : Opens ℂ} (hUC : (U : Set ℂ) ⊆ C)
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω in stRecHist xL xR W VL VR S ⁻¹' (preMarkSet t₁ Γ ∩ {y | Disjoint C (tsHull y)}),
        Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂Q =
      Coupling.projFactor U f Ξ * ∫ ω in stRecHist xL xR W VL VR S ⁻¹' (preMarkSet t₁ Γ ∩ {y | Disjoint C (tsHull y)}),
        Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂Q := by
  have hRm := hc.measurable_stRecHist
  obtain ⟨-, -, -, -, -, -, -, hhm, -⟩ := id hc
  set t₂ : ℕ → ℚ≥0 := fun n => t₁ + n + 1 with ht₂
  have ht : ∀ n, t₁ < t₂ n := fun n => by
    simp only [ht₂]
    have : (0 : ℚ≥0) < (n : ℚ≥0) + 1 := by positivity
    calc t₁ = t₁ + 0 := (add_zero t₁).symm
      _ < t₁ + ((n : ℚ≥0) + 1) := by gcongr
      _ = t₁ + n + 1 := (add_assoc _ _ _).symm
  set E : ℕ → Set Ω := fun n => stRecHist xL xR W VL VR S ⁻¹' preHistSet t₁ (t₂ n) Γ C with hEdef
  set m : Set Ω := stRecHist xL xR W VL VR S ⁻¹' (preMarkSet t₁ Γ ∩ {y | Disjoint C (tsHull y)}) with hmdef
  have hEm : ∀ n, MeasurableSet (E n) := fun n => hRm (measurableSet_preHistSet t₁ (t₂ n) hΓ hC)
  have hmm : MeasurableSet m :=
    hRm ((preMarkSigma_le _ (measurableSet_preMarkSet t₁ hΓ)).inter (measurableSet_disjoint_tsHull hC))
  have hev : ∀ᵐ ω ∂Q, ∀ᶠ n in atTop, (ω ∈ E n ↔ ω ∈ m) := by
    filter_upwards [hc.ae_isRegularStop hr] with ω hreg
    obtain ⟨S₀, hS₀⟩ := WithTop.ne_top_iff_exists.1 hreg.2.1
    obtain ⟨N, hN⟩ := exists_nat_ge (S₀ : ℝ)
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hle : S₀ ≤ ((t₂ n : ℚ≥0) : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]
      have h1 : ((t₂ n : ℚ≥0) : ℝ) = (t₁ : ℝ) + n + 1 := by simp [ht₂]
      rw [show (((t₂ n : ℚ≥0) : ℝ≥0) : ℝ) = ((t₂ n : ℚ≥0) : ℝ) from rfl, h1]
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      have h0 : (0 : ℝ) ≤ (t₁ : ℝ) := by positivity
      linarith
    have htr : truncH (t₂ n) (stRecHist xL xR W VL VR S ω) = stRecHist xL xR W VL VR S ω := by
      rw [stRecHist_eq_tsOf hreg hS₀.symm, truncH_tsOf, min_eq_left hle]
    simp only [hEdef, hmdef, mem_preimage, preHistSet, preMarkSet, mem_inter_iff, mem_ofPred_eq, htr]
    tauto
  have hbd : ∀ (χ : TestOn upperHalfPlaneOpens) ω, ‖Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ))‖ ≤ 1 :=
    fun χ ω => (Complex.norm_exp_I_mul_ofReal _).le
  have hmeas : ∀ χ : TestOn upperHalfPlaneOpens,
      AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ))) Q := fun χ =>
    (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp
      ((WholeField.measurable_sub_dist T₀).comp hhm))).aestronglyMeasurable
  have h1 := tendsto_setIntegral_of_ae_eventually hEm hmm hev (hmeas _) (hbd (lapTest U f + Ξ))
  have h2 := (tendsto_setIntegral_of_ae_eventually hEm hmm hev (hmeas _) (hbd Ξ)).const_mul
    (Coupling.projFactor U f Ξ)
  have hpre : ∀ n, ∫ ω in E n, Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂Q =
      Coupling.projFactor U f Ξ * ∫ ω in E n, Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂Q := fun n =>
    hc.setIntegral_lapTest_pre hr hT₀ (ht n) hΓ hC hCH hUC f Ξ
  simp_rw [hpre] at h1
  exact tendsto_nhds_unique h1 h2

/-! ### The marked σ-algebra at the stop and the independence -/

/-- The marked avoidance events at the stop: a pre-stop mark of the history at `S` together with the avoidance of a
compact `C ⊇ U` of `ℍ` by the hull read from the history. -/
def markGensQ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0) (U : Set ℂ) : Set (Set Ω) :=
  {m | ∃ (t : ℚ≥0) (Γ : Set TwoSeedHist) (C : Set ℂ), MeasurableSet Γ ∧ IsCompact C ∧ C ⊆ H ∧ U ⊆ C ∧
    m = stRecHist xL xR W VL VR S ⁻¹' (preMarkSet t Γ ∩ {y | Disjoint C (tsHull y)})}

/-- **The σ-algebra of the marked avoidance events at the stop.** -/
@[instance_reducible]
def markSigmaQ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0) (U : Set ℂ) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom (markGensQ xL xR W VL VR S U)

theorem isPiSystem_markGensQ (U : Set ℂ) : IsPiSystem (markGensQ xL xR W VL VR S U) := by
  rintro _ ⟨t, Γ, C, hΓ, hC, hCH, hUC, rfl⟩ _ ⟨t', Γ', C', hΓ', hC', hC'H, hUC', rfl⟩ -
  rcases le_total t t' with hle | hle
  · refine ⟨t', truncH t ⁻¹' Γ ∩ Γ', C ∪ C', ((measurable_truncH t) hΓ).inter hΓ', hC.union hC',
      union_subset hCH hC'H, hUC.trans subset_union_left, ?_⟩
    rw [← preimage_inter, ← preMarkSet_inter_of_le hle]
    congr 1
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, disjoint_union_left]
    tauto
  · refine ⟨t, truncH t' ⁻¹' Γ' ∩ Γ, C ∪ C', ((measurable_truncH t') hΓ').inter hΓ, hC.union hC',
      union_subset hCH hC'H, hUC.trans subset_union_left, ?_⟩
    rw [← preimage_inter, ← preMarkSet_inter_of_le hle]
    congr 1
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, disjoint_union_left]
    tauto

theorem markSigmaQ_le (hRm : Measurable (stRecHist xL xR W VL VR S)) (U : Set ℂ) :
    markSigmaQ xL xR W VL VR S U ≤ mΩ := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨t, Γ, C, hΓ, hC, -, -, rfl⟩
  exact hRm ((preMarkSigma_le _ (measurableSet_preMarkSet t hΓ)).inter (measurableSet_disjoint_tsHull hC))

/-- **The projection identity on every marked event at the stop** (Dynkin's π-λ theorem). -/
theorem IsStoppedSeedCoupling.setIntegral_lapTest_markSigma [IsProbabilityMeasure Q] (hr : 0 < r)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h) {T₀ : DistOn upperHalfPlaneOpens}
    (hT₀ : IsHarmonicDistOn T₀ H) {U : Opens ℂ} (hUH : (U : Set ℂ) ⊆ H)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens (fun ω => h ω - T₀) (fun ω => G (h ω - T₀)) Q)
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) (D : Set Ω)
    (hD : MeasurableSet[markSigmaQ xL xR W VL VR S U] D) :
    ∫ ω in D, Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂Q =
      Coupling.projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂Q := by
  have hRm := hc.measurable_stRecHist
  obtain ⟨-, -, -, -, -, -, -, hhm, -⟩ := id hc
  have hXm : Measurable fun ω => h ω - T₀ := (WholeField.measurable_sub_dist T₀).comp hhm
  have hle := markSigmaQ_le (xL := xL) (xR := xR) (W := W) (VL := VL) (VR := VR) (S := S) hRm (U : Set ℂ)
  have hint : ∀ χ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ))) Q := fun χ =>
    GFF.integrable_exp_I_mul ((measurable_distOn_apply χ).comp hXm)
  have hall := integral_lapTest_eq_of_isMarkovDecomposition hXm hUH hG hd f Ξ
  refine MeasurableSpace.induction_on_inter (m := markSigmaQ xL xR W VL VR S U)
    (C := fun D _ => ∫ ω in D, Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂Q =
      Coupling.projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂Q)
    rfl (isPiSystem_markGensQ (U : Set ℂ)) (by simp) ?_ ?_ ?_ D hD
  · rintro _ ⟨t, Γ, C, hΓ, hC, hCH, hUC, rfl⟩
    exact hc.setIntegral_lapTest_mark hr hT₀ t hΓ hC hCH hUC f Ξ
  · intro D' hD' hid
    rw [setIntegral_compl (hle _ hD') (hint _), setIntegral_compl (hle _ hD') (hint _), hid, hall, mul_sub]
  · intro Ds hdisj hDs hids
    rw [integral_iUnion (fun i => hle _ (hDs i)) hdisj (hint _).integrableOn,
      integral_iUnion (fun i => hle _ (hDs i)) hdisj (hint _).integrableOn, ← tsum_mul_left]
    exact tsum_congr hids

/-- **History-marked locality at the stop**: the projection of the centred field onto `H(U)` is independent of the
complementary projection together with the marked avoidance events at the stop. -/
theorem IsStoppedSeedCoupling.indep_markSigmaQ [IsProbabilityMeasure Q] (hr : 0 < r)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h) {T₀ : DistOn upperHalfPlaneOpens}
    (hT₀ : IsHarmonicDistOn T₀ H) {U : Opens ℂ} (hUH : (U : Set ℂ) ⊆ H)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens (fun ω => h ω - T₀) (fun ω => G (h ω - T₀)) Q) :
    Indep (MeasurableSpace.comap (fun ω => G (h ω - T₀)) inferInstance)
      (MeasurableSpace.comap (fun ω => markovCompl G (h ω - T₀)) inferInstance ⊔
        markSigmaQ xL xR W VL VR S U) Q := by
  obtain ⟨-, -, -, -, -, -, -, hhm, -⟩ := id hc
  exact indep_markov_of_setIntegral_lapTest (X := fun ω => h ω - T₀)
    ((WholeField.measurable_sub_dist T₀).comp hhm) hUH hG hd (markSigmaQ_le hc.measurable_stRecHist _)
    fun f Ξ D hD => hc.setIntegral_lapTest_markSigma hr hT₀ hUH hG hd f Ξ D hD

end Code

end LocalExt

end InteractingSLE
