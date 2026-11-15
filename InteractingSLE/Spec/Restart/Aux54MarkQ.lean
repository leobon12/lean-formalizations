/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54Marks

/-!
# Aux. lemma 54 for general words, part 9: history-marked locality of a coupling through a stop

Packet PROVE-AUX54. For a coupling through a stop `V` (regular at the stop, admissible seed) and the centred field
`X = h − T₀`, the projection identity at `U` holds on the **marked avoidance events at the stop**:

* `{history ∈ preMark t Γ} ∩ avoidLim C` (`U ⊆ C` compact in `ℍ`), where `avoidLim C` is the avoidance of `C` by the
  closed hulls `cl(K_{k ∧ V}) ∩ ℍ`, `k ∈ ℕ` — the limit `t₂ → ∞` of the coded identities
  (`setIntegral_lapTest_coded`);
* `{V = 0}` (the hull of a coupling stopped at `0` is empty: locality of `K_{1 ∧ V}` with the hull clock `0`);
* null events.

They form a π-system (`markGensQ`); Dynkin's theorem and the Markov decomposition of the GFF give the identity on the
generated σ-algebra `markSigmaQ`, hence the independence of the projection onto `H(U)` from the complementary projection
together with `markSigmaQ` (**`indep_markSigmaQ`**). Every event `Γq ∩ {history ∈ M}` (`Γq` the avoidance of `C` by
the recorded hull) lies in `markSigmaQ` (**`measurableSet_markSigmaQ_recHull`**), through the σ-algebra of the
pre-stop marks (`Aux54Marks`). PROVE-LOCEXT-N's `LocalExtNCode` for general words.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace Aux54

open LQGMetric LawUnique Sec4 StoppedExtendWF Coupling DomainMarkov LQGMetric.MarkovZB LocalSets

variable {nL nR : ℕ}

/-! ### Dynkin's theorem for the projection identity -/

section Dynkin

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {X : Ω → DistOn upperHalfPlaneOpens}

/-- **The projection identity on a generated σ-algebra** (Dynkin's π-λ theorem): from the identity on a π-system of
measurable events and on the whole space. -/
theorem setIntegral_lapTest_of_generateFrom (hXm : Measurable X) {U : TopologicalSpace.Opens ℂ}
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) {𝒢 : Set (Set Ω)} (h𝒢π : IsPiSystem 𝒢)
    (h𝒢m : ∀ D ∈ 𝒢, MeasurableSet D)
    (hall : ∫ ω, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
      Coupling.projFactor U f Ξ * ∫ ω, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P)
    (hgen : ∀ D ∈ 𝒢, ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
      Coupling.projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P)
    {D : Set Ω} (hD : MeasurableSet[MeasurableSpace.generateFrom 𝒢] D) :
    ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
      Coupling.projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P := by
  have hle : MeasurableSpace.generateFrom 𝒢 ≤ mΩ := MeasurableSpace.generateFrom_le h𝒢m
  have hint : ∀ χ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Complex.exp (Complex.I * (X ω χ : ℂ))) P := fun χ =>
    GFF.integrable_exp_I_mul ((measurable_distOn_apply χ).comp hXm)
  refine MeasurableSpace.induction_on_inter (m := MeasurableSpace.generateFrom 𝒢)
    (C := fun D _ => ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
      Coupling.projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P)
    rfl h𝒢π (by simp) (fun D hD => hgen D hD) ?_ ?_ D hD
  · intro D' hD' hid
    rw [setIntegral_compl (hle _ hD') (hint _), setIntegral_compl (hle _ hD') (hint _), hid, hall, mul_sub]
  · intro Ds hdisj hDs hids
    rw [integral_iUnion (fun i => hle _ (hDs i)) hdisj (hint _).integrableOn,
      integral_iUnion (fun i => hle _ (hDs i)) hdisj (hint _).integrableOn, ← tsum_mul_left]
    exact tsum_congr hids

end Dynkin

/-! ### The closed hulls and their avoidance in the limit -/

section Avoid

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- The closed hull in `ℍ` at `r ∧ V`. -/
def clHull (W : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (r : ℝ≥0) (ω : Ω) : Set ℂ :=
  closure (fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (r : ℝ≥0∞) (V ω)).toNNReal : ℝ)) ∩
    (upperHalfPlaneOpens : Set ℂ)

/-- The avoidance of `C` by every closed hull `cl(K_{k ∧ V}) ∩ ℍ`, `k ∈ ℕ`. -/
def avoidLim (W : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (C : Set ℂ) : Set Ω :=
  {ω | ∀ k : ℕ, Disjoint C (clHull W V (k : ℝ≥0) ω)}

theorem clHull_mono {r r' : ℝ≥0} (h : r ≤ r') (ω : Ω) : clHull W V r ω ⊆ clHull W V r' ω := by
  have hle : (min (r : ℝ≥0∞) (V ω)).toNNReal ≤ (min (r' : ℝ≥0∞) (V ω)).toNNReal :=
    ENNReal.toNNReal_mono (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
      (min_le_min (ENNReal.coe_le_coe.2 h) le_rfl)
  exact inter_subset_inter_left _ (closure_mono (QuantumZipper.fwdHull_mono.1 (by exact_mod_cast hle)))

theorem avoidLim_union (C C' : Set ℂ) : avoidLim W V C ∩ avoidLim W V C' = avoidLim W V (C ∪ C') := by
  ext ω
  simp only [avoidLim, mem_inter_iff, mem_ofPred_eq, disjoint_union_left]
  exact ⟨fun h k => ⟨h.1 k, h.2 k⟩, fun h => ⟨fun k => (h k).1, fun k => (h k).2⟩⟩

/-- **Avoidance at the times `t + n + 1` is eventually the limit avoidance.** -/
theorem eventually_disjoint_clHull_iff (ω : Ω) (C : Set ℂ) (t : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop, (Disjoint C (clHull W V (t + n + 1) ω) ↔ ω ∈ avoidLim W V C) := by
  by_cases hω : ω ∈ avoidLim W V C
  · obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
    refine Eventually.of_forall fun n => ⟨fun _ => hω, fun _ => (hω (N + n + 1)).mono_right ?_⟩
    refine clHull_mono ?_ ω
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith
  · simp only [avoidLim, mem_ofPred_eq, not_forall] at hω
    obtain ⟨k, hk⟩ := hω
    refine eventually_atTop.2 ⟨k, fun n hn => ⟨fun hd => absurd (hd.mono_right (clHull_mono ?_ ω)) hk,
      fun h' => absurd (h' k) hk⟩⟩
    rw [← NNReal.coe_le_coe]
    have : (k : ℝ) ≤ n := by exact_mod_cast hn
    have h0 : (0 : ℝ) ≤ t := t.coe_nonneg
    push_cast
    linarith

end Avoid

/-! ### Hull clocks of hulls avoiding an open set -/

/-- **A hull avoiding a nonempty subset of `ℍ` has its own time as hull clock** (the driver is continuous beyond the
time, `exists_continuousOn_beyond`). -/
theorem hullClock_fwdHull_of_disjoint {w : ℝ≥0 → ℝ} (hw0 : w 0 = 0) (T : ℝ≥0) {V' : Set ℂ} (hV'H : V' ⊆ H)
    (hV'ne : V'.Nonempty) (hd : Disjoint (fwdHull (fun s : ℝ => w s.toNNReal) (T : ℝ)) V') :
    WholeField.hullClock (fwdHull (fun s : ℝ => w s.toNNReal) (T : ℝ)) = T ∧
      ∃ T' : ℝ≥0, T < T' ∧ ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) < (T' : ℝ≥0∞)} := by
  obtain ⟨z, hz⟩ := hV'ne
  have hzK : z ∉ fwdHull (fun s : ℝ => w s.toNNReal) (T : ℝ) := fun hzK => Set.disjoint_left.1 hd hzK hz
  obtain ⟨T', hTT', hcT'⟩ := exists_continuousOn_beyond T.coe_nonneg (hV'H hz) hzK
  have hT'0 : (0 : ℝ) ≤ T' := T.coe_nonneg.trans hTT'.le
  have hwc : ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) < ((T'.toNNReal : ℝ≥0) : ℝ≥0∞)} := by
    intro t ht
    have ht' : (t : ℝ) ∈ Icc (0 : ℝ) T' := ⟨t.coe_nonneg,
      (Real.le_toNNReal_iff_coe_le hT'0).1 (ENNReal.coe_le_coe.1 (le_of_lt ht))⟩
    have h1 := (hcT' (t : ℝ) ht').comp (continuous_subtype_val.continuousWithinAt (x := t))
      (fun s hs => ⟨s.coe_nonneg, (Real.le_toNNReal_iff_coe_le hT'0).1 (ENNReal.coe_le_coe.1 (le_of_lt hs))⟩)
    refine h1.congr (fun s _ => ?_) ?_
    · simp only [Function.comp_apply, Real.toNNReal_coe]
    · simp only [Function.comp_apply, Real.toNNReal_coe]
  have hTT'' : (T : ℝ≥0∞) < ((T'.toNNReal : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_lt_coe.2 ((Real.lt_toNNReal_iff_coe_lt).2 hTT')
  exact ⟨WholeField.hullClock_fwdHull_rpath hwc hw0 hTT'', T'.toNNReal, ENNReal.coe_lt_coe.1 hTT'', hwc⟩

/-! ### The identity on the marked generators -/

section Gens

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- A pre-stop mark of the killed history is an event of the driving filtration at the truncation time. -/
theorem measurableSet_preMark_driving (hX : IsMeasurableKilledDriving W VL VR V) (t : ℝ≥0)
    {Γ : Set (HistorySpace nL nR)} (hΓ : MeasurableSet Γ) :
    MeasurableSet[drivingFiltration P hX t] {ω | killedHistory W VL VR V ω ∈ preMark t Γ} := by
  have hV := isStoppingTime_lifetime_driving (P := P) hX
  have e : {ω | killedHistory W VL VR V ω ∈ preMark t Γ} = {ω | ((t : ℝ≥0) : WithTop ℝ≥0) < (V ω : WithTop ℝ≥0)} ∩
      (killedHistory W VL VR (fun ω => min (t : ℝ≥0∞) (V ω))) ⁻¹' Γ := by
    ext ω
    simp only [preMark, mem_ofPred_eq, truncK_killedHistory, mem_inter_iff, mem_preimage]
    rfl
  rw [e]
  exact (LocalExt.measurableSet_lt_stop hV t).inter
    (Ito.le_usualAugmentation (killedDrivingFiltration hX) P t _ ((measurable_killedHistory_min hX t) hΓ))

/-- **The coded events converge to the marked avoidance event.** -/
theorem ae_eventually_coded {M : ℕ → Set Ω} {F₀ : Set Ω} {C : Set ℂ} {t : ℝ≥0}
    (hM : ∀ n, M n =ᵐ[P] F₀ ∩ {ω | Disjoint C (clHull W V (t + n + 1) ω)}) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (ω ∈ M n ↔ ω ∈ F₀ ∩ avoidLim W V C) := by
  filter_upwards [ae_all_iff.2 hM] with ω hω
  filter_upwards [eventually_disjoint_clHull_iff (W := W) (V := V) ω C t] with n hn
  rw [Iff.of_eq (hω n)]
  exact and_congr_right fun _ => hn

/-- The coded events at `t < t + n + 1` (`setIntegral_lapTest_coded`) for a pre-stop mark. -/
theorem exists_coded_markPre [IsProbabilityMeasure P]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H) (t : ℝ≥0)
    {Γ : Set (HistorySpace nL nR)} (hΓ : MeasurableSet Γ)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) (hCne : C.Nonempty) {U : TopologicalSpace.Opens ℂ}
    (hUC : (U : Set ℂ) ⊆ C) (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) (n : ℕ) :
    ∃ M : Set Ω, MeasurableSet M ∧
      M =ᵐ[P] {ω | killedHistory W VL VR V ω ∈ preMark t Γ} ∩
        {ω | Disjoint C (clHull W V (t + n + 1) ω)} ∧
      ∫ ω in M, Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂P =
        Coupling.projFactor U f Ξ * ∫ ω in M, Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂P := by
  have ht : t < t + n + 1 := by
    rw [add_assoc]
    exact lt_add_of_pos_right t (by positivity)
  exact setIntegral_lapTest_coded hSC hT₀ ht (F₀ := {ω | killedHistory W VL VR V ω ∈ preMark t Γ})
    (fun hX => measurableSet_preMark_driving hX t hΓ) (fun ω hω => hω.1) hC hCH hCne hUC f Ξ

/-- **A measurable version of a marked avoidance event.** -/
theorem exists_version_markPre [IsProbabilityMeasure P]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h) (t : ℝ≥0)
    {Γ : Set (HistorySpace nL nR)} (hΓ : MeasurableSet Γ)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) (hCne : C.Nonempty) :
    ∃ m : Set Ω, MeasurableSet m ∧
      m =ᵐ[P] {ω | killedHistory W VL VR V ω ∈ preMark t Γ} ∩ avoidLim W V C := by
  choose M hMm hMeq _ using fun n => exists_coded_markPre hSC (T₀ := 0)
    ⟨0, InnerProductSpace.harmonicOnNhd_const (0 : ℝ), fun φ _ => by simp⟩ t hΓ hC hCH hCne
    (U := ⊥) (by simp) 0 0 n
  have hev := ae_eventually_coded (P := P) hMeq
  refine ⟨⋃ N : ℕ, ⋂ n ≥ N, M n,
    MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => hMm n, ?_⟩
  filter_upwards [hev] with ω hω
  exact propext (mem_liminf_iff_of_eventually hω)

/-- **The projection identity on a marked avoidance event at the stop** (the limit `n → ∞` of the coded identities at
`t < t + n + 1`). -/
theorem setIntegral_lapTest_markPre [IsProbabilityMeasure P]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H) (t : ℝ≥0)
    {Γ : Set (HistorySpace nL nR)} (hΓ : MeasurableSet Γ)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) (hCne : C.Nonempty) {U : TopologicalSpace.Opens ℂ}
    (hUC : (U : Set ℂ) ⊆ C) {m : Set Ω} (hm : MeasurableSet m)
    (hmeq : m =ᵐ[P] {ω | killedHistory W VL VR V ω ∈ preMark t Γ} ∩ avoidLim W V C)
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω in m, Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂P =
      Coupling.projFactor U f Ξ * ∫ ω in m, Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂P := by
  have hhm : Measurable h := hSC.2.2.1
  choose M hMm hMeq hMid using fun n => exists_coded_markPre hSC hT₀ t hΓ hC hCH hCne hUC f Ξ n
  have hev := ae_eventually_coded (P := P) hMeq
  have hev' : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (ω ∈ M n ↔ ω ∈ m) := by
    filter_upwards [hev, hmeq] with ω hω hmω
    filter_upwards [hω] with n hn
    exact hn.trans (Iff.of_eq hmω).symm
  have hbd : ∀ (χ : TestOn upperHalfPlaneOpens) ω, ‖Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ))‖ ≤ 1 :=
    fun χ ω => (Complex.norm_exp_I_mul_ofReal _).le
  have hmeas : ∀ χ : TestOn upperHalfPlaneOpens,
      AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ))) P := fun χ =>
    (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp
      ((WholeField.measurable_sub_dist T₀).comp hhm))).aestronglyMeasurable
  have h1 := LocalExt.tendsto_setIntegral_of_ae_eventually hMm hm hev' (hmeas _) (hbd (lapTest U f + Ξ))
  have h2 := (LocalExt.tendsto_setIntegral_of_ae_eventually hMm hm hev' (hmeas _) (hbd Ξ)).const_mul
    (Coupling.projFactor U f Ξ)
  simp_rw [hMid] at h1
  exact tendsto_nhds_unique h1 h2

/-- **At a regular stop `V = 0` of an admissible seed the hull at `0` is empty and has clock `0`.** -/
theorem ae_fwdHull_zero_of_eq_zero
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hreg : IsRegularStop ρL ρR P W VL VR V) :
    ∀ᵐ ω ∂P, V ω = 0 → fwdHull (fun s : ℝ => W s.toNNReal ω) ((0 : ℝ≥0) : ℝ) = ∅ ∧
      WholeField.hullClock (fwdHull (fun s : ℝ => W s.toNNReal ω) ((0 : ℝ≥0) : ℝ)) = 0 := by
  filter_upwards [hSC.1.ae_path, hreg] with ω hp hrω h0
  have hnt : ¬ ForceWord.ThresholdCondition ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun j => VR j 0 ω) := by
    rw [hp.w_zero, show (fun i => VL i 0 ω) = xL from funext hp.vL_zero,
      show (fun j => VR j 0 ω) = xR from funext hp.vR_zero]
    exact hseed
  obtain ⟨T', hT', hcT'⟩ := hrω 0 (by rw [h0]; rfl) hnt
  have hwc : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < (T' : ℝ≥0∞)} :=
    hcT'.mono fun t ht => le_of_lt (ENNReal.coe_lt_coe.1 ht)
  have hT'0 : (0 : ℝ≥0∞) < (T' : ℝ≥0∞) := ENNReal.coe_pos.2 hT'
  exact ⟨Coupling.MartMeans2.fwdHull_rpath_zero hwc hT'0,
    WholeField.hullClock_fwdHull_rpath hwc hp.w_zero (t := 0) (by exact_mod_cast hT'0)⟩

/-- **The projection identity on the event `{V = 0}`** (locality of `K_{1 ∧ V}` weighted by `{hull clock = 0}`). -/
theorem setIntegral_lapTest_markZero [IsProbabilityMeasure P]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hreg : IsRegularStop ρL ρR P W VL VR V)
    {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) (hUne : (U : Set ℂ).Nonempty)
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω in {ω | V ω = 0}, Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂P =
      Coupling.projFactor U f Ξ * ∫ ω in {ω | V ω = 0}, Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂P := by
  classical
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  have hz := ae_fwdHull_zero_of_eq_zero hSC hseed hreg
  obtain ⟨hEv, -, -, -, hX, hcl⟩ := id hSC
  set 𝒢 := drivingFiltration P hX with h𝒢
  have hV := isStoppingTime_lifetime_driving (P := P) hX
  have hτ : IsStoppingTime 𝒢 fun ω => min ((1 : ℝ≥0) : WithTop ℝ≥0) (V ω : WithTop ℝ≥0) :=
    (isStoppingTime_const 𝒢 _).min hV
  have hloc := WholeField.IsLocalSet.sub_dist (hcl _ hτ (ae_of_all _ fun ω =>
    ⟨min_le_right _ _, ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)⟩)).1 hT₀
  set A : Ω → Set ℂ := fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω)
    (((min ((1 : ℝ≥0) : WithTop ℝ≥0) (V ω : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : ℝ) with hAdef
  set k : Set ℂ → ℂ := {S : Set ℂ | WholeField.hullClock S ≤ 0}.indicator fun _ => (1 : ℂ) with hkdef
  have hk : Measurable[hittingSigma] k :=
    measurable_const.indicator (measurableSet_le WholeField.measurable_hullClock measurable_const)
  have hkb : ∀ S, ‖k S‖ ≤ 1 := fun S => by
    simp only [hkdef]
    by_cases hS : S ∈ {S : Set ℂ | WholeField.hullClock S ≤ 0}
    · rw [indicator_of_mem hS, norm_one]
    · rw [indicator_of_notMem hS, norm_zero]; exact zero_le_one
  have key := LocalExt.integral_indicator_lapTest_eq (V := U) hloc hUH le_rfl hk hkb f Ξ
  have hVm : MeasurableSet {ω | V ω = 0} := measurable_lifetime hX (measurableSet_singleton 0)
  have hpt : ∀ᵐ ω ∂P, {ω | Disjoint (A ω) (U : Set ℂ)}.indicator (fun ω => k (A ω)) ω =
      {ω | V ω = 0}.indicator (fun _ => (1 : ℂ)) ω := by
    filter_upwards [hEv.ae_path, hz] with ω hp hzω
    by_cases h0 : V ω = 0
    · have e0 : min ((1 : ℝ≥0) : WithTop ℝ≥0) (V ω : WithTop ℝ≥0) = ((0 : ℝ≥0) : WithTop ℝ≥0) := by
        rw [show (V ω : WithTop ℝ≥0) = ((0 : ℝ≥0) : WithTop ℝ≥0) from h0]
        exact min_eq_right (WithTop.coe_le_coe.2 (zero_le : (0 : ℝ≥0) ≤ 1))
      have hA : A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((0 : ℝ≥0) : ℝ) := by
        simp only [hAdef, e0, WithTop.untopD_coe]
      obtain ⟨hA0, hcl0⟩ := hzω h0
      have hd : ω ∈ {ω | Disjoint (A ω) (U : Set ℂ)} := by
        show Disjoint (A ω) (U : Set ℂ)
        rw [hA, hA0]; exact Set.empty_disjoint _
      rw [indicator_of_mem hd, indicator_of_mem (show ω ∈ {ω | V ω = 0} from h0), hkdef,
        indicator_of_mem (show A ω ∈ {S : Set ℂ | WholeField.hullClock S ≤ 0} by
          show WholeField.hullClock (A ω) ≤ 0
          rw [hA, hcl0])]
    · rw [indicator_of_notMem (show ω ∉ {ω | V ω = 0} from h0)]
      by_cases hd : Disjoint (A ω) (U : Set ℂ)
      · obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.1
          (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left ((1 : ℝ≥0) : WithTop ℝ≥0) (V ω : WithTop ℝ≥0)))
        have hA : A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (T : ℝ) := by
          simp only [hAdef, ← hT, WithTop.untopD_coe]
        have hTpos : 0 < T := by
          have h1 : (0 : ℝ≥0∞) < min (1 : ℝ≥0∞) (V ω) := lt_min one_pos (pos_iff_ne_zero.2 h0)
          have h2 : ((T : ℝ≥0) : ℝ≥0∞) = min (1 : ℝ≥0∞) (V ω) := hT
          rw [← h2] at h1
          exact ENNReal.coe_pos.1 h1
        rw [hA] at hd
        obtain ⟨hclk, -⟩ := hullClock_fwdHull_of_disjoint (w := fun t => W t ω) hp.w_zero T hUH hUne hd
        have hmem : ω ∈ {ω | Disjoint (A ω) (U : Set ℂ)} := by
          show Disjoint (A ω) (U : Set ℂ)
          rw [hA]; exact hd
        rw [indicator_of_mem hmem,
          hkdef, indicator_of_notMem (show A ω ∉ {S : Set ℂ | WholeField.hullClock S ≤ 0} by
            show ¬ WholeField.hullClock (A ω) ≤ 0
            rw [hA, hclk]
            exact not_le.2 (ENNReal.coe_pos.2 hTpos))]
      · rw [indicator_of_notMem (show ω ∉ {ω | Disjoint (A ω) (U : Set ℂ)} from hd)]
  have hind : ∀ χ : TestOn upperHalfPlaneOpens,
      ∫ ω, {ω | Disjoint (A ω) (U : Set ℂ)}.indicator (fun ω => k (A ω)) ω *
        Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)) ∂P =
      ∫ ω in {ω | V ω = 0}, Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)) ∂P := by
    intro χ
    rw [← integral_indicator hVm]
    refine integral_congr_ae ?_
    filter_upwards [hpt] with ω hω
    rw [hω]
    by_cases h0 : V ω = 0
    · simp only [indicator_of_mem (show ω ∈ {ω | V ω = 0} from h0), one_mul]
    · simp only [indicator_of_notMem (show ω ∉ {ω | V ω = 0} from h0), zero_mul]
  rw [← hind, ← hind]
  exact key

end Gens

/-! ### The marked σ-algebra at the stop -/

section Sigma

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- The marked generators at the stop: null events, measurable versions of the marked avoidance events
`{history ∈ preMark t Γ} ∩ avoidLim C` (`U ⊆ C` compact in `ℍ`), and measurable versions of `{V = 0}`. -/
def markGensQ (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (V : Ω → ℝ≥0∞) (U : Set ℂ) : Set (Set Ω) :=
  {m | MeasurableSet m ∧ (P m = 0 ∨ ∃ C : Set ℂ, IsCompact C ∧ C ⊆ H ∧ U ⊆ C ∧
    ((∃ (t : ℝ≥0) (Γ : Set (HistorySpace nL nR)), MeasurableSet Γ ∧
      m =ᵐ[P] {ω | killedHistory W VL VR V ω ∈ preMark t Γ} ∩ avoidLim W V C) ∨
      m =ᵐ[P] {ω | V ω = 0}))}

/-- **The marked σ-algebra at the stop.** -/
@[instance_reducible]
def markSigmaQ (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (V : Ω → ℝ≥0∞) (U : Set ℂ) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom (markGensQ P W VL VR V U)

theorem markSigmaQ_le (U : Set ℂ) : markSigmaQ P W VL VR V U ≤ mΩ :=
  MeasurableSpace.generateFrom_le fun _ hm => hm.1

theorem isPiSystem_markGensQ (U : Set ℂ) : IsPiSystem (markGensQ P W VL VR V U) := by
  rintro m₁ ⟨hm₁, h₁⟩ m₂ ⟨hm₂, h₂⟩ -
  refine ⟨hm₁.inter hm₂, ?_⟩
  rcases h₁ with h₁0 | ⟨C₁, hC₁, hC₁H, hUC₁, h₁'⟩
  · exact Or.inl (measure_mono_null inter_subset_left h₁0)
  rcases h₂ with h₂0 | ⟨C₂, hC₂, hC₂H, hUC₂, h₂'⟩
  · exact Or.inl (measure_mono_null inter_subset_right h₂0)
  have hpre0 : ∀ (t : ℝ≥0) (Γ : Set (HistorySpace nL nR)) (C : Set ℂ),
      {ω | killedHistory W VL VR V ω ∈ preMark t Γ} ∩ avoidLim W V C ∩ {ω | V ω = 0} = ∅ := by
    intro t Γ C
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hω h0
    have : (t : ℝ≥0∞) < V ω := hω.1.1
    rw [h0] at this
    exact absurd this (not_lt.2 zero_le)
  rcases h₁' with ⟨t, Γ, hΓ, e₁⟩ | e₁ <;> rcases h₂' with ⟨t', Γ', hΓ', e₂⟩ | e₂
  · refine Or.inr ⟨C₁ ∪ C₂, hC₁.union hC₂, union_subset hC₁H hC₂H, hUC₁.trans subset_union_left, Or.inl ?_⟩
    have hgen : ∀ (t t' : ℝ≥0) (Γ Γ' : Set (HistorySpace nL nR)), t ≤ t' →
        ({ω | killedHistory W VL VR V ω ∈ preMark t Γ} ∩ avoidLim W V C₁) ∩
          ({ω | killedHistory W VL VR V ω ∈ preMark t' Γ'} ∩ avoidLim W V C₂) =
        {ω | killedHistory W VL VR V ω ∈ preMark t' (truncK t ⁻¹' Γ ∩ Γ')} ∩ avoidLim W V (C₁ ∪ C₂) := by
      intro t t' Γ Γ' ht
      rw [← preMark_inter_of_le ht, ← avoidLim_union]
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      tauto
    rcases le_total t t' with ht | ht
    · exact ⟨t', _, ((measurable_truncK t) hΓ).inter hΓ', (e₁.inter e₂).trans (by rw [hgen t t' Γ Γ' ht])⟩
    · refine ⟨t, _, ((measurable_truncK t') hΓ').inter hΓ, (e₁.inter e₂).trans ?_⟩
      have h' := hgen t' t Γ' Γ ht
      have e : ({ω | killedHistory W VL VR V ω ∈ preMark t Γ} ∩ avoidLim W V C₁) ∩
          ({ω | killedHistory W VL VR V ω ∈ preMark t' Γ'} ∩ avoidLim W V C₂) =
          {ω | killedHistory W VL VR V ω ∈ preMark t (truncK t' ⁻¹' Γ' ∩ Γ)} ∩ avoidLim W V (C₁ ∪ C₂) := by
        have h'' : ({ω | killedHistory W VL VR V ω ∈ preMark t' Γ'} ∩ avoidLim W V C₁) ∩
            ({ω | killedHistory W VL VR V ω ∈ preMark t Γ} ∩ avoidLim W V C₂) =
            {ω | killedHistory W VL VR V ω ∈ preMark t (truncK t' ⁻¹' Γ' ∩ Γ)} ∩ avoidLim W V (C₁ ∪ C₂) := h'
        rw [← h'']
        ext ω
        simp only [mem_inter_iff]
        tauto
      rw [e]
  · refine Or.inl ?_
    rw [measure_congr (e₁.inter e₂), hpre0, measure_empty]
  · refine Or.inl ?_
    rw [measure_congr (e₁.inter e₂), inter_comm, hpre0, measure_empty]
  · refine Or.inr ⟨C₁, hC₁, hC₁H, hUC₁, Or.inr ((e₁.inter e₂).trans (by rw [inter_self]))⟩

/-- Null events are marked events. -/
theorem measurableSet_markSigmaQ_of_null (U : Set ℂ) {m : Set Ω} (hm : MeasurableSet m) (h0 : P m = 0) :
    MeasurableSet[markSigmaQ P W VL VR V U] m :=
  MeasurableSpace.measurableSet_generateFrom ⟨hm, Or.inl h0⟩

/-- A measurable event almost surely equal to a marked event is a marked event. -/
theorem measurableSet_markSigmaQ_of_ae_eq (U : Set ℂ) {m m' : Set Ω} (hm : MeasurableSet m)
    (hm' : MeasurableSet[markSigmaQ P W VL VR V U] m') (he : m =ᵐ[P] m') :
    MeasurableSet[markSigmaQ P W VL VR V U] m := by
  have hm'm : MeasurableSet m' := markSigmaQ_le U _ hm'
  have e : m = (m' \ (m' \ m)) ∪ (m \ m') := by
    ext ω
    simp only [mem_union, Set.mem_sdiff]
    tauto
  rw [e]
  refine (hm'.diff (measurableSet_markSigmaQ_of_null U (hm'm.diff hm) ?_)).union
    (measurableSet_markSigmaQ_of_null U (hm.diff hm'm) ?_)
  · exact ae_le_set.1 he.symm.le
  · exact ae_le_set.1 he.le

end Sigma

/-! ### The identity on the marked σ-algebra and the independence -/

section Indep

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The projection identity on every marked generator.** -/
theorem setIntegral_lapTest_markGen [IsProbabilityMeasure P]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hreg : IsRegularStop ρL ρR P W VL VR V)
    {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) (hUne : (U : Set ℂ).Nonempty)
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) {m : Set Ω}
    (hm : m ∈ markGensQ P W VL VR V (U : Set ℂ)) :
    ∫ ω in m, Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂P =
      Coupling.projFactor U f Ξ * ∫ ω in m, Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂P := by
  obtain ⟨hmm, h0 | ⟨C, hC, hCH, hUC, ⟨t, Γ, hΓ, he⟩ | he⟩⟩ := hm
  · rw [Measure.restrict_eq_zero.2 h0, integral_zero_measure, integral_zero_measure, mul_zero]
  · exact setIntegral_lapTest_markPre hSC hT₀ t hΓ hC hCH (hUne.mono hUC) hUC hmm he f Ξ
  · rw [setIntegral_congr_set he, setIntegral_congr_set he]
    exact setIntegral_lapTest_markZero hSC hT₀ hseed hreg hUH hUne f Ξ

/-- **The projection identity on the marked σ-algebra** (Dynkin). -/
theorem setIntegral_lapTest_markSigma [IsProbabilityMeasure P]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hreg : IsRegularStop ρL ρR P W VL VR V)
    {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) (hUne : (U : Set ℂ).Nonempty)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens (fun ω => h ω - T₀) (fun ω => G (h ω - T₀)) P)
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) {D : Set Ω}
    (hD : MeasurableSet[markSigmaQ P W VL VR V (U : Set ℂ)] D) :
    ∫ ω in D, Complex.exp (Complex.I * ((h ω - T₀) (lapTest U f + Ξ) : ℂ)) ∂P =
      Coupling.projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * ((h ω - T₀) Ξ : ℂ)) ∂P := by
  have hXm : Measurable fun ω => h ω - T₀ := (WholeField.measurable_sub_dist T₀).comp hSC.2.2.1
  exact setIntegral_lapTest_of_generateFrom (X := fun ω => h ω - T₀) hXm f Ξ (isPiSystem_markGensQ _)
    (fun D hD => hD.1) (LocalExt.integral_lapTest_eq_of_isMarkovDecomposition hXm hUH hG hd f Ξ)
    (fun D hD => setIntegral_lapTest_markGen hSC hT₀ hseed hreg hUH hUne f Ξ hD) hD

/-- **History-marked locality at the stop**: the projection of the centred field onto `H(U)` is independent of the
complementary projection together with the marked σ-algebra at the stop. -/
theorem indep_markSigmaQ [IsProbabilityMeasure P]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hreg : IsRegularStop ρL ρR P W VL VR V)
    {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) (hUne : (U : Set ℂ).Nonempty)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens (fun ω => h ω - T₀) (fun ω => G (h ω - T₀)) P) :
    Indep (MeasurableSpace.comap (fun ω => G (h ω - T₀)) inferInstance)
      (MeasurableSpace.comap (fun ω => markovCompl G (h ω - T₀)) inferInstance ⊔
        markSigmaQ P W VL VR V (U : Set ℂ)) P := by
  have hXm : Measurable fun ω => h ω - T₀ := (WholeField.measurable_sub_dist T₀).comp hSC.2.2.1
  exact LocalExt.indep_markov_of_setIntegral_lapTest (X := fun ω => h ω - T₀) hXm hUH hG hd (markSigmaQ_le _)
    fun f Ξ D hD => setIntegral_lapTest_markSigma hSC hT₀ hseed hreg hUH hUne hG hd f Ξ hD

/-! ### Record events are marked events -/

/-- **Every event of the pre-stop marks, intersected with the limit avoidance of `C ⊇ U`, has a version in the marked
σ-algebra** (Dynkin over the pre-stop marks; the base event is `{V = 0} ∪ ({0 < V} ∩ avoidLim C)`). -/
theorem exists_markSigmaQ_version [IsProbabilityMeasure P]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hreg : IsRegularStop ρL ρR P W VL VR V)
    {U C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) (hCne : C.Nonempty) (hUC : U ⊆ C)
    {N : Set (HistorySpace nL nR)} (hN : MeasurableSet[preMarkSigma] N) :
    ∃ m : Set Ω, MeasurableSet[markSigmaQ P W VL VR V U] m ∧
      m =ᵐ[P] killedHistory W VL VR V ⁻¹' N ∩ avoidLim W V C := by
  classical
  obtain ⟨-, -, -, -, hX, -⟩ := id hSC
  have hz := ae_fwdHull_zero_of_eq_zero hSC hseed hreg
  -- the base event
  obtain ⟨m₀, hm₀m, he₀⟩ := exists_version_markPre hSC 0 MeasurableSet.univ hC hCH hCne
  have hVm : MeasurableSet {ω | V ω = 0} := measurable_lifetime hX (measurableSet_singleton 0)
  have hbase : ∃ m : Set Ω, MeasurableSet[markSigmaQ P W VL VR V U] m ∧ m =ᵐ[P] avoidLim W V C := by
    have g1 : {ω | V ω = 0} ∈ markGensQ P W VL VR V U :=
      ⟨hVm, Or.inr ⟨C, hC, hCH, hUC, Or.inr (EventuallyEq.refl _ _)⟩⟩
    have g2 : m₀ ∈ markGensQ P W VL VR V U :=
      ⟨hm₀m, Or.inr ⟨C, hC, hCH, hUC, Or.inl ⟨0, univ, MeasurableSet.univ, he₀⟩⟩⟩
    refine ⟨{ω | V ω = 0} ∪ m₀, (MeasurableSpace.measurableSet_generateFrom g1).union
      (MeasurableSpace.measurableSet_generateFrom g2), ?_⟩
    filter_upwards [he₀, hz] with ω hω hzω
    have hω' : ω ∈ m₀ ↔ killedHistory W VL VR V ω ∈ preMark 0 univ ∧ ω ∈ avoidLim W V C := Iff.of_eq hω
    apply propext
    simp only [mem_union, mem_ofPred_eq]
    rw [hω']
    by_cases h0 : V ω = 0
    · refine ⟨fun _ => fun k => ?_, fun _ => Or.inl h0⟩
      have e : (min ((k : ℝ≥0) : ℝ≥0∞) (V ω)).toNNReal = 0 := by rw [h0, min_eq_right zero_le]; rfl
      simp only [clHull, e, (hzω h0).1, closure_empty, empty_inter]
      exact disjoint_empty _
    · have hpos : (((0 : ℝ≥0)) : ℝ≥0∞) < V ω := by
        rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 h0
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact absurd h h0
        · exact h
      · intro h
        exact Or.inr ⟨⟨hpos, mem_univ _⟩, h⟩
  obtain ⟨mΛ, hmΛ, heΛ⟩ := hbase
  refine MeasurableSpace.induction_on_inter (m := preMarkSigma)
    (C := fun N _ => ∃ m : Set Ω, MeasurableSet[markSigmaQ P W VL VR V U] m ∧
      m =ᵐ[P] killedHistory W VL VR V ⁻¹' N ∩ avoidLim W V C) rfl isPiSystem_preMarkSets ?_ ?_ ?_ ?_ N hN
  · exact ⟨∅, @MeasurableSet.empty _ (markSigmaQ P W VL VR V U), by simp⟩
  · rintro _ ⟨t, Γ, hΓ, rfl⟩
    obtain ⟨m, hmm, he⟩ := exists_version_markPre hSC t hΓ hC hCH hCne
    have g : m ∈ markGensQ P W VL VR V U := ⟨hmm, Or.inr ⟨C, hC, hCH, hUC, Or.inl ⟨t, Γ, hΓ, he⟩⟩⟩
    exact ⟨m, MeasurableSpace.measurableSet_generateFrom g, he⟩
  · rintro N' - ⟨m, hm, he⟩
    refine ⟨mΛ \ m, hmΛ.diff hm, ?_⟩
    have e : killedHistory W VL VR V ⁻¹' N'ᶜ ∩ avoidLim W V C =
        avoidLim W V C \ (killedHistory W VL VR V ⁻¹' N' ∩ avoidLim W V C) := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, Set.mem_sdiff]
      tauto
    rw [e]
    exact heΛ.diff he
  · intro Ns _ _ hNs
    choose m hm he using hNs
    refine ⟨⋃ i, m i, MeasurableSet.iUnion hm, ?_⟩
    rw [preimage_iUnion, iUnion_inter]
    exact Filter.EventuallyEqSet.countable_iUnion he

/-- **The record events after the stop are marked events**: for `C ⊇ U` a nonempty compact of `ℍ` and a measurable set
`M` of histories, `{C ∩ recorded hull = ∅} ∩ {history ∈ M}` lies in the marked σ-algebra at the stop. -/
theorem measurableSet_markSigmaQ_recHull [IsProbabilityMeasure P]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hreg : IsRegularStop ρL ρR P W VL VR V)
    {U C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) (hCne : C.Nonempty) (hUC : U ⊆ C)
    {M : Set (HistorySpace nL nR)} (hM : MeasurableSet M) :
    MeasurableSet[markSigmaQ P W VL VR V U]
      ({ω | Disjoint C (recHull ρL ρR xL xR (killedHistory W VL VR V ω))} ∩ killedHistory W VL VR V ⁻¹' M) := by
  classical
  obtain ⟨hEv, hcont, -, -, hX, -⟩ := id hSC
  have hYm : Measurable (killedHistory W VL VR V) := measurable_killedHistory hX
  set N : Set (HistorySpace nL nR) := historyNormalize ⁻¹' ({γ | ¬ recMask ρL ρR xL xR γ} ∩ M) with hNdef
  have hN : MeasurableSet[preMarkSigma] N :=
    measurableSet_preimage_historyNormalize ((measurableSet_recMask ρL ρR xL xR).compl.inter hM)
  obtain ⟨m, hm, he⟩ := exists_markSigmaQ_version hSC hseed hreg hC hCH hCne hUC hN
  refine measurableSet_markSigmaQ_of_ae_eq U
    ((hYm (isMeasHull_recHull ρL ρR xL xR C hC)).inter (hYm hM)) hm (EventuallyEq.trans ?_ he.symm)
  filter_upwards [hEv.ae_path, hcont, hreg] with ω hp hcω hrω
  apply propext
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, hNdef, historyNormalize_killedHistory]
  by_cases hmask : recMask ρL ρR xL xR (killedHistory W VL VR V ω)
  · have hu : recHull ρL ρR xL xR (killedHistory W VL VR V ω) = univ := by
      simp only [recHull, hmask, ↓reduceIte]
    rw [hu]
    constructor
    · rintro ⟨hd, -⟩
      obtain ⟨z, hz⟩ := hCne
      exact absurd (mem_univ z) (Set.disjoint_left.1 hd hz)
    · rintro ⟨⟨h1, -⟩, -⟩
      exact absurd hmask h1
  · have hVtop : V ω ≠ ⊤ := fun ht => hmask (Or.inl ht)
    set T : ℝ≥0 := (V ω).toNNReal with hTdef
    have hT : (T : ℝ≥0∞) = V ω := ENNReal.coe_toNNReal hVtop
    have hc : ContinuousOn (dState W VL VR ω) (Iic T) := hcω T hT
    have h0 : dState W VL VR ω 0 = initVal xL xR := by
      simp only [dState, initVal, hp.w_zero, Prod.mk.injEq, true_and]
      exact ⟨funext hp.vL_zero, funext hp.vR_zero⟩
    have hstop := stopVal_killedHistory (xL := xL) (xR := xR) hT hc h0
    have hnt : ¬ ForceWord.ThresholdCondition ρL ρR (W T ω) (fun i => VL i T ω) (fun j => VR j T ω) := by
      intro hth
      refine hmask (Or.inr ?_)
      rw [hstop]
      exact hth
    obtain ⟨T', hTT', hw⟩ := hrω T hT hnt
    rw [recHull_of_not_mask hmask, regHull_recH_killedHistory hT hc h0 hTT' hw]
    have hlim : ω ∈ avoidLim W V C ↔
        Disjoint C (closure (fwdHull (fun r : ℝ => W r.toNNReal ω) T) ∩ (upperHalfPlaneOpens : Set ℂ)) := by
      have hk : ∀ k : ℕ, (min ((k : ℝ≥0) : ℝ≥0∞) (V ω)).toNNReal ≤ T := fun k => by
        rw [← hT, ← ENNReal.coe_le_coe, ENNReal.coe_toNNReal
          (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
        exact min_le_right _ _
      constructor
      · intro h'
        obtain ⟨k, hk'⟩ := exists_nat_ge (T : ℝ)
        have e : (min ((k : ℝ≥0) : ℝ≥0∞) (V ω)).toNNReal = T := by
          rw [← hT, min_eq_right (ENNReal.coe_le_coe.2 (by rw [← NNReal.coe_le_coe]; exact_mod_cast hk'))]
          rfl
        have := h' k
        simp only [clHull, e] at this
        exact this
      · intro h' k
        refine h'.mono_right (inter_subset_inter_left _ (closure_mono (QuantumZipper.fwdHull_mono.1 ?_)))
        exact_mod_cast hk k
    rw [hlim]
    tauto

end Indep

end Aux54

end Restart

end InteractingSLE
