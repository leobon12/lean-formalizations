/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50HitPath

/-!
# Aux. lemma 50 for every `κ < 8`: the label means are the Borel functionals of the history

Packet PROVE-AUX50B. Follow-up note C.3 (`source/external/AstraIG1/ig1_followup_proofs.txt` L1560–1650, "Pass the
marked kernels to the announced birth": "Hence the displayed mean pairings converge on the component event. Their
limits are functions of the stopped driving history, since every announcing time and canonical mean in the sequence
is such a function") and (WF2): "The mean `M_τ` is a measurable function of the recorded driving history. On the
active component it equals `m_τ`; in each pocket it is the harmonic limit of `m_s` as `s` increases to that pocket's
first disconnection time, and is thereafter frozen."

For a coupling with the frozen optional hull specification and infinite lifetime:

* `ae_charMean_eq_condExp`: at a stopping rule `S`, on `{supp ψ ∩ K_S = ∅}`, the tested mean read from the Borel
  characteristic functional of the history (`charMean (histG …)`) is `E[(h, ψ) | 𝓕_S]` (the frozen kernel at every
  multiple `(j+1)⁻¹ ψ`);
* `isStoppingTime_safeKRule`: the safe exit rules of a compact set are stopping times of the driving filtration;
* **`ae_condExp_eq_iSup_of_pocket`** (the freeze at a birth): along the safe exit rules `ρ_k` of `supp ψ`, on the event
  that `supp ψ` is a pocket at `N`, `E[(h, ψ) | 𝓕_N] = E[(h, ψ) | 𝓕_T]` with `T = sup ρ_k` the birth time, and
  `E[(h, ψ) | 𝓕_{ρ_k}] → E[(h, ψ) | 𝓕_T]` (Lévy). This is PROVE-WHOLEFIELD9's birth step
  (`WholeField.ae_condExp_exp_eq_cmKer_of_birth`, whose freeze is internal) with these explicit announcing rules;
* **`ae_labelMean_eq_condExp`**: on the event that `supp ψ` is a label at `N`, the Borel label mean of the history
  stopped at `N` is `E[(h, ψ) | 𝓕_N]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Aux50Hit

open LawUnique Sec4 QuantumZipper LQGMetric WholeField

variable {nL nR : ℕ}

/-! ### The Borel characteristic functional -/

/-- **The Borel conditional characteristic functional** of the frozen hull specification at the recorded stop
(`Sec4.hasMeasurableHistCharFun`). -/
def histG (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ :=
  Classical.choose (hasMeasurableHistCharFun κ ρL ρR)

theorem measurable_histG (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (φ : TestOn upperHalfPlaneOpens) :
    Measurable (histG κ ρL ρR φ) :=
  (Classical.choose_spec (hasMeasurableHistCharFun κ ρL ρR)).1 φ

theorem histG_eq (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (φ : TestOn upperHalfPlaneOpens)
    (γ : HistorySpace nL nR) (hγ : IsContHist γ) (hd : Disjoint (tsupport φ) (histHull γ)) :
    histG κ ρL ρR φ γ = histCharFun κ ρL ρR φ γ :=
  (Classical.choose_spec (hasMeasurableHistCharFun κ ρL ρR)).2 φ γ hγ hd

/-- The safe exit rule of `K` read on a killed history (through the history stopped at `N`). -/
def safeKRule (K : Set ℂ) (m : ℝ) (N k : ℕ) : HistorySpace nL nR → ℝ≥0 :=
  fun x => safeRule K m N k (stopHistory (natStop N) x)

theorem measurable_safeKRule {K : Set ℂ} (hKH : K ⊆ H) {m : ℝ} (hm : 0 < m) (N k : ℕ) :
    Measurable (safeKRule (nL := nL) (nR := nR) K m N k) :=
  (measurable_safeRule hKH hm N k).comp (measurable_stopHistory (measurable_natStop N))

section Coupling

universe v

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-! ### The tested mean at a stopping rule -/

/-- **The active mean at a stopping rule is the Borel tested mean of the stopped history.** On
`{supp ψ ∩ K_S = ∅}`, `charMean (histG …) ψ (history through S) = E[(h, ψ) | 𝓕_S]`. -/
theorem ae_charMean_eq_condExp (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hX : IsMeasurableKilledDriving W VL VR ζ) {s : HistorySpace nL nR → ℝ≥0}
    (hS : IsStoppingTime (drivingFiltration P hX) (ruleTime s W VL VR ζ)) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (Ito.rpath fun t => W t ω) (s (killedHistory W VL VR ζ ω))) →
      charMean (histG κ ρL ρR) ψ (stopHistory s (killedHistory W VL VR ζ ω)) =
        (P[fun ω' => h ω' ψ | hS.measurableSpace]) ω := by
  have hSζ : ∀ᵐ ω ∂P, (s (killedHistory W VL VR ζ ω) : ℝ≥0∞) < ζ ω :=
    hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top
  have hgood := ae_isGoodPath hC.1 hζ
  have hcf : ∀ j : ℕ, ∀ᵐ ω ∂P, Disjoint (tsupport ((1 / ((j : ℝ) + 1)) • ψ))
      (regHull (stopHistory s (killedHistory W VL VR ζ ω))) →
      P[fun o => Complex.exp (↑(h o ((1 / ((j : ℝ) + 1)) • ψ)) * Complex.I) | hS.measurableSpace] ω =
        histG κ ρL ρR ((1 / ((j : ℝ) + 1)) • ψ) (stopHistory s (killedHistory W VL VR ζ ω)) := fun j =>
    hC.ae_condExp_hist (A := regHull) (fun γ hγ => hγ.regHull_eq) (histG_eq κ ρL ρR) hX hS hSζ _
  have hact : ∀ j : ℕ, ∀ᵐ ω ∂P, Disjoint (tsupport ψ)
      (fwdHull (fun r : ℝ => W r.toNNReal ω) (s (killedHistory W VL VR ζ ω) : ℝ)) →
      (P[fun ω' => cexp (I * (((1 / ((j : ℝ) + 1)) * h ω' ψ : ℝ) : ℂ)) | hS.measurableSpace]) ω =
        cexp (I * (((1 / ((j : ℝ) + 1)) * actMean κ ρL ρR W VL VR (s (killedHistory W VL VR ζ ω)) ψ ω : ℝ) : ℂ) -
          (((1 / 2) * ((1 / ((j : ℝ) + 1)) ^ 2 *
            WangWu.retainedGreenEnergy (W · ω) (s (killedHistory W VL VR ζ ω)) ψ) : ℝ) : ℂ)) := fun j =>
    ae_condExp_exp_smul_eq_of_active (σ := fun ω => s (killedHistory W VL VR ζ ω)) hC hX hS hSζ ψ _
  have hmean := ae_condExp_pairing_eq_actMean (σ := fun ω => s (killedHistory W VL VR ζ ω)) hC hX hS hSζ ψ
  filter_upwards [ae_all_iff.2 hcf, ae_all_iff.2 hact, hmean, hgood] with ω h1 h2 h3 hg hd
  have hreg := regHull_stopHistory hg s
  refine Eq.trans ?_ (h3 hd).symm
  refine charMean_eq (v := WangWu.retainedGreenEnergy (W · ω) (s (killedHistory W VL VR ζ ω)) ψ) fun j => ?_
  have hd' : Disjoint (tsupport ((1 / ((j : ℝ) + 1)) • ψ))
      (regHull (stopHistory s (killedHistory W VL VR ζ ω))) := by
    rw [hreg]
    exact hd.mono_left (tsupport_smul_subset_right (fun _ => (1 / ((j : ℝ) + 1))) ψ)
  rw [← h1 j hd']
  have e : (fun o => Complex.exp (↑(h o ((1 / ((j : ℝ) + 1)) • ψ)) * Complex.I)) =
      fun ω' => cexp (I * (((1 / ((j : ℝ) + 1)) * h ω' ψ : ℝ) : ℂ)) := by
    funext o
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [e, h2 j hd]
  rfl

/-! ### The safe exit rules along a coupling -/

omit [IsProbabilityMeasure P] in
/-- A measurable full-measure set of good paths. -/
theorem exists_goodSet (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∃ G₀ : Set Ω, MeasurableSet G₀ ∧ P G₀ᶜ = 0 ∧ ∀ ω ∈ G₀, IsGoodPath W VL VR ζ ω := by
  have hae := ae_isGoodPath hE hζ
  refine ⟨(toMeasurable P {ω | ¬ IsGoodPath W VL VR ζ ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
    fun ω hω => ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
  · by_contra h'; exact hω (subset_toMeasurable _ _ h')

omit [IsProbabilityMeasure P] in
/-- **The safe exit rules are stopping times** of the driving filtration. -/
theorem isStoppingTime_safeKRule (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hX : IsMeasurableKilledDriving W VL VR ζ) {K : Set ℂ} (hKH : K ⊆ H) {m : ℝ}
    (hm : 0 < m) (N k : ℕ) :
    IsStoppingTime (drivingFiltration P hX) (ruleTime (safeKRule K m N k) W VL VR ζ) := by
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨G₀, hG₀m, hG₀c, hG₀g⟩ := exists_goodSet hE hζ
  have hG₀ : ∀ t, MeasurableSet[drivingFiltration P hX t] G₀ := fun t => by
    have := (Ito.measurableSet_usualAugmentation_of_null (𝓕 := killedDrivingFiltration hX) hG₀m.compl hG₀c
      t).compl
    rwa [compl_compl] at this
  obtain ⟨D, hDK, hDc, hKD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  set δ : ℝ := m / ((k : ℝ) + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hWa : AdaptedBefore (drivingFiltration P hX) ζ W :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hwc : ∀ ω ∈ G₀, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω => (hG₀g ω hω).2.2.1
  have hform : ∀ ω ∈ G₀, safeKRule K m N k (killedHistory W VL VR ζ ω) =
      Coupling.safeExitTime K δ k N (ζ ω) (fun t => W t ω) := fun ω hω => by
    rw [safeKRule, safeRule_eq (hG₀g ω hω), (hG₀g ω hω).1]
  have hρm : Measurable fun ω => safeKRule K m N k (killedHistory W VL VR ζ ω) :=
    (measurable_safeKRule hKH hm N k).comp (measurable_killedHistory hX)
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
  obtain ⟨T, hTc, hTd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have heq : {ω | ruleTime (safeKRule K m N k) W VL VR ζ ω < (t : WithTop ℝ≥0)} =
      (⋃ d ∈ T ∩ Iio t, G₀ \ {ω | ω ∈ G₀ ∧ Coupling.IsSafeAt D δ k ((fun _ => (N : ℝ≥0)) ω) (ζ ω)
        (fun t => W t ω) d}) ∪ (G₀ᶜ ∩ {ω | safeKRule K m N k (killedHistory W VL VR ζ ω) < t}) := by
    ext ω
    simp only [ruleTime, mem_ofPred_eq, WithTop.coe_lt_coe, mem_union, mem_iUnion, mem_inter_iff,
      Set.mem_sdiff, mem_Iio, exists_prop, mem_compl_iff]
    by_cases hω : ω ∈ G₀
    · simp only [hω, true_and, not_true_eq_false, false_and, or_false]
      rw [hform ω hω, Coupling.safeExitTime_lt_iff (hwc ω hω) hKH hTd]
      have hDiff : ∀ d : ℝ≥0, Coupling.IsSafeAt K δ k N (ζ ω) (fun t => W t ω) d ↔
          Coupling.IsSafeAt D δ k N (ζ ω) (fun t => W t ω) d := fun d =>
        ⟨fun h' => h'.subset hDK, fun h' => h'.of_dense (hwc ω hω) hKH hKD hDK hδ⟩
      constructor
      · rintro ⟨d, hd, hdt, hnp⟩; exact ⟨d, ⟨hd, hdt⟩, fun h' => hnp ((hDiff d).2 h')⟩
      · rintro ⟨d, ⟨hd, hdt⟩, hnp⟩; exact ⟨d, hd, hdt, fun h' => hnp ((hDiff d).1 h')⟩
    · simp only [hω, false_and, and_false, exists_false, false_or, not_false_eq_true, true_and]
  rw [heq]
  refine MeasurableSet.union (MeasurableSet.biUnion (hTc.mono inter_subset_left) fun d hd => ?_) ?_
  · exact (drivingFiltration P hX).mono hd.2.le _ ((hG₀ d).diff (Coupling.measurableSet_isSafeAt hWa hwc
      (hG₀ 0) hDc (hDK.trans hKH) (isStoppingTime_const _ _) δ k d))
  · refine Ito.measurableSet_usualAugmentation_of_null (hG₀m.compl.inter
      (measurableSet_lt hρm measurable_const)) (measure_mono_null inter_subset_left hG₀c) t

omit mΩ [IsProbabilityMeasure P] in
/-- **The safe exit rules along a good path**: monotone, at most `N`, the compact set is alive at each of them, and
they exhaust every time `t ≤ N` at which it is alive. -/
theorem safeKRule_props {ω : Ω} (hg : IsGoodPath W VL VR ζ ω) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    {m : ℝ} (hm : 0 < m) (hKm : ∀ z ∈ K, m ≤ z.im) (N : ℕ) :
    Monotone (fun k => safeKRule K m N k (killedHistory W VL VR ζ ω)) ∧
      (∀ k, safeKRule K m N k (killedHistory W VL VR ζ ω) ≤ N) ∧
      (∀ k, Disjoint K (fwdHull (Ito.rpath fun t => W t ω) (safeKRule K m N k (killedHistory W VL VR ζ ω)))) ∧
      ∀ t : ℝ≥0, t ≤ N → Disjoint K (fwdHull (Ito.rpath fun t => W t ω) t) →
        ∀ᶠ k in atTop, t ≤ safeKRule K m N k (killedHistory W VL VR ζ ω) := by
  have hform : ∀ k, safeKRule K m N k (killedHistory W VL VR ζ ω) =
      Coupling.safeExitTime K (m / ((k : ℝ) + 1)) k N ⊤ (fun t => W t ω) := fun k => safeRule_eq hg K m N k
  have hw : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} := hg.continuous.continuousOn
  refine ⟨fun k k' hkk' => ?_, fun k => ?_, fun k => ?_, fun t htN hdis => ?_⟩
  · simp only [hform]
    have hk : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
    exact Coupling.safeExitTime_mono (div_le_div_of_nonneg_left hm.le (by positivity) (by linarith)) hk le_rfl
  · rw [hform]; exact Coupling.safeExitTime_le_sigma
  · rw [hform]
    have hn1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [k.cast_nonneg (α := ℝ)]
    have h0 : Coupling.IsSafeAt K (m / ((k : ℝ) + 1)) k N ⊤ (fun t => W t ω) 0 :=
      Coupling.isSafeAt_zero hKH (fun z hz => (div_le_self hm.le hn1).trans (hKm z hz)) hg.2.1
        ENNReal.zero_lt_top k.cast_nonneg
    have hs := Coupling.isSafeAt_safeExitTime hw hKH (by positivity) ENNReal.coe_lt_top h0
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    obtain ⟨u, hu⟩ := (hs.2.2.2 z hz).1
    exact Ito.notMem_fwdHull_of_isForwardSol hg.continuous_rpath (lt_of_lt_of_le hm (hKm z hz))
      (NNReal.coe_nonneg _) hu hzK
  · have halive : ∀ z ∈ K, ∃ u, IsForwardSol (Ito.rpath fun t => W t ω) z t u := fun z hz =>
      exists_isForwardSol_of_not_mem_fwdHull t.coe_nonneg (hKH hz) fun hzK =>
        Set.disjoint_left.1 hdis hz hzK
    filter_upwards [Coupling.eventually_le_safeExitTime hw hK hKH m (σ₀ := (N : ℝ≥0)) (by exact_mod_cast htN)
      ENNReal.coe_lt_top halive] with k hk
    rw [hform]; exact hk

/-! ### The freeze at a birth -/

/-- **The pocket mean at `N` is the limit of the active means along the safe exit rules** (the birth step of
follow-up note C.3 with the explicit announcing rules). For a test `ψ` with nonempty support and `N ≥ 1`: almost
surely on the event that `supp ψ` is a pocket at `N` (swallowed at one time `β ≤ N`),
`E[(h, ψ) | 𝓕_{ρ_k}] → E[(h, ψ) | 𝓕_N]`, `ρ_k` the safe exit rules of `supp ψ`. The safe exit rules increase to `β`
(Lévy's upward theorem gives the limit `E[(h, ψ) | 𝓕_β]`) and the birth transfer `WholeField.ae_condExp_eq_of_birth`
freezes the conditional law after `β`. -/
theorem ae_tendsto_condExp_safeKRule_of_pocket (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hX : IsMeasurableKilledDriving W VL VR ζ) {N : ℕ} (hN1 : 1 ≤ N)
    (ψ : TestOn upperHalfPlaneOpens) (hne : (tsupport ψ).Nonempty)
    (hN : IsStoppingTime (drivingFiltration P hX) (ruleTime (natStop N) W VL VR ζ)) :
    ∀ᵐ ω ∂P, IsPocketLabel (fun t => W t ω) (tsupport ψ) N →
      Tendsto (fun k => (P[fun ω' => h ω' ψ | (isStoppingTime_safeKRule hC.1 hζ hX ψ.tsupport_subset
        (testLow_pos ψ) N k).measurableSpace]) ω) atTop (𝓝 ((P[fun ω' => h ω' ψ | hN.measurableSpace]) ω)) := by
  have hE := hC.1
  obtain ⟨u₀, hu₀⟩ := exists_bhe κ ρL ρR xL xR
  set K : Set ℂ := tsupport ψ with hKdef
  have hK : IsCompact K := ψ.hasCompactSupport.isCompact
  have hKH : K ⊆ H := ψ.tsupport_subset
  set m : ℝ := testLow ψ with hmdef
  have hm : 0 < m := testLow_pos ψ
  have hKm : ∀ z ∈ K, m ≤ z.im := fun z hz => testLow_le ψ hz
  set ρ : ℕ → Ω → ℝ≥0 := fun k ω => safeKRule K m N k (killedHistory W VL VR ζ ω) with hρdef
  have hρ : ∀ k, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ k ω : WithTop ℝ≥0) := fun k =>
    isStoppingTime_safeKRule hE hζ hX hKH hm N k
  have hgood := ae_isGoodPath hE hζ
  -- the properties of the safe rules, for every `ω`
  have hρN : ∀ k ω, ρ k ω ≤ (N : ℝ≥0) := fun k ω => safeRule_le K m N k _
  have hρm : ∀ ω, Monotone fun k => ρ k ω := by
    intro ω k k' hkk'
    simp only [hρdef, safeKRule, safeRule]
    have hk : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
    exact Coupling.safeExitTime_mono (div_le_div_of_nonneg_left hm.le (by positivity) (by linarith)) hk le_rfl
  have hbdd : ∀ ω, BddAbove (range fun k => ρ k ω) := fun ω => ⟨N, by rintro _ ⟨k, rfl⟩; exact hρN k ω⟩
  set T : Ω → ℝ≥0 := fun ω => ⨆ k, ρ k ω with hTdef
  have hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0) :=
    WangWu.isStoppingTime_iSup_coe hρ hρN
  have hTN : ∀ ω, T ω ≤ N := fun ω => ciSup_le fun k => hρN k ω
  have hρT : ∀ k ω, ρ k ω ≤ T ω := fun k ω => le_ciSup (hbdd ω) k
  have hρlim : ∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (T ω)) := fun ω =>
    tendsto_atTop_ciSup (hρm ω) (hbdd ω)
  have hTζ : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω := hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top
  have hρζ : ∀ k, ∀ᵐ ω ∂P, (ρ k ω : ℝ≥0∞) < ζ ω := fun k =>
    hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top
  have hdis : ∀ᵐ ω ∂P, ∀ k, Disjoint K (fwdHull (Ito.rpath fun t => W t ω) (ρ k ω)) := by
    filter_upwards [hgood] with ω hg using (safeKRule_props hg hK hKH hm hKm N).2.2.1
  have hT0 : ∀ᵐ ω ∂P, 0 < T ω ∨ ∀ i j, xL i < xR j := by
    filter_upwards [hgood] with ω hg
    left
    obtain ⟨t, ht0, -, htd⟩ := exists_pos_disjoint_fwdHull_of_path hg.2.2.1 hg.2.1
      (by rw [hg.1]; exact ENNReal.zero_lt_top) hK hKH
    have ht1 : min t 1 ≤ (N : ℝ≥0) := (min_le_right _ _).trans (by exact_mod_cast hN1)
    have hd1 : Disjoint K (fwdHull (Ito.rpath fun t => W t ω) (min t 1 : ℝ≥0)) :=
      htd.mono_right (fwdHull_mono.1 (by exact_mod_cast min_le_left t 1))
    obtain ⟨k, hk⟩ := ((safeKRule_props hg hK hKH hm hKm N).2.2.2 _ ht1 hd1).exists
    exact lt_of_lt_of_le (lt_min ht0 one_pos) (hk.trans (hρT k ω))
  -- the event facts
  set E : Set Ω := {ω | IsPocketLabel (fun t => W t ω) K N} with hEdef
  have hev : ∀ᵐ ω ∂P, ω ∈ E → ∃ β : ℝ≥0, T ω = β ∧ (∀ k, ρ k ω < β) ∧
      (∀ z ∈ K, swallowTime (Ito.rpath fun t => W t ω) z = β) ∧ β ≤ N := by
    filter_upwards [hgood] with ω hg ⟨β, hβN, hβ⟩
    obtain ⟨-, -, hd, hex⟩ := safeKRule_props hg hK hKH hm hKm N
    obtain ⟨z₀, hz₀⟩ := hne
    have hlt : ∀ k, ρ k ω < β := fun k => by
      by_contra hle
      refine Set.disjoint_left.1 (hd k) hz₀ (mem_fwdHull_rpath_iff.2 ⟨hKH hz₀, ?_⟩)
      rw [hβ z₀ hz₀]; exact_mod_cast not_lt.1 hle
    refine ⟨β, le_antisymm (ciSup_le fun k => (hlt k).le) ?_, hlt, hβ, hβN⟩
    refine le_of_forall_lt_imp_le_of_dense fun t ht => ?_
    have hdisj : Disjoint K (fwdHull (Ito.rpath fun t => W t ω) (t : ℝ)) :=
      isActiveLabel_of_lt_swallowTime (w := fun t => W t ω) (C := K) (t := t) fun z hz => by
        rw [hβ z hz]; exact_mod_cast ht
    obtain ⟨k, hk⟩ := (hex t (ht.le.trans hβN) hdisj).exists
    exact hk.trans (hρT k ω)
  -- the hull version at the birth stop and the pocket event
  obtain ⟨AT, hATm, hATK, hAT𝓕⟩ := exists_hullVersion hC hκ hX hT hTζ
  obtain ⟨F, hFm, hFsub, hFmem⟩ := exists_pocketEvent hAT𝓕 hKH
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P := integrable_pairing hC
  have hNσ : IsStoppingTime (drivingFiltration P hX) fun _ : Ω => ((N : ℝ≥0) : WithTop ℝ≥0) := hN
  -- the birth transfer, for every multiple
  have hpre : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ E →
      (P[fun ω' => cexp (I * (h ω' (c • ψ) : ℂ)) | hN.measurableSpace]) ω =
        WangWu.gaussCF ((P[fun ω' => h ω' (c • ψ) | hT.measurableSpace]) ω)
          (WangWu.retainedGreenEnergy (W · ω) N (c • ψ)) := by
    intro c
    have hFZ : StronglyMeasurable[histGerm hT.measurableSpace AT (centredField h u₀)]
        (F.indicator fun ω => cexp (I * (h ω (c • ψ) : ℂ))) :=
      stronglyMeasurable_indicator_exp_histGerm (h := h) hu₀.1 hFm fun ω hω δ hδ =>
        (tsupport_smul_subset_right (fun _ => c) ψ).trans (hFsub ω hω δ hδ)
    have h1 : ∀ k, ∀ᵐ ω ∂P, ω ∈ {ω | Disjoint (tsupport (c • ψ))
        (fwdHull (fun s : ℝ => W s.toNNReal ω) (ρ k ω))} →
        (P[fun ω' => cexp (I * (h ω' (c • ψ) : ℂ)) | (hρ k).measurableSpace]) ω =
          cmKer P (hρ k).measurableSpace h W (ρ k ω) (c • ψ) ω := fun k =>
      ae_condExp_exp_eq_cmKer_of_active hC hX (hρ k) (hρζ k) (c • ψ)
    have h2 : ∀ᵐ ω ∂P, ω ∈ E → ∀ᶠ k in atTop, ω ∈ {ω | Disjoint (tsupport (c • ψ))
        (fwdHull (fun s : ℝ => W s.toNNReal ω) (ρ k ω))} := by
      filter_upwards [hdis] with ω hd _
      exact Eventually.of_forall fun k =>
        (hd k).mono_left (tsupport_smul_subset_right (fun _ => c) ψ)
    have hlev := ae_tendsto_condExp_real_of_announce hC hκ hu₀ hX hT hTζ hT0 hρ hρm hρT
      (Eventually.of_forall hρlim) (hint (c • ψ))
    have h3 : ∀ᵐ ω ∂P, ω ∈ E → Tendsto (fun k => cmKer P (hρ k).measurableSpace h W (ρ k ω) (c • ψ) ω)
        atTop (𝓝 (WangWu.gaussCF ((P[fun ω' => h ω' (c • ψ) | hT.measurableSpace]) ω)
          (WangWu.retainedGreenEnergy (W · ω) (T ω) (c • ψ)))) := by
      filter_upwards [hlev, hgood, hTζ] with ω hl hg hTω _
      have hc := continuous_retainedGreenForm_min_of_path hg.2.2.1 hg.2.1 hTω
        (isTestFn_of_testOn (c • ψ)) (isTestFn_of_testOn (c • ψ))
      have hgreen : Tendsto (fun k => WangWu.retainedGreenEnergy (W · ω) (ρ k ω) (c • ψ)) atTop
          (𝓝 (WangWu.retainedGreenEnergy (W · ω) (T ω) (c • ψ))) := by
        have h1 := (hc.tendsto (T ω)).comp (hρlim ω)
        rw [min_self] at h1
        refine h1.congr fun k => ?_
        simp only [Function.comp_apply, min_eq_left (hρT k ω)]
        rfl
      exact (WangWu.continuous_gaussCF.tendsto _).comp (hl.prodMk_nhds hgreen)
    have h4 : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ F ∧ T ω ≤ (fun _ => (N : ℝ≥0)) ω := by
      filter_upwards [hev, hATK] with ω hevω hATω hωE
      obtain ⟨β, hTβ, -, hβ, -⟩ := hevω hωE
      refine ⟨hFmem ω ?_, hTN ω⟩
      rw [hATω, hTβ]
      intro z hz
      refine ⟨hKH hz, ?_⟩
      show swallowTime (Ito.rpath (W · ω)) z ≤ ENNReal.ofReal ((β : ℝ≥0) : ℝ)
      rw [ENNReal.ofReal_coe_nnreal, hβ z hz]
    have hbirth := ae_condExp_eq_of_birth (σ := fun _ => (N : ℝ≥0)) hC hκ hu₀ hX hT hNσ hTζ hT0 hρ hρm hρT
      (Eventually.of_forall hρlim) hATm hATK (aestronglyMeasurable_exp_pairing hC.2.1 (c • ψ))
      (fun ω => norm_exp_I_mul_pairing (c • ψ) ω) hFm hFZ h1 h2 h3 h4
    filter_upwards [hbirth, hev] with ω hb1 hevω hωE
    obtain ⟨β, hTβ, -, hβ, hβN⟩ := hevω hωE
    refine (hb1 hωE).trans ?_
    congr 1
    rw [hTβ]
    refine (retainedGreenEnergy_eq_of_swallowTime_le (fun z hz => ?_) hβN).symm
    rw [hβ z ((tsupport_smul_subset_right (fun _ => c) ψ) (subset_tsupport _ hz))]
  -- the freeze of the conditional mean
  have hfreeze : ∀ᵐ ω ∂P, ω ∈ E →
      (P[fun ω' => h ω' ψ | hN.measurableSpace]) ω = (P[fun ω' => h ω' ψ | hT.measurableSpace]) ω := by
    refine ae_condExp_eq_of_condCharFun_on (hint ψ)
      (v := fun ω => WangWu.retainedGreenEnergy (W · ω) N ψ) fun c => ?_
    filter_upwards [hpre c, condExp_pairing_smul (P := P) hT.measurableSpace h c ψ] with ω h1 h2 hωE
    rw [← exp_pairing_smul, h1 hωE, h2]
    first
    | rw [retainedGreenEnergy_testOn_smul, WangWu.gaussCF]
    | rw [retainedGreenEnergy_smul, WangWu.gaussCF]
  have hlev := ae_tendsto_condExp_real_of_announce hC hκ hu₀ hX hT hTζ hT0 hρ hρm hρT
    (Eventually.of_forall hρlim) (hint ψ)
  filter_upwards [hlev, hfreeze] with ω hl hfr hωE
  rw [hfr hωE]
  exact hl

/-! ### The label means -/

omit mΩ [IsProbabilityMeasure P] in
/-- On a good path no nonempty compact subset of `ℍ` is swallowed at time `0`. -/
theorem not_isPocketLabel_zero {ω : Ω} (hg : IsGoodPath W VL VR ζ ω) {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ H) (hne : K.Nonempty) : ¬ IsPocketLabel (fun t => W t ω) K 0 := by
  rintro ⟨β, hβ0, hβ⟩
  obtain ⟨t, ht0, -, htd⟩ := exists_pos_disjoint_fwdHull_of_path hg.2.2.1 hg.2.1
    (by rw [hg.1]; exact ENNReal.zero_lt_top) hK hKH
  obtain ⟨z₀, hz₀⟩ := hne
  refine Set.disjoint_left.1 htd hz₀ (mem_fwdHull_rpath_iff.2 ⟨hKH hz₀, ?_⟩)
  rw [hβ z₀ hz₀, le_antisymm hβ0 zero_le]
  exact_mod_cast zero_le

/-- **The label mean of the history at `N` is the conditional mean** (follow-up note (WF2): "On the active component
it equals `m_τ`; in each pocket it is the harmonic limit of `m_s` as `s` increases to that pocket's first
disconnection time, and is thereafter frozen"): almost surely, if `supp ψ` is a label at `N`,
`labelMean (histG …) N ψ (history through N) = E[(h, ψ) | 𝓕_N]`. -/
theorem ae_labelMean_eq_condExp (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hX : IsMeasurableKilledDriving W VL VR ζ) (N : ℕ)
    (hN : IsStoppingTime (drivingFiltration P hX) (ruleTime (natStop N) W VL VR ζ))
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, IsLabel (fun t => W t ω) (tsupport ψ) N →
      labelMean (histG κ ρL ρR) N ψ (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) =
        (P[fun ω' => h ω' ψ | hN.measurableSpace]) ω := by
  have hE := hC.1
  have hgood := ae_isGoodPath hE hζ
  set K : Set ℂ := tsupport ψ with hKdef
  have hK : IsCompact K := ψ.hasCompactSupport.isCompact
  have hKH : K ⊆ H := ψ.tsupport_subset
  have hact := ae_charMean_eq_condExp (κ := κ) (ρL := ρL) (ρR := ρR) hC hζ hX hN ψ
  have hst : stopHistory (cstop (N : ℝ≥0)) = stopHistory (nL := nL) (nR := nR) (natStop N) := rfl
  by_cases hne : K.Nonempty
  swap
  · -- empty support: always active
    have hemp : tsupport ⇑ψ = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    filter_upwards [hact, hgood] with ω h1 hg _
    have hd : Disjoint (tsupport ⇑ψ) (regHull (stopHistory (cstop N) (stopHistory (natStop N)
        (killedHistory W VL VR ζ ω)))) := by
      rw [hemp]; exact Set.empty_disjoint _
    simp only [labelMean, hd, ↓reduceIte]
    rw [stopHistory_cstop_natStop le_rfl, hst]
    exact h1 (by rw [hemp]; exact Set.empty_disjoint _)
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · -- `N = 0`: no pocket
    subst hN0
    filter_upwards [hact, hgood] with ω h1 hg hlab
    have hA : IsActiveLabel (fun t => W t ω) K ((0 : ℕ) : ℝ≥0) :=
      hlab.resolve_right (by have := not_isPocketLabel_zero hg hK hKH hne; simpa using this)
    have hd : Disjoint K (regHull (stopHistory (cstop (0 : ℕ)) (stopHistory (natStop 0)
        (killedHistory W VL VR ζ ω)))) := by
      rw [stopHistory_cstop_natStop le_rfl, regHull_stopHistory_cstop hg]; exact hA
    simp only [labelMean, ← hKdef, hd, ↓reduceIte]
    rw [stopHistory_cstop_natStop le_rfl, hst]
    exact h1 hA
  -- the pocket case uses the safe exit rules
  have hρ : ∀ k, IsStoppingTime (drivingFiltration P hX) (ruleTime (safeKRule K (testLow ψ) N k) W VL VR ζ) :=
    fun k => isStoppingTime_safeKRule hE hζ hX hKH (testLow_pos ψ) N k
  have hρmean : ∀ k, ∀ᵐ ω ∂P, Disjoint K (fwdHull (Ito.rpath fun t => W t ω)
      (safeKRule K (testLow ψ) N k (killedHistory W VL VR ζ ω))) →
      charMean (histG κ ρL ρR) ψ (stopHistory (safeKRule K (testLow ψ) N k) (killedHistory W VL VR ζ ω)) =
        (P[fun ω' => h ω' ψ | (hρ k).measurableSpace]) ω := fun k =>
    ae_charMean_eq_condExp hC hζ hX (hρ k) ψ
  have hlim := ae_tendsto_condExp_safeKRule_of_pocket hC hκ hζ hX hN1 ψ hne hN
  filter_upwards [hact, hgood, ae_all_iff.2 hρmean, hlim] with ω h1 hg h2 h3 hlab
  by_cases hA : IsActiveLabel (fun t => W t ω) K N
  · have hd : Disjoint K (regHull (stopHistory (cstop N) (stopHistory (natStop N)
        (killedHistory W VL VR ζ ω)))) := by
      rw [stopHistory_cstop_natStop le_rfl, regHull_stopHistory_cstop hg]; exact hA
    simp only [labelMean, ← hKdef, hd, ↓reduceIte]
    rw [stopHistory_cstop_natStop le_rfl, hst]
    exact h1 hA
  · have hP : IsPocketLabel (fun t => W t ω) K N := hlab.resolve_left hA
    have hd : ¬ Disjoint K (regHull (stopHistory (cstop N) (stopHistory (natStop N)
        (killedHistory W VL VR ζ ω)))) := by
      rw [stopHistory_cstop_natStop le_rfl, regHull_stopHistory_cstop hg]; exact hA
    simp only [labelMean, ← hKdef, hd, ↓reduceIte, pocketMean]
    obtain ⟨-, -, hdk, -⟩ := safeKRule_props hg hK hKH (testLow_pos ψ) (fun z hz => testLow_le ψ hz) N
    have e : ∀ k, charMean (histG κ ρL ρR) ψ (stopHistory (safeRule K (testLow ψ) N k)
        (stopHistory (natStop N) (killedHistory W VL VR ζ ω))) =
        (P[fun ω' => h ω' ψ | (hρ k).measurableSpace]) ω := fun k => by
      rw [stopHistory_stopHistory_natStop _ (safeRule_le _ _ _ _ _)]
      exact h2 k (hdk k)
    simp only [e]
    exact (h3 hP).limsup_eq

end Coupling

end Aux50Hit

end InteractingSLE
