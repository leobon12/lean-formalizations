/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.HOuterMarkedPathInf

/-!
# The outer pocket opening at the flow seed: the marked stop and the walls' law at `T⁰(q)`

Packet PROVE-HOUTER. The port of PROVE-STRIPSYS43's `PocketStopMarkedInf.lean` (sections `StopInf`, `LawInf`) from the
contained pocket opening at the flow seed (`IsCfPocketConfigInf`) to a mixed or outer one (`HOuter.IsOuterCfgInf`): the
Galmarino property of `stopTimeMInf`, the marks' measurability, and **`pocketStopWallsLaw_stopHull0Inf_marked`**
(Aux. lemma 35's marked union law of the walls with the counterflow hull at `T⁰(q)`, no stop input). Proofs are
STRIPSYS43's with `IsOuterPocketInf` (`HOuterMarkedPathInf`). Declarations in the sub-namespace
`PocketStopMarked.Outer`.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopMarked.Outer

open QuantumZipper (H)
open LQGMetric (DistOn)
open WangWu (negInv)
open PocketCoord PocketJordan PocketWordAssembly PocketStopWallsFin PocketCoupling Lemma71C Lemma71I PocketAdapt
  PocketTraversal PocketSeedOpen

/-- **An outer configuration at infinity with a Jordan coordinate is an `IsOuterPocketInf`.** -/
theorem _root_.InteractingSLE.Sec7.HOuter.IsOuterCfgInf.toPocketInf {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ}
    {η : ℝ → ℂ} (hc : HOuter.IsOuterCfgInf R L r W η) {ψ : ℂ → ℂ} (hψ : IsCfJordanInf R L r ψ) :
    IsOuterPocketInf W η (cfPocket R L r) (cfArcRInf R L r 0) (firstHit η (cfArcRInf R L r 0)) ψ := by
  refine ⟨hc.erase, hc.trace, PocketJordan.image_negInv_subset_H hc.conf.changePocket_subset_H, ?_,
    (hc.props hψ).1⟩
  rw [IsChangeConfigInc.cfArcRInf_zero]
  exact hψ

/-- **`hT` for `T⁰(q)`** (outer pocket opening at the flow seed; `PocketStopWallsFin.stopHull0Inf_eq_regHull`). -/
theorem stopHull0Inf_eq_regHull' {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ω : Ω}
    (hc : HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω)) (hζ : ζ' ω = ⊤) (q : ℝ≥0) :
    stopHull0Inf R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q ω =
      regHull W' ζ' (stopTime0Inf R L r η ψ q ω).toNNReal ω := by
  have h0 : 0 ≤ ambTime0Inf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) q :=
    hc.erase.nonneg.trans (HOuter.pocketFibreLeftInf_props hc.erase
      (clockOf_mem_Ico hc.erase.clockEnd_pos (capInv_nonneg _ _))).1
  rw [regHull_eq (continuous_nnreal_of_continuous_real hc.continuous_W) hζ, stopTime0Inf,
    ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal h0]
  rfl

section StopInf

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳] {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {𝓕 : Filtration ℝ≥0 mΩ} {X : Ω → 𝒳} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {G A : Set Ω} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}

omit mΩ in
theorem adTrace_eq_of_memInf
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {ω : Ω} (hω : ω ∈ A) {u : ℝ} (hu : 0 ≤ u) : adTrace W' ζ' ω u = η ω u := by
  have hc := hcfg ω hω
  have h0 : W' 0 ω = 0 := by simpa using hc.W_zero
  exact adTrace_eq hc.trace hc.continuous_W h0 (hζA ω hω) hu

omit mΩ in
theorem continuousOn_adTraceInf
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {ω : Ω} (hω : ω ∈ A) : ContinuousOn (adTrace W' ζ' ω) (Ici 0) :=
  (hcfg ω hω).trace.2.1.congr fun _ hu => adTrace_eq_of_memInf hcfg hζA hω hu

omit mΩ in
theorem firstHitInf_first {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ} (hc : HOuter.IsOuterCfgInf R L r W η) :
    0 ≤ firstHit η (cfArcR R L r 1) ∧ η (firstHit η (cfArcR R L r 1)) = cfArcR R L r 1 ∧
      cfArcR R L r 1 ∉ η '' Ico 0 (firstHit η (cfArcR R L r 1)) := by
  rw [← cfArcRInf_zero_eq]
  exact PocketJordan.firstHit_spec hc.erase.cont
    ⟨firstHit η (cfArcRInf R L r 0), firstHit η (cfArcRInf R L r 0), ⟨hc.erase.nonneg, le_rfl⟩, hc.erase.first_y⟩

theorem measurableSet_firstHitInf_le (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (u : ℝ≥0) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 u]
      {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) ≤ u} := by
  have hc : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h𝓦u := le_sup_of_le_zero h𝓦 u
  have e : {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) ≤ u} =
      {ω | ω ∈ A ∧ cfArcR (R ω) (L ω) r 1 ∈ adTrace W' ζ' ω '' Icc 0 u} := by
    ext ω
    simp only [mem_ofPred_eq]
    refine and_congr_right fun hω => ?_
    obtain ⟨h0, h1, h2⟩ := firstHitInf_first (hcfg ω hω)
    rw [le_iff_mem_image_of_first h0 h1 h2]
    rw [image_congr fun t ht => adTrace_eq_of_memInf hcfg hζA hω ht.1]
  rw [e]
  exact measurableSet_mem_arc_image (mΩ := MeasurableSpace.comap X inferInstance ⊔ 𝓕 u) h𝓦u hRm hLm hGm hG
    (h𝓦u _ hA) hAG (fun ω hω => continuousOn_adTraceInf hcfg hζA hω) (NNReal.coe_nonneg u)
    (fun u' _ hu' => measurable_adTrace_sup hWad hu') hc

theorem measurableSet_firstHitInf_le_stopping (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {σ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
      {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) ≤ σ ω} := by
  have hc : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have e : {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) ≤ σ ω} = A ∩ ⋂ n : ℕ, ⋃ q : ℚ, ⋃ (_ : 0 ≤ q),
      ({ω | StripSys.rt q ≤ σ ω} ∩ {ω | ω ∈ A ∧ dist (cfArcR (R ω) (L ω) r 1) (adTrace W' ζ' ω (StripSys.rt q)) <
        1 / ((n : ℝ) + 1)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hω, hle⟩
      obtain ⟨h0, h1, h2⟩ := firstHitInf_first (hcfg ω hω)
      have hcont : Continuous fun s : ℝ≥0 => η ω s :=
        (hcfg ω hω).trace.2.1.comp_continuous NNReal.continuous_coe fun s => s.2
      have himg : (fun s : ℝ≥0 => η ω s) '' Icc 0 (σ ω) = η ω '' Icc 0 (σ ω : ℝ) := by
        have := PocketMeas.image_nnPath (η ω) (NNReal.coe_nonneg (σ ω))
        rw [Real.toNNReal_coe] at this
        exact this
      have hmem := (le_iff_mem_image_of_first h0 h1 h2).1 hle
      rw [← himg, StripSys.mem_image_Icc_iff hcont] at hmem
      refine ⟨hω, fun n => ?_⟩
      obtain ⟨q, hq0, hqσ, hd⟩ := hmem n
      refine ⟨q, hq0, ?_, hω, ?_⟩
      · rw [← NNReal.coe_le_coe, StripSys.rt, Real.coe_toNNReal _ (by exact_mod_cast hq0)]
        exact hqσ
      · rw [adTrace_eq_of_memInf hcfg hζA hω (NNReal.coe_nonneg _)]
        simpa using hd
    · rintro ⟨hω, h⟩
      obtain ⟨h0, h1, h2⟩ := firstHitInf_first (hcfg ω hω)
      have hcont : Continuous fun s : ℝ≥0 => η ω s :=
        (hcfg ω hω).trace.2.1.comp_continuous NNReal.continuous_coe fun s => s.2
      have himg : (fun s : ℝ≥0 => η ω s) '' Icc 0 (σ ω) = η ω '' Icc 0 (σ ω : ℝ) := by
        have := PocketMeas.image_nnPath (η ω) (NNReal.coe_nonneg (σ ω))
        rw [Real.toNNReal_coe] at this
        exact this
      refine ⟨hω, (le_iff_mem_image_of_first h0 h1 h2).2 ?_⟩
      rw [← himg, StripSys.mem_image_Icc_iff hcont]
      intro n
      obtain ⟨q, hq0, hqσ, -, hd⟩ := h n
      refine ⟨q, hq0, ?_, ?_⟩
      · rw [← NNReal.coe_le_coe, StripSys.rt, Real.coe_toNNReal _ (by exact_mod_cast hq0)] at hqσ
        exact hqσ
      · rw [adTrace_eq_of_memInf hcfg hζA hω (NNReal.coe_nonneg _)] at hd
        simpa using hd
  rw [e]
  refine (measurableSet_sup_of_zero hσ (h𝓦 _ hA)).inter (MeasurableSet.iInter fun n =>
    MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => ?_)
  have h𝓦q := le_sup_of_le_zero h𝓦 (StripSys.rt q)
  exact measurableSet_le_inter_sup hσ (StripSys.rt q)
    (measurableSet_arc_dist_lt (mΩ := MeasurableSpace.comap X inferInstance ⊔ 𝓕 (StripSys.rt q)) h𝓦q hRm hLm hGm
      hG (h𝓦q _ hA) hAG (measurable_adTrace_sup hWad le_rfl) hc _)

theorem measurableSet_firstHitInf_lt_stopping (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {σ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
      {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < σ ω} := by
  have e : {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < σ ω} = ⋃ q : ℚ, ⋃ (_ : (0 : ℝ) ≤ q),
      ({ω | StripSys.rt q < σ ω} ∩ {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) ≤ StripSys.rt q}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨hω, hlt⟩
      have h0 := (firstHitInf_first (hcfg ω hω)).1
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have hq0 : (0 : ℝ) ≤ q := h0.trans hq1.le
      refine ⟨q, hq0, ?_, hω, by rw [rt_coe hq0]; exact hq1.le⟩
      rw [← NNReal.coe_lt_coe, rt_coe hq0]
      exact hq2
    · rintro ⟨q, hq0, hqσ, hω, hle⟩
      exact ⟨hω, hle.trans_lt (by exact_mod_cast hqσ)⟩
  rw [e]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    measurableSet_lt_inter_sup hσ _ (measurableSet_firstHitInf_le h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA _)

omit mΩ in
theorem relCapInf_eq_ratCap
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) {ω : Ω} (hω : ω ∈ A) {p : ℝ}
    (hp : firstHit (η ω) (cfArcR (R ω) (L ω) r 1) ≤ p) :
    relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (ψ ω) p =
      ratCap A R L r (adTrace W' ζ') ψ p ω := by
  classical
  have hP := (hcfg ω hω).toPocketInf (hψ ω hω)
  rw [cfArcRInf_zero_eq] at hP
  rw [relCapInf_eq_hcapHit_rat hP hp, ratCap]
  have hfun : (fun p' : ℚ => if 0 ≤ (p' : ℝ) ∧ (p' : ℝ) ≤ p ∧ η ω p' ∈ cfPocket (R ω) (L ω) r then
      ψ ω (η ω p') else 0) =
      fun p' : ℚ => if 0 ≤ (p' : ℝ) ∧ (p' : ℝ) ≤ p then visPt A R L r (adTrace W' ζ') ψ p' ω else 0 := by
    funext p'
    by_cases h1 : 0 ≤ (p' : ℝ) ∧ (p' : ℝ) ≤ p
    · have he := adTrace_eq_of_memInf hcfg hζA hω h1.1
      by_cases h2 : η ω p' ∈ cfPocket (R ω) (L ω) r
      · rw [ite_eq_left ⟨h1.1, h1.2, h2⟩, ite_eq_left h1, visPt, ite_eq_left ⟨hω, he ▸ h2⟩, he]
      · rw [ite_eq_right fun h => h2 h.2.2, ite_eq_left h1, visPt,
          ite_eq_right fun (h : ω ∈ A ∧ adTrace W' ζ' ω p' ∈ cfPocket (R ω) (L ω) r) => h2 (he ▸ h.2)]
    · rw [ite_eq_right fun (h : 0 ≤ (p' : ℝ) ∧ (p' : ℝ) ≤ p ∧ η ω p' ∈ cfPocket (R ω) (L ω) r) => h1 ⟨h.1, h.2.1⟩,
        ite_eq_right h1]
  rw [hfun]

theorem measurableSet_ratCapInf_event (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) (p : ℝ≥0) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 p]
      ({ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < p} ∩
        (ratCap A R L r (adTrace W' ζ') ψ p) ⁻¹' B) := by
  have h𝓦p := le_sup_of_le_zero h𝓦 p
  have hlt : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 p]
      {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < p} := by
    have e : {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < p} =
        ⋃ q : ℚ, ⋃ (_ : StripSys.rt q < p), {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) ≤ StripSys.rt q} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hω, hlt⟩
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
        have hq0 : (0 : ℝ) ≤ q := (firstHitInf_first (hcfg ω hω)).1.trans hq1.le
        refine ⟨q, ?_, hω, by rw [rt_coe hq0]; exact hq1.le⟩
        rw [← NNReal.coe_lt_coe, rt_coe hq0]
        exact hq2
      · rintro ⟨q, hq, hω, hle⟩
        exact ⟨hω, hle.trans_lt (by exact_mod_cast hq)⟩
    rw [e]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => (sup_le_sup_left (𝓕.mono hq.le) _) _
      (measurableSet_firstHitInf_le h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA _)
  refine hlt.inter ?_
  exact measurable_ratCapInf (mΩ := MeasurableSpace.comap X inferInstance ⊔ 𝓕 p) h𝓦p hRm hLm hGm hG (h𝓦p _ hA)
    hAG (fun ω hω => (hψ ω hω).1) hψm (fun u' _ hu' => measurable_adTrace_sup hWad hu') hB

omit mΩ in
/-- **The marked stop before `s`** (pathwise, pocket opening at the flow seed). -/
theorem stopTimeMInf_le_iff
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (q : ℝ≥0) {ω : Ω} (hω : ω ∈ A) (s : ℝ≥0) :
    stopTimeMInf A R L r η ψ q ω ≤ s ↔ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) ≤ s ∧
      (q : ℝ) ≤ relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (ψ ω) s := by
  classical
  have hP := (hcfg ω hω).toPocketInf (hψ ω hω)
  have key := live_and_ambTime0Inf_le_iff hP (NNReal.coe_nonneg q) (s : ℝ)
  rw [cfArcRInf_zero_eq] at key
  rw [← key]
  have e0 : (q : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
  unfold stopTimeMInf
  by_cases hl : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)
  · rw [ite_eq_left ⟨hω, hl⟩, stopTime0Inf, cfArcRInf_zero_eq, ← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg s)]
    rw [e0] at hl
    exact ⟨fun h => ⟨by rw [← cfArcRInf_zero_eq]; exact hl, h⟩, fun h => h.2⟩
  · rw [ite_eq_right fun h => hl h.2]
    refine ⟨fun h => absurd h (by simp), fun h => absurd ?_ hl⟩
    rw [e0]
    have := h.1
    rwa [← cfArcRInf_zero_eq] at this

/-- **`{T ≤ σ}` is an event of `σ(X) ∨ 𝓕_σ`** (pocket opening at the flow seed). -/
theorem measurableSet_stopTimeMInf_le (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) (q : ℝ≥0) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
      {ω | stopTimeMInf A R L r η ψ q ω ≤ σ ω} := by
  classical
  set Ev : ℚ → Set ℝ → Set Ω := fun p B =>
    {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < StripSys.rt p} ∩
      (ratCap A R L r (adTrace W' ζ') ψ (StripSys.rt p)) ⁻¹' B with hEv
  have hEvm : ∀ p : ℚ, ∀ B : Set ℝ, MeasurableSet B →
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
        ({ω | StripSys.rt p < σ ω} ∩ Ev p B) := fun p B hB =>
    measurableSet_lt_inter_sup hσ _
      (measurableSet_ratCapInf_event h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hψ hψm (StripSys.rt p) hB)
  set Z : Set Ω := if q = 0 then univ else
    {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < σ ω} ∩ ⋂ n : ℕ, ⋃ p : ℚ, ⋃ (_ : (0 : ℝ) ≤ p),
      ({ω | StripSys.rt p < σ ω} ∩ Ev p (Ioi ((q : ℝ) - 1 / ((n : ℝ) + 1)))) with hZ
  have e : {ω | stopTimeMInf A R L r η ψ q ω ≤ σ ω} =
      {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) ≤ σ ω} ∩ Z := by
    ext ω
    by_cases hω : ω ∈ A
    swap
    · have h1 : ¬ stopTimeMInf A R L r η ψ q ω ≤ σ ω := by
        unfold stopTimeMInf
        rw [ite_eq_right fun h => hω h.1]
        simp
      simp only [mem_ofPred_eq, h1, mem_inter_iff, hω, false_and]
    have hP := (hcfg ω hω).toPocketInf (hψ ω hω)
    rw [cfArcRInf_zero_eq] at hP
    have hτ0 : 0 ≤ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) := hP.erase.nonneg
    simp only [mem_ofPred_eq, mem_inter_iff]
    rw [stopTimeMInf_le_iff hcfg hψ q hω (σ ω)]
    simp only [hω, true_and]
    have hρ : ∀ p : ℚ, firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < p →
        ratCap A R L r (adTrace W' ζ') ψ (StripSys.rt p) ω =
          relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (ψ ω) p :=
      fun p h1 => by rw [rt_coe (hτ0.trans h1.le), relCapInf_eq_ratCap hcfg hζA hψ hω h1.le]
    refine and_congr_right fun hτσ => ?_
    rw [hZ]
    split_ifs with hq
    · rw [hq, NNReal.coe_zero]
      exact ⟨fun _ => mem_univ ω, fun _ => hP.driven.capClock_nonneg (relTimeInf_nonneg hP hτσ)⟩
    · simp only [mem_inter_iff, mem_ofPred_eq, hω, true_and, mem_iInter, mem_iUnion, exists_prop, hEv,
        mem_preimage, mem_Ioi]
      constructor
      · intro hqc
        have hτσ' : firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < σ ω := by
          refine lt_of_le_of_ne hτσ fun h => ?_
          rw [← h, relCapInf_τ hP] at hqc
          exact hq (le_antisymm (by exact_mod_cast hqc) bot_le)
        have hrat := (le_relCapInf_iff_rat hP hτσ').1 hqc
        refine ⟨hτσ', fun n => ?_⟩
        obtain ⟨p, hp1, hp2, hp3⟩ := hrat n
        have hp0 : (0 : ℝ) ≤ p := hτ0.trans hp1.le
        refine ⟨p, hp0, ?_, by rw [rt_coe hp0]; exact hp1, ?_⟩
        · rw [← NNReal.coe_lt_coe, rt_coe hp0]; exact hp2
        · rw [hρ p hp1]; exact hp3
      · rintro ⟨hτσ', hall⟩
        refine (le_relCapInf_iff_rat hP hτσ').2 fun n => ?_
        obtain ⟨p, hp0, hpσ, hp1, hp3⟩ := hall n
        rw [rt_coe hp0] at hp1
        have hpσ' : (p : ℝ) < σ ω := by rw [← NNReal.coe_lt_coe, rt_coe hp0] at hpσ; exact hpσ
        refine ⟨p, hp1, hpσ', ?_⟩
        rw [← hρ p hp1]
        exact hp3
  rw [e]
  refine (measurableSet_firstHitInf_le_stopping h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hσ).inter ?_
  rw [hZ]
  split_ifs
  · exact MeasurableSet.univ
  · exact (measurableSet_firstHitInf_lt_stopping h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hσ).inter
      (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ =>
        hEvm p _ measurableSet_Ioi)

/-- **The marked prefix generators on `{T ≤ σ}`** (pocket opening at the flow seed). -/
theorem measurableSet_stopTimeMInf_le_inter_prefix (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) {q r' : ℝ≥0} (hr' : r' ≤ q) (n : ℕ) (k : ℤ × ℤ)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
      ({ω | stopTimeMInf A R L r η ψ q ω ≤ σ ω} ∩ (A ∩ prefixEvent (travAllInf R L r η ψ) r' n k)) := by
  classical
  have hD := measurableSet_stopTimeMInf_le h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hψ hψm q hσ
  have hlive : ∀ ω, stopTimeMInf A R L r η ψ q ω ≤ σ ω → ω ∈ A ∧
      (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧ stopTime0Inf R L r η ψ q ω ≤ σ ω := fun ω h => by
    unfold stopTimeMInf at h
    by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)
    · rw [ite_eq_left hl] at h
      exact ⟨hl.1, hl.2, h⟩
    · rw [ite_eq_right hl] at h
      simp at h
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ r' from bot_le) with hr0 | hr0
  · have e : {ω | stopTimeMInf A R L r η ψ q ω ≤ σ ω} ∩ (A ∩ prefixEvent (travAllInf R L r η ψ) r' n k) =
        {ω | stopTimeMInf A R L r η ψ q ω ≤ σ ω} ∩ {_ω | (0 : ℂ) ∈ Restart.dyadicSquare n k} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      refine and_congr_right fun hle => ?_
      obtain ⟨hω, hl, -⟩ := hlive ω hle
      have hγ := (hcfg ω hω).props (hψ ω hω)
      have hl' : (r' : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) :=
        lt_of_le_of_lt (by exact_mod_cast hr') hl
      have hci : capInv (travAllInf R L r η ψ ω) r' = 0 := hγ.1.capInv_of_nonpos (by rw [← hr0]; simp)
      simp only [prefixEvent, mem_ofPred_eq, hω, hl', true_and, hci, Icc_self, image_singleton]
      change ((Restart.dyadicSquare n k ∩ {cfTraversalInf (R ω) (L ω) r (η ω) (ψ ω) 0}).Nonempty ↔ _)
      rw [hγ.1.zero]
      exact ⟨fun ⟨z, hz, hz0⟩ => hz0 ▸ hz, fun h => ⟨0, h, rfl⟩⟩
    rw [e]
    exact hD.inter (MeasurableSet.const _)
  · have hr0' : (0 : ℝ) < r' := by exact_mod_cast hr0
    set V : ℕ → ℚ → Set Ω := fun m p =>
      {ω | ω ∈ A ∧ adTrace W' ζ' ω (StripSys.rt p) ∈ cfPocket (R ω) (L ω) r} ∩
        (ratCap A R L r (adTrace W' ζ') ψ (StripSys.rt p)) ⁻¹' Iio (r' : ℝ) ∩
        (visPt A R L r (adTrace W' ζ') ψ (StripSys.rt p)) ⁻¹'
          thickening (1 / ((m : ℝ) + 1)) (Restart.dyadicSquare n k) with hV
    have hVm : ∀ m p, MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 (StripSys.rt p)] (V m p) :=
      fun m p => by
        have h𝓦p := le_sup_of_le_zero h𝓦 (StripSys.rt p)
        have hem := measurable_adTrace_sup (X := X) hWad (le_refl ((StripSys.rt p : ℝ≥0) : ℝ))
        refine ((measurableSet_visit (mΩ := MeasurableSpace.comap X inferInstance ⊔ 𝓕 (StripSys.rt p)) h𝓦p hRm
          hLm hGm hG (h𝓦p _ hA) hAG hem).inter ?_).inter ?_
        · exact measurable_ratCapInf (mΩ := MeasurableSpace.comap X inferInstance ⊔ 𝓕 (StripSys.rt p)) h𝓦p hRm hLm
            hGm hG (h𝓦p _ hA) hAG (fun ω hω => (hψ ω hω).1) hψm
            (fun u' _ hu' => measurable_adTrace_sup hWad hu') measurableSet_Iio
        · exact measurable_visPtInf (mΩ := MeasurableSpace.comap X inferInstance ⊔ 𝓕 (StripSys.rt p)) h𝓦p hRm hLm
            hGm hG (h𝓦p _ hA) hAG (fun ω hω => (hψ ω hω).1) hψm hem isOpen_thickening.measurableSet
    have e : {ω | stopTimeMInf A R L r η ψ q ω ≤ σ ω} ∩ (A ∩ prefixEvent (travAllInf R L r η ψ) r' n k) =
        {ω | stopTimeMInf A R L r η ψ q ω ≤ σ ω} ∩
          ⋂ m : ℕ, ⋃ p : ℚ, ⋃ (_ : (0 : ℝ) ≤ p), ({ω | StripSys.rt p < σ ω} ∩ V m p) := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop]
      refine and_congr_right fun hle => ?_
      obtain ⟨hω, hl, hT⟩ := hlive ω hle
      have hc := hcfg ω hω
      have hP := hc.toPocketInf (hψ ω hω)
      have hl' : (r' : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) := lt_of_le_of_lt (by exact_mod_cast hr') hl
      have hlR : ENNReal.ofReal (r' : ℝ) < capLife (travInf (η ω) (cfPocket (R ω) (L ω) r)
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) := by
        rw [ENNReal.ofReal_coe_nnreal]; exact hl'
      have hqR : ENNReal.ofReal (q : ℝ) < capLife (travInf (η ω) (cfPocket (R ω) (L ω) r)
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) := by
        rw [ENNReal.ofReal_coe_nnreal]; exact hl
      have hT' : ambTime0Inf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) q ≤
          σ ω := by
        have : ENNReal.ofReal (ambTime0Inf (η ω) (cfPocket (R ω) (L ω) r)
            (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) q) ≤ ENNReal.ofReal (σ ω) := by
          rw [ENNReal.ofReal_coe_nnreal]; exact hT
        exact (ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg _)).1 this
      have hvis : ∀ p : ℚ, (0 : ℝ) ≤ p → η ω p ∈ cfPocket (R ω) (L ω) r →
          firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ p := fun p hp0 hpC =>
        (hP.erase.mem_visitSet hp0 hpC).1.le
      have hρ : ∀ p : ℚ, (0 : ℝ) ≤ p → η ω p ∈ cfPocket (R ω) (L ω) r →
          relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) p =
            ratCap A R L r (adTrace W' ζ') ψ p ω := fun p hp0 hpC => by
        have := relCapInf_eq_ratCap hcfg hζA hψ hω (p := p) (by rw [← cfArcRInf_zero_eq]; exact hvis p hp0 hpC)
        rwa [← cfArcRInf_zero_eq] at this
      simp only [prefixEvent, mem_ofPred_eq, hω, hl', true_and]
      change (Restart.dyadicSquare n k ∩ travInf (η ω) (cfPocket (R ω) (L ω) r)
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) '' Icc 0 (capInv (travInf (η ω) (cfPocket (R ω) (L ω) r)
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) r')).Nonempty ↔ _
      rw [prefix_nonempty_iff_visitInf hP hr0' hlR (Restart.isClosed_dyadicSquare n k)]
      refine forall_congr' fun m => ?_
      rw [exists_visitInf_iff_rat hP isOpen_thickening]
      constructor
      · rintro ⟨p, hp0, hpC, hpr, hpS⟩
        have hpI := hvis p hp0 hpC
        have he := adTrace_eq_of_memInf hcfg hζA hω (show (0 : ℝ) ≤ (StripSys.rt p : ℝ) from NNReal.coe_nonneg _)
        rw [rt_coe hp0] at he
        have hpT : (p : ℝ) < σ ω := by
          refine lt_of_lt_of_le (lt_of_not_ge fun h => ?_) hT'
          have := (ambTime0Inf_le_iff hP (NNReal.coe_nonneg q) hqR hpI).1 h
          linarith [(show (r' : ℝ) ≤ q from hr')]
        refine ⟨p, hp0, by rw [← NNReal.coe_lt_coe, rt_coe hp0]; exact hpT, ?_⟩
        simp only [hV, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Iio, rt_coe hp0, he, hω, hpC, and_self,
          true_and]
        refine ⟨by rw [← hρ p hp0 hpC]; exact hpr, ?_⟩
        rw [visPt, ite_eq_left ⟨hω, he ▸ hpC⟩, he]
        exact hpS
      · rintro ⟨p, hp0, -, hpV⟩
        simp only [hV, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Iio, rt_coe hp0] at hpV
        obtain ⟨⟨⟨-, hpC⟩, hpr⟩, hpS⟩ := hpV
        have he := adTrace_eq_of_memInf hcfg hζA hω (show (0 : ℝ) ≤ (StripSys.rt p : ℝ) from NNReal.coe_nonneg _)
        rw [rt_coe hp0] at he
        rw [he] at hpC
        refine ⟨p, hp0, hpC, by rw [hρ p hp0 hpC]; exact hpr, ?_⟩
        rw [visPt, ite_eq_left ⟨hω, he ▸ hpC⟩, he] at hpS
        exact hpS
    rw [e]
    exact hD.inter (MeasurableSet.iInter fun m => MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ =>
      measurableSet_lt_inter_sup hσ _ (hVm m p))

/-- **`IsMarkedStop` for the marked stop** (pocket opening at the flow seed). -/
theorem isMarkedStop_stopTimeMInf (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) (q : ℝ≥0) :
    IsMarkedStop (locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q) 𝓕 X (stopTimeMInf A R L r η ψ q) := by
  intro σ hσ M hM
  have hD := measurableSet_stopTimeMInf_le h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hψ hψm q hσ
  have hle : locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q ≤
      traceSigma (MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace) _ hD := by
    refine sup_le (fun M hM => hD.inter (measurableSet_sup_of_zero hσ (h𝓦 _ hM)))
      (MeasurableSpace.generateFrom_le ?_)
    rintro _ ⟨r', hr', n, k, rfl⟩
    exact measurableSet_stopTimeMInf_le_inter_prefix h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hψ hψm hr' n k hσ
  exact hle M hM

/-- **The marks are events of `σ(X) ∨ 𝓕_∞`** (`hS0`, pocket opening at the flow seed). -/
theorem measurableSet_sup_iSup_of_locPrefixSigmaInf (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) (q : ℝ≥0) (M : Set Ω)
    (hM : MeasurableSet[locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q] M) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ⨆ t, 𝓕 t] M := by
  classical
  have hmono : ∀ t, MeasurableSpace.comap X inferInstance ⊔ 𝓕 t ≤
      MeasurableSpace.comap X inferInstance ⊔ ⨆ t, 𝓕 t := fun t => sup_le_sup_left (le_iSup (fun t => 𝓕 t) t) _
  refine (sup_le ((h𝓦.trans (hmono 0))) (MeasurableSpace.generateFrom_le ?_)) M hM
  rintro _ ⟨r', -, n, k, rfl⟩
  have e : A ∩ prefixEvent (travAllInf R L r η ψ) r' n k =
      ⋃ N : ℕ, ({ω | stopTimeMInf A R L r η ψ r' ω ≤ ((N : ℝ≥0) : ℝ≥0∞)} ∩
        (A ∩ prefixEvent (travAllInf R L r η ψ) r' n k)) := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hω, hpre⟩
      have hl : (r' : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) := hpre.1
      have hfin : stopTimeMInf A R L r η ψ r' ω ≠ ⊤ := by
        unfold stopTimeMInf
        rw [ite_eq_left ⟨hω, hl⟩]
        exact ENNReal.ofReal_ne_top
      obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hfin
      exact ⟨N, by rw [ENNReal.coe_natCast]; exact hN.le, hω, hpre⟩
    · rintro ⟨N, -, h⟩
      exact h
  rw [e]
  refine MeasurableSet.iUnion fun N => ?_
  have hc := isStoppingTime_const 𝓕 (N : ℝ≥0)
  have h := measurableSet_stopTimeMInf_le_inter_prefix h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hψ hψm
    (le_refl r') n k (σ := fun _ => (N : ℝ≥0)) hc
  rw [IsStoppingTime.measurableSpace_const] at h
  exact hmono _ _ h

end StopInf

section LawInf

variable {Ω : Type*}

open WholeField PocketStopField PocketStopWalls PocketMarks PocketUnionPt PocketStop

/-! ### The change pocket opening at the flow seed -/

/-- **`PocketStopWallsLaw` at the left end `T⁰(q)` for the change pocket opening at the flow seed, without stop
inputs** (Aux. lemma 35's marked union law of the walls with the counterflow hull, rulings R67–R68):
PROVE-STRIPSYS41's `pocketStopWallsLaw_stopHull0Inf` with the stop `T⁰(q)` taken on the live event
(`stopTimeMInf`), whose Galmarino property (`isMarkedStop_stopTimeMInf`) and `hS0`
(`measurableSet_sup_iSup_of_locPrefixSigmaInf`) are proved from the configuration, the Jordan coordinate's point
measurability and `𝓦 ≤ σ(fullHist ![R, L]) ∨ 𝓕_0`. -/
theorem pocketStopWallsLaw_stopHull0Inf_marked
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (h𝓦 : 𝓦 ≤ MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX 0)
    (hRm' : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm' : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hGm : MeasurableSet[𝓦] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A)
    (hAG : A ⊆ G) (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) (q : ℝ≥0) :
    PocketStopWallsLaw 𝓦 P A (travAllInf R L r η ψ) (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (stopHull0Inf R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q) (centredField h'' u₀') q := by
  classical
  have hc2 : ∀ i ω, Continuous ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := Fin.forall_fin_two.2 ⟨hRc, hLc⟩
  have h02 : ∀ i ω, (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω 0 = (0 : Fin 2 → ℂ) i :=
    Fin.forall_fin_two.2 ⟨hR0, hL0⟩
  have hm2 : ∀ i t, Measurable fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t := Fin.forall_fin_two.2 ⟨hRm, hLm⟩
  have hdet2 : ∀ i t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω) :=
    Fin.forall_fin_two.2 ⟨hdetR, hdetL⟩
  have hloc2 : ∀ i, Sec6.IsEntranceHistoryLocal ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i) (centredField h u₀) P :=
    Fin.forall_fin_two.2 ⟨hlocR, hlocL⟩
  have hΓe : (fun ω => negInv '' (range (R ω) ∪ range (L ω))) =
      fun ω => negInv '' ⋃ i, range ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := funext fun ω => by
    rw [iUnion_range_fin_two]
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  rw [hΓe]
  refine pocketStopWallsLaw_regHull (T := stopTimeMInf A R L r η ψ q) hC hκ' hu₀' hX hζ (measurable_fullHist hm2)
    (measurable_negInv_walls hc2 hm2)
    (fun U G hUH hG hd B hB => walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc2 h02 hm2 hdet2 hloc2 U G hUH hG hd B hB)
    (fun ω hω hl => ?_)
    (isMarkedStop_stopTimeMInf h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q)
    (measurableSet_sup_iSup_of_locPrefixSigmaInf h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q)
  have hT : stopTimeMInf A R L r η ψ q ω = stopTime0Inf R L r η ψ q ω := by
    unfold stopTimeMInf
    exact ite_eq_left ⟨hω, hl⟩
  rw [hT]
  exact ⟨ENNReal.ofReal_lt_top, stopHull0Inf_eq_regHull' (hcfg ω hω) (hζA ω hω) q⟩

end LawInf

end InteractingSLE.Sec7.PocketStopMarked.Outer
