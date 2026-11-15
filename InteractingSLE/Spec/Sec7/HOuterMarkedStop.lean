/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.HOuterMarkedPath

/-!
# The outer pocket's stop `T⁰(q)` is a marked stop; the walls' marked union law at `T⁰(q)`

Packet PROVE-HOUTER. The port of PROVE-STRIPSYS43's `PocketStopMarkedStop.lean` (the Galmarino property of the marked
stop `stopTimeM` and the marks' measurability `hS0`) and of `pocketStopWallsLaw_stopHull0_marked`
(`PocketStopMarkedLaw.lean`) from the contained change pocket (`IsCfPocketConfig`) to a mixed or outer change pocket
(`HOuter.IsOuterCfg`): Aux. lemma 35's marked stopping-time union law of the walls with the counterflow hull at the left
fibre end `T⁰(q)` (ruling R67) holds for the outer pocket with no stop input. The proofs are STRIPSYS43's with the
pathwise facts of `HOuterMarkedPath` (`IsOuterPocket`) in place of the reverse-pocket ones; the first visit of `m(y₀)`
is a first visit by `PocketJordan.firstHit_spec`.

* `HOuter.IsOuterCfg.toPocket`, `firstHit_first`, `stopHull0_eq_regHull'`;
* `measurableSet_stopTimeM_le`, `measurableSet_stopTimeM_le_inter_prefix`, **`isMarkedStop_stopTimeM`**,
  **`measurableSet_sup_iSup_of_locPrefixSigma`** (ports);
* **`pocketStopWallsLaw_stopHull0_marked`** (port): `PocketStopWallsLaw` at `T⁰(q)` for the outer pocket.

Declarations in the sub-namespace `PocketStopMarked.Outer` (see `HOuterMarkedPath`). Ruling R48: nothing here uses
Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopMarked.Outer

open QuantumZipper (H)
open PocketCoord PocketJordan PocketWordAssembly PocketStopWallsFin PocketCoupling Lemma71C Lemma71I PocketAdapt
  PocketTraversal

/-! ### One realization of an outer configuration as an outer pocket -/

/-- **An outer configuration with a Jordan coordinate is an `IsOuterPocket`** (the driven traversal from the relative
Loewner conclusion). -/
theorem _root_.InteractingSLE.Sec7.HOuter.IsOuterCfg.toPocket {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hc : HOuter.IsOuterCfg R L r W η) {ψ : ℂ → ℂ} (hψ : IsCfJordan R L r ψ) :
    IsOuterPocket W η (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) ψ :=
  ⟨hc.erase, hc.trace, PocketJordan.image_negInv_subset_H hc.conf.changePocket_subset_H, isJordanCoord_of_cf hψ,
    (hc.props hψ).1⟩

/-- **`hT` for `T⁰(q)`** (outer pocket; `PocketStopWallsFin.stopHull0_eq_regHull`): on a configuration whose driver is
continuous with infinite lifetime, `stopHull0 = K̃_{T⁰(q)}`. -/
theorem stopHull0_eq_regHull' {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ω : Ω}
    (hc : HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω)) (hζ : ζ' ω = ⊤) (q : ℝ≥0) :
    stopHull0 R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q ω =
      regHull W' ζ' (stopTime0 R L r η ψ q ω).toNNReal ω := by
  have h0 : 0 ≤ ambTime0 (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) q :=
    hc.erase.nonneg.trans (fibreLeft_mem hc.erase.continuous_clock hc.erase.lt.le _).1
  rw [regHull_eq (continuous_nnreal_of_continuous_real hc.continuous_W) hζ, stopTime0,
    ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal h0]
  rfl

/-! ### The marked stop and its pathwise description -/

section Path

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ} {ψ : ℂ → ℂ}

/-- **The live marked stop before `s`** (one realization): `q < capLife γ ∧ T⁰(q) ≤ s` iff `τ ≤ s < S ∧ q ≤ c(s)` or
`S ≤ s ∧ q < c(p)` for some rational `p ∈ (τ, S)`. -/
theorem cf_live_le_iff (hc : HOuter.IsOuterCfg R L r W η) (hψ : IsCfJordan R L r ψ) (q s : ℝ≥0) :
    ((q : ℝ≥0∞) < capLife (cfTraversal R L r η ψ) ∧
        ENNReal.ofReal (ambTime0 η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) ψ q) ≤
          (s : ℝ≥0∞)) ↔
      (firstHit η (cfArcR R L r 1) ≤ s ∧ (s : ℝ) < firstHit η (cfArcR R L r 0) ∧
          (q : ℝ) ≤ relCap η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) ψ s) ∨
        (firstHit η (cfArcR R L r 0) ≤ s ∧ ∃ p : ℚ, firstHit η (cfArcR R L r 1) < p ∧
          (p : ℝ) < firstHit η (cfArcR R L r 0) ∧
          (q : ℝ) < relCap η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) ψ p) := by
  have hP := hc.toPocket hψ
  have e1 : ENNReal.ofReal (ambTime0 η (cfPocket R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) ψ q) ≤ (s : ℝ≥0∞) ↔
      ambTime0 η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) ψ q ≤ s := by
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg s)]
  have e0 : (q : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
  rw [e1, e0]
  have h := live_and_ambTime0_le_iff hP (NNReal.coe_nonneg q) (s : ℝ)
  rw [exists_relCap_gt_iff_rat hP] at h
  exact h

end Path

/-! ### Fixed-time and stopping-time events of the strip pocket -/

section Meas

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳] {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {𝓕 : Filtration ℝ≥0 mΩ} {X : Ω → 𝒳} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {G A : Set Ω} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}

omit mΩ in
theorem adTrace_eq_of_mem (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {ω : Ω} (hω : ω ∈ A) {u : ℝ} (hu : 0 ≤ u) : adTrace W' ζ' ω u = η ω u := by
  have hc := hcfg ω hω
  have h0 : W' 0 ω = 0 := by simpa using hc.W_zero
  exact adTrace_eq hc.trace hc.continuous_W h0 (hζA ω hω) hu

omit mΩ in
theorem continuousOn_adTrace (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {ω : Ω} (hω : ω ∈ A) : ContinuousOn (adTrace W' ζ' ω) (Ici 0) :=
  (hcfg ω hω).trace.2.1.congr fun _ hu => adTrace_eq_of_mem hcfg hζA hω hu

/-- The first visits of `m(y₀)` (`c = 1`) and `m(x₀)` (`c = 0`) are first visit times. -/
theorem firstHit_first {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ} (hc : HOuter.IsOuterCfg R L r W η)
    {c : ℝ} (hc01 : c = 0 ∨ c = 1) :
    0 ≤ firstHit η (cfArcR R L r c) ∧ η (firstHit η (cfArcR R L r c)) = cfArcR R L r c ∧
      cfArcR R L r c ∉ η '' Ico 0 (firstHit η (cfArcR R L r c)) := by
  rcases hc01 with rfl | rfl
  · exact ⟨hc.erase.nonneg_σ, hc.erase.first_x, hc.erase.fresh_x⟩
  · exact PocketJordan.firstHit_spec hc.erase.cont
      ⟨firstHit η (cfArcR R L r 1), firstHit η (cfArcR R L r 1), ⟨hc.erase.nonneg, le_rfl⟩, hc.erase.first_y⟩

/-- **The first visit of a pocket corner by time `u`** is an event of `σ(X) ∨ 𝓕_u` on `A`. -/
theorem measurableSet_firstHit_le (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {c : ℝ} (hc01 : c = 0 ∨ c = 1) (u : ℝ≥0) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 u]
      {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r c) ≤ u} := by
  have hc : c ∈ Icc (0 : ℝ) 1 := by rcases hc01 with rfl | rfl <;> norm_num
  have h𝓦u := le_sup_of_le_zero h𝓦 u
  have e : {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r c) ≤ u} =
      {ω | ω ∈ A ∧ cfArcR (R ω) (L ω) r c ∈ adTrace W' ζ' ω '' Icc 0 u} := by
    ext ω
    simp only [mem_ofPred_eq]
    refine and_congr_right fun hω => ?_
    obtain ⟨h0, h1, h2⟩ := firstHit_first (hcfg ω hω) hc01
    rw [le_iff_mem_image_of_first h0 h1 h2]
    rw [image_congr fun t ht => adTrace_eq_of_mem hcfg hζA hω ht.1]
  rw [e]
  exact measurableSet_mem_arc_image (mΩ := MeasurableSpace.comap X inferInstance ⊔ 𝓕 u) h𝓦u hRm hLm hGm hG
    (h𝓦u _ hA) hAG (fun ω hω => continuousOn_adTrace hcfg hζA hω) (NNReal.coe_nonneg u)
    (fun u' _ hu' => measurable_adTrace_sup hWad hu') hc

/-- **The first visit of a pocket corner strictly before time `u`** is an event of `σ(X) ∨ 𝓕_u` on `A`. -/
theorem measurableSet_firstHit_lt (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {c : ℝ} (hc01 : c = 0 ∨ c = 1) (u : ℝ≥0) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 u]
      {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r c) < u} := by
  have e : {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r c) < u} =
      ⋃ q : ℚ, ⋃ (_ : StripSys.rt q < u), {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r c) ≤ StripSys.rt q} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hω, hlt⟩
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have h0 := (firstHit_first (hcfg ω hω) hc01).1
      have hq0 : (0 : ℝ) ≤ q := h0.trans hq1.le
      refine ⟨q, ?_, hω, ?_⟩
      · rw [← NNReal.coe_lt_coe, StripSys.rt, Real.coe_toNNReal _ hq0]
        exact hq2
      · rw [StripSys.rt, Real.coe_toNNReal _ hq0]
        exact hq1.le
    · rintro ⟨q, hq, hω, hle⟩
      exact ⟨hω, hle.trans_lt (by exact_mod_cast hq)⟩
  rw [e]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  exact (sup_le_sup_left (𝓕.mono hq.le) _) _
    (measurableSet_firstHit_le h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hc01 (StripSys.rt q))

/-- **The first visit of a pocket corner by a stopping time `σ`** is an event of `σ(X) ∨ 𝓕_σ` on `A`. -/
theorem measurableSet_firstHit_le_stopping (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {c : ℝ} (hc01 : c = 0 ∨ c = 1) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
      {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r c) ≤ σ ω} := by
  have hc : c ∈ Icc (0 : ℝ) 1 := by rcases hc01 with rfl | rfl <;> norm_num
  have e : {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r c) ≤ σ ω} = A ∩ ⋂ n : ℕ, ⋃ q : ℚ, ⋃ (_ : 0 ≤ q),
      ({ω | StripSys.rt q ≤ σ ω} ∩ {ω | ω ∈ A ∧ dist (cfArcR (R ω) (L ω) r c) (adTrace W' ζ' ω (StripSys.rt q)) <
        1 / ((n : ℝ) + 1)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hω, hle⟩
      obtain ⟨h0, h1, h2⟩ := firstHit_first (hcfg ω hω) hc01
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
      · rw [adTrace_eq_of_mem hcfg hζA hω (NNReal.coe_nonneg _)]
        simpa using hd
    · rintro ⟨hω, h⟩
      obtain ⟨h0, h1, h2⟩ := firstHit_first (hcfg ω hω) hc01
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
      · rw [adTrace_eq_of_mem hcfg hζA hω (NNReal.coe_nonneg _)] at hd
        simpa using hd
  rw [e]
  refine (measurableSet_sup_of_zero hσ (h𝓦 _ hA)).inter (MeasurableSet.iInter fun n =>
    MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => ?_)
  have h𝓦q := le_sup_of_le_zero h𝓦 (StripSys.rt q)
  exact measurableSet_le_inter_sup hσ (StripSys.rt q)
    (measurableSet_arc_dist_lt (mΩ := MeasurableSpace.comap X inferInstance ⊔ 𝓕 (StripSys.rt q)) h𝓦q hRm hLm hGm
      hG (h𝓦q _ hA) hAG (measurable_adTrace_sup hWad le_rfl) hc _)

omit mΩ in
/-- **The relative capacity at `p ∈ [τ, S)` is the measurable `ratCap`** of the adapted trace (on `A`). -/
theorem relCap_eq_ratCap (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) {ω : Ω} (hω : ω ∈ A) {p : ℝ}
    (hp : p ∈ Ico (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))) :
    relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) p = ratCap A R L r (adTrace W' ζ') ψ p ω := by
  classical
  rw [relCap_eq_hcapHit_rat ((hcfg ω hω).toPocket (hψ ω hω)) hp, ratCap]
  have hfun : (fun p' : ℚ => if 0 ≤ (p' : ℝ) ∧ (p' : ℝ) ≤ p ∧ η ω p' ∈ cfPocket (R ω) (L ω) r then
      ψ ω (η ω p') else 0) =
      fun p' : ℚ => if 0 ≤ (p' : ℝ) ∧ (p' : ℝ) ≤ p then visPt A R L r (adTrace W' ζ') ψ p' ω else 0 := by
    funext p'
    by_cases h1 : 0 ≤ (p' : ℝ) ∧ (p' : ℝ) ≤ p
    · have he := adTrace_eq_of_mem hcfg hζA hω h1.1
      by_cases h2 : η ω p' ∈ cfPocket (R ω) (L ω) r
      · rw [ite_eq_left ⟨h1.1, h1.2, h2⟩, ite_eq_left h1, visPt, ite_eq_left ⟨hω, he ▸ h2⟩, he]
      · rw [ite_eq_right fun h => h2 h.2.2, ite_eq_left h1, visPt,
          ite_eq_right fun (h : ω ∈ A ∧ adTrace W' ζ' ω p' ∈ cfPocket (R ω) (L ω) r) => h2 (he ▸ h.2)]
    · rw [ite_eq_right fun (h : 0 ≤ (p' : ℝ) ∧ (p' : ℝ) ≤ p ∧ η ω p' ∈ cfPocket (R ω) (L ω) r) => h1 ⟨h.1, h.2.1⟩,
        ite_eq_right h1]
  rw [hfun]

/-- **The relative-capacity event at a rational time** (`τ < p < S`, `ratCap p ∈ B`) is an event of `σ(X) ∨ 𝓕_p`. -/
theorem measurableSet_ratCap_event (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) (p : ℝ≥0) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 p]
      ({ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < p} \
          {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 0) ≤ p} ∩
        (ratCap A R L r (adTrace W' ζ') ψ p) ⁻¹' B) := by
  have h𝓦p := le_sup_of_le_zero h𝓦 p
  refine ((measurableSet_firstHit_lt h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA (Or.inr rfl) p).diff
    (measurableSet_firstHit_le h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA (Or.inl rfl) p)).inter ?_
  exact measurable_ratCap (mΩ := MeasurableSpace.comap X inferInstance ⊔ 𝓕 p) h𝓦p hRm hLm hGm hG (h𝓦p _ hA) hAG
    (fun ω hω => (hψ ω hω).1) hψm (fun u' _ hu' => measurable_adTrace_sup hWad hu') hB

/-- **The first visit of `m(y₀)` strictly before a stopping time `σ`** is an event of `σ(X) ∨ 𝓕_σ` on `A`. -/
theorem measurableSet_firstHit_lt_stopping (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {c : ℝ} (hc01 : c = 0 ∨ c = 1) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
      {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r c) < σ ω} := by
  have e : {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r c) < σ ω} = ⋃ q : ℚ, ⋃ (_ : (0 : ℝ) ≤ q),
      ({ω | StripSys.rt q < σ ω} ∩ {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r c) ≤ StripSys.rt q}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨hω, hlt⟩
      have h0 := (firstHit_first (hcfg ω hω) hc01).1
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have hq0 : (0 : ℝ) ≤ q := h0.trans hq1.le
      refine ⟨q, hq0, ?_, hω, by rw [rt_coe hq0]; exact hq1.le⟩
      rw [← NNReal.coe_lt_coe, rt_coe hq0]
      exact hq2
    · rintro ⟨q, hq0, hqσ, hω, hle⟩
      exact ⟨hω, hle.trans_lt (by exact_mod_cast hqσ)⟩
  rw [e]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    measurableSet_lt_inter_sup hσ _ (measurableSet_firstHit_le h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hc01 _)

omit mΩ in
/-- **The marked stop before `s`** (pathwise, on `A`). -/
theorem stopTimeM_le_iff (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (q : ℝ≥0) {ω : Ω} (hω : ω ∈ A) (s : ℝ≥0) :
    stopTimeM A R L r η ψ q ω ≤ s ↔
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1) ≤ s ∧ (s : ℝ) < firstHit (η ω) (cfArcR (R ω) (L ω) r 0) ∧
          (q : ℝ) ≤ relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
            (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) s) ∨
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0) ≤ s ∧ ∃ p : ℚ, firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < p ∧
          (p : ℝ) < firstHit (η ω) (cfArcR (R ω) (L ω) r 0) ∧
          (q : ℝ) < relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
            (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) p) := by
  classical
  rw [← cf_live_le_iff (hcfg ω hω) (hψ ω hω) q s]
  unfold stopTimeM
  by_cases hl : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)
  · rw [ite_eq_left ⟨hω, hl⟩]
    exact ⟨fun h => ⟨hl, h⟩, fun h => h.2⟩
  · rw [ite_eq_right fun h => hl h.2]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h.1 hl⟩

/-- **`{T ≤ σ}` is an event of `σ(X) ∨ 𝓕_σ`** for the marked stop of the bounded change pocket. -/
theorem measurableSet_stopTimeM_le (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) (q : ℝ≥0) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
      {ω | stopTimeM A R L r η ψ q ω ≤ σ ω} := by
  classical
  -- the relative-capacity events at rational times
  set Ev : ℚ → Set ℝ → Set Ω := fun p B =>
    ({ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < StripSys.rt p} \
        {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 0) ≤ StripSys.rt p}) ∩
      (ratCap A R L r (adTrace W' ζ') ψ (StripSys.rt p)) ⁻¹' B with hEv
  have hEvm : ∀ p : ℚ, ∀ B : Set ℝ, MeasurableSet B →
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
        ({ω | StripSys.rt p < σ ω} ∩ Ev p B) := fun p B hB =>
    measurableSet_lt_inter_sup hσ _
      (measurableSet_ratCap_event h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hψ hψm (StripSys.rt p) hB)
  set Z : Set Ω := if q = 0 then univ else
    {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < σ ω} ∩ ⋂ n : ℕ, ⋃ p : ℚ, ⋃ (_ : (0 : ℝ) ≤ p),
      ({ω | StripSys.rt p < σ ω} ∩ Ev p (Ioi ((q : ℝ) - 1 / ((n : ℝ) + 1)))) with hZ
  have e : {ω | stopTimeM A R L r η ψ q ω ≤ σ ω} =
      ({ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) ≤ σ ω} ∩
          {ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 0) ≤ σ ω}ᶜ ∩ Z) ∪
        ({ω | ω ∈ A ∧ firstHit (η ω) (cfArcR (R ω) (L ω) r 0) ≤ σ ω} ∩
          ⋃ p : ℚ, ⋃ (_ : (0 : ℝ) ≤ p), ({ω | StripSys.rt p < σ ω} ∩ Ev p (Ioi (q : ℝ)))) := by
    ext ω
    by_cases hω : ω ∈ A
    swap
    · have h1 : ¬ stopTimeM A R L r η ψ q ω ≤ σ ω := by
        unfold stopTimeM
        rw [ite_eq_right fun h => hω h.1]
        simp
      simp only [mem_ofPred_eq, h1, mem_union, mem_inter_iff, hω, false_and, or_self]
    have hP := (hcfg ω hω).toPocket (hψ ω hω)
    have hτ0 : 0 ≤ firstHit (η ω) (cfArcR (R ω) (L ω) r 1) := hP.erase.nonneg
    simp only [mem_ofPred_eq]
    rw [stopTimeM_le_iff hcfg hψ q hω (σ ω)]
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, hω, true_and, mem_iUnion, exists_prop,
      hEv, Set.mem_sdiff, mem_preimage, mem_Ioi]
    -- the relative capacity at rational times between `τ` and `S`
    have hρ : ∀ p : ℚ, firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < p →
        (p : ℝ) < firstHit (η ω) (cfArcR (R ω) (L ω) r 0) →
        ratCap A R L r (adTrace W' ζ') ψ (StripSys.rt p) ω =
          relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
            (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) p := fun p h1 h2 => by
      rw [rt_coe (hτ0.trans h1.le), relCap_eq_ratCap hcfg hζA hψ hω ⟨h1.le, h2⟩]
    refine or_congr ?_ ?_
    · -- the first alternative
      constructor
      · rintro ⟨hτσ, hσS, hqc⟩
        refine ⟨⟨hτσ, not_le.2 hσS⟩, ?_⟩
        rw [hZ]
        split_ifs with hq
        · exact mem_univ ω
        · have hτσ' : firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < σ ω := by
            refine lt_of_le_of_ne hτσ fun h => ?_
            rw [← h, relCap_τ hP] at hqc
            exact hq (le_antisymm (by exact_mod_cast hqc) bot_le)
          have hrat := (le_relCap_iff_rat hP ⟨hτσ', hσS⟩).1 hqc
          simp only [mem_inter_iff, mem_ofPred_eq, hω, true_and, mem_iInter, mem_iUnion, exists_prop, hEv,
            Set.mem_sdiff, mem_preimage, mem_Ioi]
          refine ⟨hτσ', fun n => ?_⟩
          obtain ⟨p, hp1, hp2, hp3⟩ := hrat n
          have hp0 : (0 : ℝ) ≤ p := hτ0.trans hp1.le
          refine ⟨p, hp0, ?_, ⟨by rw [rt_coe hp0]; exact hp1, fun h => ?_⟩, ?_⟩
          · rw [← NNReal.coe_lt_coe, rt_coe hp0]; exact hp2
          · rw [rt_coe hp0] at h; linarith [h]
          · rw [hρ p hp1 (hp2.trans hσS)]; exact hp3
      · rintro ⟨⟨hτσ, hSσ⟩, hZω⟩
        have hσS : (σ ω : ℝ) < firstHit (η ω) (cfArcR (R ω) (L ω) r 0) := not_le.1 hSσ
        refine ⟨hτσ, hσS, ?_⟩
        rw [hZ] at hZω
        split_ifs at hZω with hq
        · rw [hq, NNReal.coe_zero]
          exact hP.driven.capClock_nonneg (relTime_nonneg hP ⟨hτσ, hσS⟩)
        · simp only [mem_inter_iff, mem_ofPred_eq, hω, true_and, mem_iInter, mem_iUnion, exists_prop, hEv,
            Set.mem_sdiff, mem_preimage, mem_Ioi] at hZω
          obtain ⟨hτσ', hall⟩ := hZω
          refine (le_relCap_iff_rat hP ⟨hτσ', hσS⟩).2 fun n => ?_
          obtain ⟨p, hp0, hpσ, ⟨hp1, hp2⟩, hp3⟩ := hall n
          rw [rt_coe hp0] at hp1
          have hpσ' : (p : ℝ) < σ ω := by rw [← NNReal.coe_lt_coe, rt_coe hp0] at hpσ; exact hpσ
          refine ⟨p, hp1, hpσ', ?_⟩
          rw [← hρ p hp1 (hpσ'.trans hσS)]
          exact hp3
    · -- the second alternative
      refine and_congr_right fun hSσ => ?_
      constructor
      · rintro ⟨p, hp1, hp2, hp3⟩
        have hp0 : (0 : ℝ) ≤ p := hτ0.trans hp1.le
        refine ⟨p, hp0, ?_, ⟨by rw [rt_coe hp0]; exact hp1, fun h => ?_⟩, ?_⟩
        · rw [← NNReal.coe_lt_coe, rt_coe hp0]; exact hp2.trans_le hSσ
        · rw [rt_coe hp0] at h; linarith [h]
        · rw [hρ p hp1 hp2]; exact hp3
      · rintro ⟨p, hp0, -, ⟨hp1, hp2⟩, hp3⟩
        rw [rt_coe hp0] at hp1
        have hp2' : (p : ℝ) < firstHit (η ω) (cfArcR (R ω) (L ω) r 0) := by
          by_contra h
          exact hp2 (by rw [rt_coe hp0]; exact not_lt.1 h)
        refine ⟨p, hp1, hp2', ?_⟩
        rw [← hρ p hp1 hp2']
        exact hp3
  rw [e]
  have hτσ := measurableSet_firstHit_le_stopping h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA (Or.inr rfl) hσ
  have hSσ := measurableSet_firstHit_le_stopping h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA (Or.inl rfl) hσ
  refine MeasurableSet.union ((hτσ.inter hSσ.compl).inter ?_)
    (hSσ.inter (MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ => hEvm p _ measurableSet_Ioi))
  rw [hZ]
  split_ifs
  · exact MeasurableSet.univ
  · exact (measurableSet_firstHit_lt_stopping h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA (Or.inr rfl) hσ).inter
      (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ =>
        hEvm p _ measurableSet_Ioi)

/-- **The marked prefix generators on `{T ≤ σ}`**: for `r' ≤ q`, `{T ≤ σ} ∩ A ∩ prefixEvent γ r' n k` is an event of
`σ(X) ∨ 𝓕_σ`. -/
theorem measurableSet_stopTimeM_le_inter_prefix (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) {q r' : ℝ≥0} (hr' : r' ≤ q) (n : ℕ) (k : ℤ × ℤ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
      ({ω | stopTimeM A R L r η ψ q ω ≤ σ ω} ∩ (A ∩ prefixEvent (travAll R L r η ψ) r' n k)) := by
  classical
  have hD := measurableSet_stopTimeM_le h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hψ hψm q hσ
  -- on `{T ≤ σ}`: `ω ∈ A`, the live event at `q`, and `T⁰(q) ≤ σ`
  have hlive : ∀ ω, stopTimeM A R L r η ψ q ω ≤ σ ω → ω ∈ A ∧
      (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧ stopTime0 R L r η ψ q ω ≤ σ ω := fun ω h => by
    unfold stopTimeM at h
    by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)
    · rw [ite_eq_left hl] at h
      exact ⟨hl.1, hl.2, h⟩
    · rw [ite_eq_right hl] at h
      simp at h
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ r' from bot_le) with hr0 | hr0
  · -- `r' = 0`: the prefix is the seed `0`
    have e : {ω | stopTimeM A R L r η ψ q ω ≤ σ ω} ∩ (A ∩ prefixEvent (travAll R L r η ψ) r' n k) =
        {ω | stopTimeM A R L r η ψ q ω ≤ σ ω} ∩ {_ω | (0 : ℂ) ∈ Restart.dyadicSquare n k} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      refine and_congr_right fun hle => ?_
      obtain ⟨hω, hl, -⟩ := hlive ω hle
      have hγ := (hcfg ω hω).props (hψ ω hω)
      have hl' : (r' : ℝ≥0∞) < capLife (travAll R L r η ψ ω) :=
        lt_of_le_of_lt (by exact_mod_cast hr') hl
      have hci : capInv (travAll R L r η ψ ω) r' = 0 := hγ.1.capInv_of_nonpos (by rw [← hr0]; simp)
      simp only [prefixEvent, mem_ofPred_eq, hω, hl', true_and, hci, Icc_self, image_singleton]
      change ((Restart.dyadicSquare n k ∩ {cfTraversal (R ω) (L ω) r (η ω) (ψ ω) 0}).Nonempty ↔ _)
      rw [hγ.1.zero]
      exact ⟨fun ⟨z, hz, hz0⟩ => hz0 ▸ hz, fun h => ⟨0, h, rfl⟩⟩
    rw [e]
    exact hD.inter (MeasurableSet.const _)
  · -- `r' > 0`: rational pocket visits before the stop
    have hr0' : (0 : ℝ) < r' := by exact_mod_cast hr0
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
        · exact measurable_ratCap (mΩ := MeasurableSpace.comap X inferInstance ⊔ 𝓕 (StripSys.rt p)) h𝓦p hRm hLm
            hGm hG (h𝓦p _ hA) hAG (fun ω hω => (hψ ω hω).1) hψm
            (fun u' _ hu' => measurable_adTrace_sup hWad hu') measurableSet_Iio
        · exact measurable_visPt (mΩ := MeasurableSpace.comap X inferInstance ⊔ 𝓕 (StripSys.rt p)) h𝓦p hRm hLm
            hGm hG (h𝓦p _ hA) hAG (fun ω hω => (hψ ω hω).1) hψm hem isOpen_thickening.measurableSet
    have e : {ω | stopTimeM A R L r η ψ q ω ≤ σ ω} ∩ (A ∩ prefixEvent (travAll R L r η ψ) r' n k) =
        {ω | stopTimeM A R L r η ψ q ω ≤ σ ω} ∩
          ⋂ m : ℕ, ⋃ p : ℚ, ⋃ (_ : (0 : ℝ) ≤ p), ({ω | StripSys.rt p < σ ω} ∩ V m p) := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop]
      refine and_congr_right fun hle => ?_
      obtain ⟨hω, hl, hT⟩ := hlive ω hle
      have hc := hcfg ω hω
      have hP := hc.toPocket (hψ ω hω)
      have hl' : (r' : ℝ≥0∞) < capLife (travAll R L r η ψ ω) := lt_of_le_of_lt (by exact_mod_cast hr') hl
      have hlR : ENNReal.ofReal (r' : ℝ) < capLife (trav (η ω) (cfPocket (R ω) (L ω) r)
          (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) := by
        rw [ENNReal.ofReal_coe_nnreal]; exact hl'
      have hqR : ENNReal.ofReal (q : ℝ) < capLife (trav (η ω) (cfPocket (R ω) (L ω) r)
          (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) := by
        rw [ENNReal.ofReal_coe_nnreal]; exact hl
      have hT' : ambTime0 (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
          (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) q ≤ σ ω := by
        have : ENNReal.ofReal (ambTime0 (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
            (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) q) ≤ ENNReal.ofReal (σ ω) := by
          rw [ENNReal.ofReal_coe_nnreal]; exact hT
        exact (ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg _)).1 this
      -- the pocket visits at rational times
      have hvis : ∀ p : ℚ, (0 : ℝ) ≤ p → η ω p ∈ cfPocket (R ω) (L ω) r →
          (p : ℝ) ∈ Ico (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) :=
        fun p hp0 hpC => by
          have := hP.erase.mem_visitSet hp0 hpC
          exact ⟨this.1.1.le, this.1.2⟩
      simp only [prefixEvent, mem_ofPred_eq, hω, hl', true_and]
      change (Restart.dyadicSquare n k ∩ trav (η ω) (cfPocket (R ω) (L ω) r)
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) ''
          Icc 0 (capInv (trav (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
            (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) r')).Nonempty ↔ _
      rw [prefix_nonempty_iff_visit hP hr0' hlR (Restart.isClosed_dyadicSquare n k)]
      refine forall_congr' fun m => ?_
      rw [exists_visit_iff_rat hP isOpen_thickening]
      constructor
      · rintro ⟨p, hp0, hpC, hpr, hpS⟩
        have hpI := hvis p hp0 hpC
        have he := adTrace_eq_of_mem hcfg hζA hω (show (0 : ℝ) ≤ (StripSys.rt p : ℝ) from NNReal.coe_nonneg _)
        rw [rt_coe hp0] at he
        -- `p` is before the stop
        have hpT : (p : ℝ) < σ ω := by
          refine lt_of_lt_of_le (lt_of_not_ge fun h => ?_) hT'
          have := (ambTime0_le_iff hP (NNReal.coe_nonneg q) hqR hpI).1 h
          linarith [(show (r' : ℝ) ≤ q from hr')]
        refine ⟨p, hp0, by rw [← NNReal.coe_lt_coe, rt_coe hp0]; exact hpT, ?_⟩
        simp only [hV, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Iio, rt_coe hp0, he, hω, hpC, and_self,
          true_and]
        refine ⟨by rw [← relCap_eq_ratCap hcfg hζA hψ hω hpI]; exact hpr, ?_⟩
        rw [visPt, ite_eq_left ⟨hω, he ▸ hpC⟩, he]
        exact hpS
      · rintro ⟨p, hp0, -, hpV⟩
        simp only [hV, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Iio, rt_coe hp0] at hpV
        obtain ⟨⟨⟨-, hpC⟩, hpr⟩, hpS⟩ := hpV
        have he := adTrace_eq_of_mem hcfg hζA hω (show (0 : ℝ) ≤ (StripSys.rt p : ℝ) from NNReal.coe_nonneg _)
        rw [rt_coe hp0] at he
        rw [he] at hpC
        have hpI := hvis p hp0 hpC
        refine ⟨p, hp0, hpC, by rw [relCap_eq_ratCap hcfg hζA hψ hω hpI]; exact hpr, ?_⟩
        rw [visPt, ite_eq_left ⟨hω, he ▸ hpC⟩, he] at hpS
        exact hpS
    rw [e]
    exact hD.inter (MeasurableSet.iInter fun m => MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ =>
      measurableSet_lt_inter_sup hσ _ (hVm m p))

/-- **`IsMarkedStop` for the marked stop of the bounded change pocket** (the Galmarino property of `T⁰(q)`, with the
marks `locPrefixSigma 𝓦 A γ q` and the walls' information `X`, `𝓦 ≤ σ(X) ∨ 𝓕_0`). -/
theorem isMarkedStop_stopTimeM (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) (q : ℝ≥0) :
    IsMarkedStop (locPrefixSigma 𝓦 A (travAll R L r η ψ) q) 𝓕 X (stopTimeM A R L r η ψ q) := by
  intro σ hσ M hM
  have hD := measurableSet_stopTimeM_le h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hψ hψm q hσ
  have hle : locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤
      traceSigma (MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace) _ hD := by
    refine sup_le (fun M hM => hD.inter (measurableSet_sup_of_zero hσ (h𝓦 _ hM)))
      (MeasurableSpace.generateFrom_le ?_)
    rintro _ ⟨r', hr', n, k, rfl⟩
    exact measurableSet_stopTimeM_le_inter_prefix h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hψ hψm hr' n k hσ
  exact hle M hM

/-- **The marks are events of `σ(X) ∨ 𝓕_∞`** (`hS0`). -/
theorem measurableSet_sup_iSup_of_locPrefixSigma (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) (q : ℝ≥0) (M : Set Ω)
    (hM : MeasurableSet[locPrefixSigma 𝓦 A (travAll R L r η ψ) q] M) :
    MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ⨆ t, 𝓕 t] M := by
  classical
  have hmono : ∀ t, MeasurableSpace.comap X inferInstance ⊔ 𝓕 t ≤
      MeasurableSpace.comap X inferInstance ⊔ ⨆ t, 𝓕 t := fun t => sup_le_sup_left (le_iSup (fun t => 𝓕 t) t) _
  refine (sup_le ((h𝓦.trans (hmono 0))) (MeasurableSpace.generateFrom_le ?_)) M hM
  rintro _ ⟨r', -, n, k, rfl⟩
  have e : A ∩ prefixEvent (travAll R L r η ψ) r' n k =
      ⋃ N : ℕ, ({ω | stopTimeM A R L r η ψ r' ω ≤ ((N : ℝ≥0) : ℝ≥0∞)} ∩
        (A ∩ prefixEvent (travAll R L r η ψ) r' n k)) := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hω, hpre⟩
      have hl : (r' : ℝ≥0∞) < capLife (travAll R L r η ψ ω) := hpre.1
      have hfin : stopTimeM A R L r η ψ r' ω ≠ ⊤ := by
        unfold stopTimeM
        rw [ite_eq_left ⟨hω, hl⟩]
        exact ENNReal.ofReal_ne_top
      obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hfin
      exact ⟨N, by rw [ENNReal.coe_natCast]; exact hN.le, hω, hpre⟩
    · rintro ⟨N, -, h⟩
      exact h
  rw [e]
  refine MeasurableSet.iUnion fun N => ?_
  have hc := isStoppingTime_const 𝓕 (N : ℝ≥0)
  have h := measurableSet_stopTimeM_le_inter_prefix h𝓦 hWad hRm hLm hGm hG hA hAG hcfg hζA hψ hψm (le_refl r') n k
    (σ := fun _ => (N : ℝ≥0)) hc
  rw [IsStoppingTime.measurableSpace_const] at h
  exact hmono _ _ h

end Meas


/-! ### The walls' marked union law at `T⁰(q)` -/

section Law

open LQGMetric (DistOn)
open WangWu (negInv)
open WholeField PocketStopField PocketStopWalls PocketMarks PocketSeedOpen PocketUnionPt PocketStop

variable {Ω : Type*}

/-- **`PocketStopWallsLaw` at the left end `T⁰(q)` for a bounded mixed or outer pocket, without stop inputs**
(Aux. lemma
35's marked union law of the walls with the counterflow hull, rulings R67–R68): PROVE-STRIPSYS41's
`pocketStopWallsLaw_stopHull0` with the stop `T⁰(q)` taken on the live event (`stopTimeM`), whose Galmarino property
(`isMarkedStop_stopTimeM`) and `hS0` (`measurableSet_sup_iSup_of_locPrefixSigma`) are proved from the configuration,
the Jordan coordinate's point measurability and `𝓦 ≤ σ(fullHist ![R, L]) ∨ 𝓕_0`. -/
theorem pocketStopWallsLaw_stopHull0_marked
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
    (hAG : A ⊆ G) (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) (q : ℝ≥0) :
    PocketStopWallsLaw 𝓦 P A (travAll R L r η ψ) (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (stopHull0 R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q) (centredField h'' u₀') q := by
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
  refine pocketStopWallsLaw_regHull (T := stopTimeM A R L r η ψ q) hC hκ' hu₀' hX hζ (measurable_fullHist hm2)
    (measurable_negInv_walls hc2 hm2)
    (fun U G hUH hG hd B hB => walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc2 h02 hm2 hdet2 hloc2 U G hUH hG hd B hB)
    (fun ω hω hl => ?_)
    (isMarkedStop_stopTimeM h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q)
    (measurableSet_sup_iSup_of_locPrefixSigma h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q)
  have hT : stopTimeM A R L r η ψ q ω = stopTime0 R L r η ψ q ω := by
    unfold stopTimeM
    exact ite_eq_left ⟨hω, hl⟩
  rw [hT]
  exact ⟨ENNReal.ofReal_lt_top, stopHull0_eq_regHull' (hcfg ω hω) (hζA ω hω) q⟩

end Law

end InteractingSLE.Sec7.PocketStopMarked.Outer
