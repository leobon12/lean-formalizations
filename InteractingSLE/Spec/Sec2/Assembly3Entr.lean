/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly3Obs
import InteractingSLE.Spec.Sec2.AssemblyTheorem

/-!
# Theorem 2.2, uniqueness in law for the admissible entrances

Packet PROVE-SEC2-PATCH4. Two integrated `SLE_a(ρ)` evolutions of an ordered force word with a left
and a right mark at `0` (seed groups of total weights `> −2`) have the same killed
finite-dimensional laws. With PROVE-SEC2-PATCH's `measure_killedState_eq_of_separated_or_threshold`
this gives the frozen uniqueness statement of Theorem 2.2 for every ordered word
(`InteractingSLE.IsIntegratedSLEEvolution.measure_killedState_eq_assembled`, provider form).

Route (Specification, proof of Theorem 2.2, L488 "One can also reverse this procedure …"):

1. **Modification** (`exists_good_modification`): each evolution is changed on a null set, in the
   usual augmentation of its filtration, so that every path is continuous before the lifetime, every
   Brownian path is continuous and the lifetime is positive; the killed laws do not change.
2. **Localization**: `T = entT`, the first time a non-seed mark comes within `δ` of the driver or
   the lifetime is reached, capped at `1`, is a stopping time with `0 < T ≤ ζ`, and `T < ζ` almost
   surely (`ae_entT_lt_lifetime`, by Aux. lemma 3: before `T` only whole seed groups can meet the
   driver).
3. **Reduction** (`IsIntegratedSLEEvolution.measure_killedState_eq_of_map_observe_eq`): it suffices
   that the observations up to `T` have the same law; **reverse Girsanov**
   (`IsSLEEvolutionUpTo.map_observe_brownian_eq`, the non-seed weights changed to `0`): it suffices
   that the observations with the changed Brownian motion `B̂` have the same law under the changed
   measures `Q`.
4. Under `Q` the merged seeds form a local two-seed evolution up to `T` (`mergeSeeds`), which is
   continued after `T` by the maximal solution (`isIntegratedSLEEvolution_contClosed`, on the
   processes stopped at `T`) to a two-seed evolution `G`; the law of its code is unique
   (`map_stCode_eq_twoSeed`, PROVE-SEC2-JAC2), and the observation is a fixed measurable function of
   the code (`obsOfCode_stCode`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly3

open Assembly Assembly2

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-! ### Step 1: a good modification -/

open Classical in
/-- **A good modification of an evolution**: changed on a null set, in the usual augmentation,
every path is continuous before the lifetime, every Brownian path is continuous, the initial
values hold for every `ω`, the lifetime is positive, null sets are in every `𝓖 t`, and the killed
finite-dimensional laws are unchanged. -/
theorem exists_good_modification (hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∃ (𝓖 : Filtration ℝ≥0 mΩ) (_ : 𝓖.IsRightContinuous) (W' : ℝ≥0 → Ω → ℝ)
      (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ)
      (ζ' : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓖 W' VL' VR' B' ζ' ∧
      (∀ ω, ContinuousOn (W' · ω) {t | (t : ℝ≥0∞) < ζ' ω}) ∧
      (∀ i ω, ContinuousOn (VL' i · ω) {t | (t : ℝ≥0∞) < ζ' ω}) ∧
      (∀ j ω, ContinuousOn (VR' j · ω) {t | (t : ℝ≥0∞) < ζ' ω}) ∧
      (∀ ω, Continuous (B' · ω)) ∧ (∀ ω, W' 0 ω = 0) ∧ (∀ i ω, VL' i 0 ω = xL i) ∧
      (∀ j ω, VR' j 0 ω = xR j) ∧ (∀ ω, 0 < ζ' ω) ∧
      (∀ N : Set Ω, MeasurableSet N → P N = 0 → ∀ t, MeasurableSet[𝓖 t] N) ∧
      ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (StateSp nL nR)),
        P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
          (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j} =
        P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ' ω ∧
          (W' (ts j) ω, (fun i => VL' i (ts j) ω), (fun i => VR' i (ts j) ω), B' (ts j) ω) ∈
            A j} := by
  have hgood : ∀ᵐ ω ∂P, IsIntegratedSLEPath a xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (ζ ω) ∧ Continuous (B · ω) :=
    hE.2.2.2.2.and hE.1.1.cont
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hgoodω : ∀ ω, ω ∉ N → IsIntegratedSLEPath a xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (ζ ω) ∧ Continuous (B · ω) := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  obtain ⟨hB', hB'c⟩ := Ito.isFilteredBrownianReal_modify hE.1 hNm.compl (by simpa using hN0)
    fun ω hω => (hgoodω ω hω).2
  set 𝓖 := usualAugmentation (Ito.nullAugmented 𝓕 P) P with h𝓖
  have h𝓤 : usualAugmentation 𝓕 P ≤ 𝓖 :=
    Ito.usualAugmentation_mono (Ito.le_nullAugmented 𝓕 P) P
  have hnull : ∀ N' : Set Ω, MeasurableSet N' → P N' = 0 → ∀ t, MeasurableSet[𝓖 t] N' :=
    fun N' hm h0 t => Ito.measurableSet_usualAugmentation_of_null hm h0 t
  have hNt : ∀ t, MeasurableSet[𝓖 t] N := hnull N hNm hN0
  set ζ' : Ω → ℝ≥0∞ := fun ω => if ω ∈ N then ⊤ else ζ ω with hζ'
  have hadapt : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓕 ζ X → ∀ c : ℝ,
      AdaptedBefore 𝓖 ζ' (fun t ω => if ω ∈ N then c else X t ω) := fun {X} hX c t A hA => by
    have e : {ω | (t : ℝ≥0∞) < ζ' ω ∧ (if ω ∈ N then c else X t ω) ∈ A} =
        ({ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} ∩ Nᶜ) ∪ (N ∩ {_ω | c ∈ A}) := by
      ext ω
      by_cases hω : ω ∈ N <;> simp [hζ', hω]
    rw [e]
    exact (h𝓤 t _ (((Ito.le_usualAugmentation 𝓕 P t) _ (hX t A hA)))).inter (hNt t).compl
      |>.union ((hNt t).inter (MeasurableSet.const _))
  have hpathω : ∀ ω, ω ∉ N → IsIntegratedSLEPath a xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (ζ ω) := fun ω hω => (hgoodω ω hω).1
  refine ⟨𝓖, inferInstance, fun t ω => if ω ∈ N then 0 else W t ω,
    fun i t ω => if ω ∈ N then xL i else VL i t ω,
    fun j t ω => if ω ∈ N then xR j else VR j t ω,
    fun t ω => @ite ℝ (ω ∈ Nᶜ) (Classical.propDecidable (ω ∈ Nᶜ)) (B t ω) 0, ζ',
    ⟨Ito.isFilteredBrownianReal_usualAugmentation hB', hadapt hE.2.1 0,
      fun i => hadapt (hE.2.2.1 i) (xL i), fun j => hadapt (hE.2.2.2.1 j) (xR j), ?_⟩,
    fun ω => ?_, fun i ω => ?_, fun j ω => ?_, hB'c, fun ω => ?_, fun i ω => ?_, fun j ω => ?_,
    fun ω => ?_, hnull, fun n ts A => ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    have hω' : ω ∈ Nᶜ := hω
    simp only [hω, hω', hζ', ↓reduceIte]
    exact hpathω ω hω
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]; exact continuousOn_const
    · simp only [hω, hζ', ↓reduceIte]; exact (hpathω ω hω).isForcePath.continuousOn_w
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]; exact continuousOn_const
    · simp only [hω, hζ', ↓reduceIte]; exact (hpathω ω hω).isForcePath.continuousOn_vL i
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]; exact continuousOn_const
    · simp only [hω, hζ', ↓reduceIte]; exact (hpathω ω hω).isForcePath.continuousOn_vR j
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
    · simp only [hω, ↓reduceIte]; exact (hpathω ω hω).isForcePath.w_zero
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
    · simp only [hω, ↓reduceIte]; exact (hpathω ω hω).isForcePath.vL_zero i
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
    · simp only [hω, ↓reduceIte]; exact (hpathω ω hω).isForcePath.vR_zero j
  · by_cases hω : ω ∈ N
    · simp only [hζ', hω, ↓reduceIte]; exact ENNReal.zero_lt_top
    · simp only [hζ', hω, ↓reduceIte]
      refine pos_iff_ne_zero.2 fun h0 => hthr ?_
      exact (hpathω ω hω).isForcePath.threshold_of_eq_zero h0
  · refine measure_congr ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    have hω' : ω ∈ Nᶜ := hω
    simp only [hω, hω', hζ', ↓reduceIte]

/-! ### Step 2: the localization time comes before the lifetime -/

/-- **The localization time is almost surely before the lifetime** (Aux. lemma 3: at a finite
lifetime the state converges to a threshold state, but before the localization time only whole
seed groups can meet the driver, and their weights exceed `−2`). -/
theorem ae_entT_lt_lifetime (ha : 0 < a) {δ : ℝ} (hδ : 0 < δ) {pL : Fin nL} {pR : Fin nR}
    (hpL : xL pL = 0) (hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) (hpR : xR pR = 0) :
    ∀ᵐ ω ∂P, entT δ xL xR ζ W VL VR ω < ζ ω := by
  classical
  have : Nonempty (Fin nL ⊕ Fin nR) := ⟨Sum.inl pL⟩
  obtain ⟨hsL, hsR⟩ := (not_thr_iff_seedSum xL xR ρL ρR).1 hthr
  filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold ha] with ω hp hlim
  have hle := entT_le_lifetime (ζ := ζ) (W := W) (VL := VL) (VR := VR) (xL := xL) (xR := xR)
    hδ.le ω
  refine lt_of_le_of_ne hle fun heq => ?_
  have hfin : ζ ω ≠ ⊤ := by rw [← heq]; exact entT_ne_top ω
  rcases eq_or_ne (ζ ω) 0 with h0 | h0
  · exact hthr (hp.isForcePath.threshold_of_eq_zero h0)
  set T : ℝ≥0 := (ζ ω).toNNReal with hTdef
  have hT : (T : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hfin
  have hT0 : 0 < T := by
    have : (0 : ℝ≥0∞) < T := by rw [hT]; exact pos_iff_ne_zero.2 h0
    exact_mod_cast this
  obtain ⟨w₀, vL₀, vR₀, hl, hthr₀⟩ := hlim T hT0 hT
  have hNe : NeBot (𝓝[<] T) := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
  have hbefore : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, ((t : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      ∀ k, δ < gapFam δ xL xR W VL VR k t ω := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine lt_of_lt_entT hδ.le ?_
    rw [heq, ← hT]; exact_mod_cast ht
  have hw := (continuous_fst.tendsto _).comp hl
  have hvL : ∀ i, Tendsto (fun t => VL i t ω) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    (((continuous_apply i).comp (continuous_fst.comp continuous_snd)).tendsto _).comp hl
  have hvR : ∀ j, Tendsto (fun t => VR j t ω) (𝓝[<] T) (𝓝 (vR₀ j)) := fun j =>
    (((continuous_apply j).comp (continuous_snd.comp continuous_snd)).tendsto _).comp hl
  have hp' := hp.isSLEPathUpTo (le_refl (ζ ω))
  -- seeds have a common limit; the other marks stay away
  have hseedL : ∀ i, xL i = 0 → vL₀ i = vL₀ pL := fun i hi =>
    tendsto_nhds_unique (hvL i) ((hvL pL).congr' (by
      filter_upwards [hbefore] with t ht
      exact hp'.vL_eq_of_xL_eq (hpL.trans hi.symm) ht.1))
  have hseedR : ∀ j, xR j = 0 → vR₀ j = vR₀ pR := fun j hj =>
    tendsto_nhds_unique (hvR j) ((hvR pR).congr' (by
      filter_upwards [hbefore] with t ht
      exact hp'.vR_eq_of_xR_eq (hpR.trans hj.symm) ht.1))
  have hfarL : ∀ i, xL i ≠ 0 → vL₀ i ≠ w₀ := fun i hi he => by
    have hg : δ ≤ w₀ - vL₀ i := ge_of_tendsto (hw.sub (hvL i)) (by
      filter_upwards [hbefore] with t ht
      have := ht.2 (Sum.inl i)
      simp only [gapFam, Sum.elim_inl, hi, ↓reduceIte] at this
      exact this.le)
    rw [he, sub_self] at hg
    linarith
  have hfarR : ∀ j, xR j ≠ 0 → vR₀ j ≠ w₀ := fun j hj he => by
    have hg : δ ≤ vR₀ j - w₀ := ge_of_tendsto ((hvR j).sub hw) (by
      filter_upwards [hbefore] with t ht
      have := ht.2 (Sum.inr j)
      simp only [gapFam, Sum.elim_inr, hj, ↓reduceIte] at this
      exact this.le)
    rw [he, sub_self] at hg
    linarith
  -- the sums over the marks at the limit driver
  have hsumL : -2 < ∑ i ∈ Finset.univ.filter (fun i => vL₀ i = w₀), ρL i := by
    by_cases hpw : vL₀ pL = w₀
    · have e : Finset.univ.filter (fun i => vL₀ i = w₀) =
          Finset.univ.filter (fun i => xL i = 0) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun h => by_contra fun hi => hfarL i hi h, fun hi => by rw [hseedL i hi, hpw]⟩
      rw [e]; exact hsL
    · have e : Finset.univ.filter (fun i => vL₀ i = w₀) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro h
        by_cases hi : xL i = 0
        · exact hpw (by rw [← hseedL i hi]; exact h)
        · exact hfarL i hi h
      rw [e, Finset.sum_empty]; norm_num
  have hsumR : -2 < ∑ j ∈ Finset.univ.filter (fun j => vR₀ j = w₀), ρR j := by
    by_cases hpw : vR₀ pR = w₀
    · have e : Finset.univ.filter (fun j => vR₀ j = w₀) =
          Finset.univ.filter (fun j => xR j = 0) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun h => by_contra fun hj => hfarR j hj h, fun hj => by rw [hseedR j hj, hpw]⟩
      rw [e]; exact hsR
    · have e : Finset.univ.filter (fun j => vR₀ j = w₀) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro h
        by_cases hj : xR j = 0
        · exact hpw (by rw [← hseedR j hj]; exact h)
        · exact hfarR j hj h
      rw [e, Finset.sum_empty]; norm_num
  rcases hthr₀ with h | h
  · exact absurd h (not_le.2 hsumL)
  · exact absurd h (not_le.2 hsumR)

/-! ### Step 3: the two-seed evolution under the changed measure -/

section Cover

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The two-seed cover.** For a good evolution of an admissible entrance, under the Girsanov
measure removing the weights of the non-seed marks up to the localization time `T`, there is a
two-seed evolution (driven by the changed Brownian motion) whose code determines the observation of
the evolution up to `T`. -/
theorem exists_twoSeed_cover (ha : 0 < a) (hF : IsOrderedForceWord xL xR) {δ : ℝ} (hδ : 0 < δ)
    (hδL : ∀ i, xL i ≠ 0 → δ < -xL i) (hδR : ∀ j, xR j ≠ 0 → δ < xR j)
    {pL : Fin nL} {pR : Fin nR} (hpL : xL pL = 0) (hpR : xR pR = 0)
    (hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓖 W VL VR B ζ)
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVLc : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVRc : ∀ j ω, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hBc : ∀ ω, Continuous (B · ω)) (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i)
    (hVR0 : ∀ j ω, VR j 0 ω = xR j) (hζ0 : ∀ ω, 0 < ζ ω)
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → ∀ t, MeasurableSet[𝓖 t] N) :
    ∃ (Gw : ℝ≥0 → Ω → ℝ) (Gl Gr : Fin 1 → ℝ≥0 → Ω → ℝ) (ζG : Ω → ℝ≥0∞),
      IsProbabilityMeasure (girsanovMeasure P 𝓖 B (weightDrift a δ ρL (seedW xL ρL) ρR
        (seedW xR ρR) (entT δ xL xR ζ W VL VR) ζ W VL VR) (1 + 1)) ∧
      IsIntegratedSLEEvolution a (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
        (fun _ => seedSum xL ρL) (fun _ => seedSum xR ρR)
        (girsanovMeasure P 𝓖 B (weightDrift a δ ρL (seedW xL ρL) ρR (seedW xR ρR)
          (entT δ xL xR ζ W VL VR) ζ W VL VR) (1 + 1)) 𝓖 Gw Gl Gr
        (girsanovProcess B (weightDrift a δ ρL (seedW xL ρL) ρR (seedW xR ρR)
          (entT δ xL xR ζ W VL VR) ζ W VL VR)) ζG ∧
      ∀ᵐ ω ∂(girsanovMeasure P 𝓖 B (weightDrift a δ ρL (seedW xL ρL) ρR (seedW xR ρR)
          (entT δ xL xR ζ W VL VR) ζ W VL VR) (1 + 1)),
        obsOfCode δ xL xR (stCode ζG Gw Gl Gr (girsanovProcess B (weightDrift a δ ρL
          (seedW xL ρL) ρR (seedW xR ρR) (entT δ xL xR ζ W VL VR) ζ W VL VR)) ω) =
        observe (entT δ xL xR ζ W VL VR) W VL VR (girsanovProcess B (weightDrift a δ ρL
          (seedW xL ρL) ρR (seedW xR ρR) (entT δ xL xR ζ W VL VR) ζ W VL VR)) ω := by
  classical
  have hne : Nonempty (Fin nL ⊕ Fin nR) := ⟨Sum.inl pL⟩
  obtain ⟨hsL, hsR⟩ := (not_thr_iff_seedSum xL xR ρL ρR).1 hthr
  set T := entT δ xL xR ζ W VL VR with hTdef
  set θ := weightDrift a δ ρL (seedW xL ρL) ρR (seedW xR ρR) T ζ W VL VR with hθdef
  set Q := girsanovMeasure P 𝓖 B θ (1 + 1) with hQdef
  set Bh := girsanovProcess B θ with hBhdef
  -- the localization time
  have hTle : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | T ω ≤ s} :=
    measurableSet_entT_le hδ.le hE.2.1 hE.2.2.1 hE.2.2.2.1 hWc hVLc hVRc
  have hTζ : ∀ ω, T ω ≤ ζ ω := entT_le_lifetime hδ.le
  have hT1 : ∀ ω, T ω ≤ ((1 : ℝ≥0) : ℝ≥0∞) := fun ω => by
    rw [ENNReal.coe_one]; exact entT_le_one ω
  have h0gap : ∀ ω k, δ < gapFam δ xL xR W VL VR k 0 ω := by
    rintro ω (i | j)
    · simp only [gapFam, Sum.elim_inl]
      split_ifs with hi
      · linarith
      · rw [hW0, hVL0]; linarith [hδL i hi]
    · simp only [gapFam, Sum.elim_inr]
      split_ifs with hj
      · linarith
      · rw [hW0, hVR0]; linarith [hδR j hj]
  have hT0 : ∀ ω, 0 < T ω := fun ω =>
    entT_pos hδ.le (hWc ω) (fun i => hVLc i ω) (fun j => hVRc j ω) (hζ0 ω) (h0gap ω)
  -- Girsanov
  have hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < T ω →
      (∀ i, seedW xL ρL i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧
        ∀ j, seedW xR ρR j ≠ ρR j → δ ≤ |W t ω - VR j t ω| := ae_of_all _ fun ω t ht => by
    have hk := (lt_of_lt_entT hδ.le ht).2
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · have hxi : xL i ≠ 0 := fun h => hi (seedW_of_eq h)
      have := hk (Sum.inl i)
      simp only [gapFam, Sum.elim_inl, hxi, ↓reduceIte] at this
      exact this.le.trans (le_abs_self _)
    · have hxj : xR j ≠ 0 := fun h => hj (seedW_of_eq h)
      have := hk (Sum.inr j)
      simp only [gapFam, Sum.elim_inr, hxj, ↓reduceIte] at this
      rw [abs_sub_comm]
      exact this.le.trans (le_abs_self _)
  have hEu := hE.isSLEEvolutionUpTo
  obtain ⟨hQ, hEQ⟩ := hEu.girsanov_changeWeights ha (seedW xL ρL) (seedW xR ρR) hTle hTζ hT1 hδ
    hgap
  have hQp : IsProbabilityMeasure Q := hQ.isProb
  have hQP : Q ≪ P := hQ.ac
  obtain ⟨hθp, hθb, -⟩ := hEu.weightDrift_props (seedW xL ρL) (seedW xR ρR) hTle hTζ hδ
  have hBhc : ∀ ω, Continuous (Bh · ω) := fun ω =>
    (hBc ω).add (Girsanov.continuous_drift hθp hθb ω)
  -- `T < ζ` almost surely
  have hTltP : ∀ᵐ ω ∂P, T ω < ζ ω := ae_entT_lt_lifetime ha hδ hpL hthr hE hpR
  -- the stopped processes
  set Tn : Ω → ℝ≥0 := fun ω => (T ω).toNNReal with hTndef
  have hTn : ∀ ω, (Tn ω : ℝ≥0∞) = T ω := fun ω => ENNReal.coe_toNNReal (entT_ne_top ω)
  have hTn0 : ∀ ω, 0 < Tn ω := fun ω => by
    have : (0 : ℝ≥0∞) < Tn ω := by rw [hTn]; exact hT0 ω
    exact_mod_cast this
  have hTst : IsStoppingTime 𝓖 fun ω => (Tn ω : WithTop ℝ≥0) := fun u => by
    have e : {ω | (Tn ω : WithTop ℝ≥0) ≤ u} = {ω | T ω ≤ u} := by
      ext ω
      simp only [mem_ofPred_eq]
      rw [← hTn ω]
      exact WithTop.coe_le_coe.trans ENNReal.coe_le_coe.symm
    rw [e]
    exact hTle u
  have hTm : Measurable T := by
    refine measurable_of_Iic fun x => ?_
    induction x using ENNReal.recTopCoe with
    | top => simp
    | coe s => exact 𝓖.le s _ (hTle s)
  have hζm : Measurable ζ := measurable_lifetime hE.2.1
  set N₂ : Set Ω := {ω | ¬ (T ω < ζ ω)} with hN₂
  have hN₂m : MeasurableSet N₂ := (measurableSet_lt hTm hζm).compl
  have hN₂0 : P N₂ = 0 := ae_iff.1 hTltP
  have hN₂Q : ∀ᵐ ω ∂Q, ω ∉ N₂ := hQP.ae_le (measure_eq_zero_iff_ae_notMem.1 hN₂0)
  set Ws : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ N₂ then 0 else stopK ζ Tn W t ω with hWs
  set Ls : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ N₂ then 0 else stopK ζ Tn (VL pL) t ω with hLs
  set Rs : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ N₂ then 0 else stopK ζ Tn (VR pR) t ω with hRs
  have hsm : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓖 ζ X →
      (∀ ω, ContinuousOn (X · ω) {t | (t : ℝ≥0∞) < ζ ω}) → ∀ t,
      Measurable[𝓖 t] (fun ω => if ω ∈ N₂ then 0 else stopK ζ Tn X t ω) := fun {X} hX hXc t => by
    let _ : MeasurableSpace Ω := 𝓖 t
    exact Measurable.ite (hnull N₂ hN₂m hN₂0 t) measurable_const (measurable_stopK hX hXc hTst t)
  have hsc : ∀ {X : ℝ≥0 → Ω → ℝ}, (∀ ω, ContinuousOn (X · ω) {t | (t : ℝ≥0∞) < ζ ω}) →
      ∀ ω, Continuous (fun t => if ω ∈ N₂ then 0 else stopK ζ Tn X t ω) := fun {X} hXc ω => by
    by_cases hω : ω ∈ N₂
    · simp only [hω, ↓reduceIte]; exact continuous_const
    · simp only [hω, ↓reduceIte]
      have : T ω < ζ ω := by simpa [hN₂] using hω
      exact continuous_stopK (hXc ω) (by rw [hTn]; exact this)
  have hsEq : ∀ {X : ℝ≥0 → Ω → ℝ} {ω : Ω}, ω ∉ N₂ → ∀ t : ℝ≥0, t ≤ Tn ω →
      (if ω ∈ N₂ then 0 else stopK ζ Tn X t ω) = X t ω := fun {X ω} hω t ht => by
    have : T ω < ζ ω := by simpa [hN₂] using hω
    simp only [hω, ↓reduceIte]
    exact stopK_of_le (by rw [hTn]; exact this) ht
  -- the merged two-seed path under `Q` up to `T`
  have hmerge : ∀ᵐ ω ∂Q, IsSLEPathUpTo a (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
      (fun _ => seedSum xL ρL) (fun _ => seedSum xR ρR) (Ws · ω) (fun _ t => Ls t ω)
      (fun _ t => Rs t ω) (Bh · ω) (Tn ω) := by
    filter_upwards [hEQ.ae_path, hN₂Q] with ω hp hω
    have hm := hp.mergeSeeds hpL hpR hsL hsR
    rw [← hTn ω] at hm
    refine isSLEPathUpTo_congr hm (hsEq hω 0 (zero_le)) (fun _ => hsEq hω 0 (zero_le))
      (fun _ => hsEq hω 0 (zero_le)) (fun t ht => hsEq hω t ?_) (fun t ht _ => hsEq hω t ?_)
      (fun t ht _ => hsEq hω t ?_) fun _ _ => rfl
    all_goals exact le_of_lt (by exact_mod_cast ht)
  -- the word at `T` is good
  have hgood : ∀ᵐ ω ∂Q, GoodWord (fun _ : Fin 1 => seedSum xL ρL) (fun _ : Fin 1 => seedSum xR ρR)
      (contWord Ws (fun _ : Fin 1 => Ls) (fun _ : Fin 1 => Rs) Tn ω) := by
    filter_upwards [hQP.ae_le hE.2.2.2.2, hQP.ae_le hTltP, hN₂Q] with ω hp hlt hω
    have hp' := hp.isSLEPathUpTo (le_refl (ζ ω))
    have hTlt : (Tn ω : ℝ≥0∞) < ζ ω := by rw [hTn]; exact hlt
    have hw : Ws (Tn ω) ω = W (Tn ω) ω := hsEq hω _ le_rfl
    have hl : Ls (Tn ω) ω = VL pL (Tn ω) ω := hsEq hω _ le_rfl
    have hr : Rs (Tn ω) ω = VR pR (Tn ω) ω := hsEq hω _ le_rfl
    refine ⟨fun _ _ => ?_, ⟨fun _ _ _ => le_rfl, fun _ => ?_, fun _ _ _ => le_rfl, fun _ => ?_⟩,
      not_thr_twoSeed hsL hsR _ _ _⟩
    · show Ls (Tn ω) ω - Ws (Tn ω) ω < Rs (Tn ω) ω - Ws (Tn ω) ω
      rw [hw, hl, hr]
      linarith [hp'.vL_lt_vR_of_pos hF (hTn0 ω) hTlt pL pR]
    · show Ls (Tn ω) ω - Ws (Tn ω) ω ≤ 0
      rw [hw, hl]
      linarith [hp'.vL_le_w hTlt pL]
    · show 0 ≤ Rs (Tn ω) ω - Ws (Tn ω) ω
      rw [hw, hr]
      linarith [hp'.w_le_vR hTlt pR]
  -- the continuation
  have hG := isIntegratedSLEEvolution_contClosed (P := Q) (𝓕 := 𝓖) ha hEQ.brownian hBhc
    (hsm hE.2.1 hWc) (fun _ t => hsm (hE.2.2.1 pL) (hVLc pL) t)
    (fun _ t => hsm (hE.2.2.2.1 pR) (hVRc pR) t) (hsc hWc) (fun _ => hsc (hVLc pL))
    (fun _ => hsc (hVRc pR)) hmerge hTst hTn0 hgood
  refine ⟨_, _, _, _, hQp, hG, ?_⟩
  filter_upwards [ae_lifetime_eq_top_twoSeed ha hG hsL hsR, hG.2.2.2.2, hQP.ae_le hE.2.2.2.2,
    hQP.ae_le hTltP, hN₂Q] with ω hζω hpG hp hlt hω
  have hpG' := hpG.isForcePath
  rw [hζω] at hpG'
  have huniv : {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun _ => ENNReal.coe_lt_top
  have hGwc := continuousOn_univ.1 (huniv ▸ hpG'.continuousOn_w)
  have hGlc := continuousOn_univ.1 (huniv ▸ hpG'.continuousOn_vL 0)
  have hGrc := continuousOn_univ.1 (huniv ▸ hpG'.continuousOn_vR 0)
  have hTlt : (Tn ω : ℝ≥0∞) < ζ ω := by rw [hTn]; exact hlt
  have hIic : Iic (Tn ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun t ht =>
    lt_of_le_of_lt (by exact_mod_cast ht) hTlt
  have hag : ∀ {f g : ℝ≥0 → ℝ}, Continuous f → ContinuousOn g {t | (t : ℝ≥0∞) < ζ ω} →
      (∀ s < Tn ω, f s = g s) → ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T ω → f t = g t := by
    intro f g hf hg hfg t ht
    have ht' : t ≤ Tn ω := by rw [← hTn ω] at ht; exact_mod_cast ht
    rcases lt_or_eq_of_le ht' with h | h
    · exact hfg t h
    · rw [h]
      exact eq_of_eqOn_Iio (hTn0 ω) hf.continuousOn (hg.mono hIic) hfg
  refine obsOfCode_stCode hδ hpL hpR (hp.isSLEPathUpTo le_rfl) (hT0 ω) hlt hζω hGwc hGlc hGrc
    (hBhc ω) (hag hGwc (hWc ω) fun s hs => ?_) (hag hGlc (hVLc pL ω) fun s hs => ?_)
    (hag hGrc (hVRc pR ω) fun s hs => ?_)
  · show concatAt (Tn ω) (Ws · ω) _ _ s = W s ω
    rw [concatAt_of_lt hs]; exact hsEq hω s hs.le
  · show concatAt (Tn ω) (Ls · ω) _ _ s = VL pL s ω
    rw [concatAt_of_lt hs]; exact hsEq hω s hs.le
  · show concatAt (Tn ω) (Rs · ω) _ _ s = VR pR s ω
    rw [concatAt_of_lt hs]; exact hsEq hω s hs.le

end Cover

/-! ### Step 4: uniqueness in law for the admissible entrances -/

section Main

open Girsanov

/-- The localization time of a good evolution: a positive stopping time, at most the lifetime and
`1`. -/
theorem entT_good {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {δ : ℝ} (hδ : 0 < δ) (hδL : ∀ i, xL i ≠ 0 → δ < -xL i)
    (hδR : ∀ j, xR j ≠ 0 → δ < xR j) (pL : Fin nL)
    (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓖 ζ (VR j))
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVLc : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVRc : ∀ j ω, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i) (hVR0 : ∀ j ω, VR j 0 ω = xR j)
    (hζ0 : ∀ ω, 0 < ζ ω) :
    (∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | entT δ xL xR ζ W VL VR ω ≤ s}) ∧
      Measurable (entT δ xL xR ζ W VL VR) ∧ (∀ ω, 0 < entT δ xL xR ζ W VL VR ω) ∧
      (∀ ω, entT δ xL xR ζ W VL VR ω ≤ ζ ω) ∧
      ∀ ω, entT δ xL xR ζ W VL VR ω ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by
  have hne : Nonempty (Fin nL ⊕ Fin nR) := ⟨Sum.inl pL⟩
  have hTle := measurableSet_entT_le (δ := δ) (xL := xL) (xR := xR) hδ.le hW hVL hVR hWc hVLc hVRc
  refine ⟨hTle, ?_, fun ω => entT_pos hδ.le (hWc ω) (fun i => hVLc i ω) (fun j => hVRc j ω)
    (hζ0 ω) ?_, entT_le_lifetime hδ.le, fun ω => by rw [ENNReal.coe_one]; exact entT_le_one ω⟩
  · refine measurable_of_Iic fun x => ?_
    induction x using ENNReal.recTopCoe with
    | top => simp
    | coe s => exact 𝓖.le s _ (hTle s)
  · rintro (i | j)
    · simp only [gapFam, Sum.elim_inl]
      split_ifs with hi
      · linarith
      · rw [hW0, hVL0]; linarith [hδL i hi]
    · simp only [gapFam, Sum.elim_inr]
      split_ifs with hj
      · linarith
      · rw [hW0, hVR0]; linarith [hδR j hj]

/-- **Theorem 2.2, uniqueness in law, for the admissible entrances**: an ordered word with a left
and a right mark at `0` whose seed is not a threshold state. -/
theorem measure_killedState_eq_of_entrance (ha : 0 < a) (hF : IsOrderedForceWord xL xR)
    {pL : Fin nL} {pR : Fin nR} (hpL : xL pL = 0) (hpR : xR pR = 0)
    (hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ))
    (hA : ∀ j, MeasurableSet (A j)) :
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈
          A j} := by
  classical
  obtain ⟨hsL, hsR⟩ := (not_thr_iff_seedSum xL xR ρL ρR).1 hthr
  -- the level `δ`
  set f : Fin nL ⊕ Fin nR → ℝ := Sum.elim (fun i => if xL i = 0 then 1 else -xL i)
    (fun j => if xR j = 0 then 1 else xR j) with hf
  have hfpos : ∀ k, 0 < f k := by
    rintro (i | j)
    · simp only [hf, Sum.elim_inl]
      split_ifs with h
      · exact one_pos
      · exact neg_pos.2 (lt_of_le_of_ne (hF.2.1 i) h)
    · simp only [hf, Sum.elim_inr]
      split_ifs with h
      · exact one_pos
      · exact lt_of_le_of_ne (hF.2.2.2 j) (Ne.symm h)
  obtain ⟨δ, hδ, hδf⟩ := exists_pos_forall_lt' f hfpos
  have hδL : ∀ i, xL i ≠ 0 → δ < -xL i := fun i hi => by
    simpa only [hf, Sum.elim_inl, hi, ↓reduceIte] using hδf (Sum.inl i)
  have hδR : ∀ j, xR j ≠ 0 → δ < xR j := fun j hj => by
    simpa only [hf, Sum.elim_inr, hj, ↓reduceIte] using hδf (Sum.inr j)
  -- good modifications
  obtain ⟨𝓖₁, h𝓖₁, W₁', VL₁', VR₁', B₁', ζ₁', hE₁, hW₁c, hVL₁c, hVR₁c, hB₁c, hW₁0, hVL₁0, hVR₁0,
    hζ₁0, hnull₁, hkill₁⟩ := exists_good_modification hthr h₁
  obtain ⟨𝓖₂, h𝓖₂, W₂', VL₂', VR₂', B₂', ζ₂', hE₂, hW₂c, hVL₂c, hVR₂c, hB₂c, hW₂0, hVL₂0, hVR₂0,
    hζ₂0, hnull₂, hkill₂⟩ := exists_good_modification hthr h₂
  rw [hkill₁ n ts A, hkill₂ n ts A]
  -- the localization times
  obtain ⟨hT₁le, hT₁m, hT₁0, hT₁ζ, hT₁1⟩ := entT_good hδ hδL hδR pL hE₁.2.1 hE₁.2.2.1
    hE₁.2.2.2.1 hW₁c hVL₁c hVR₁c hW₁0 hVL₁0 hVR₁0 hζ₁0
  obtain ⟨hT₂le, hT₂m, hT₂0, hT₂ζ, hT₂1⟩ := entT_good hδ hδL hδR pL hE₂.2.1 hE₂.2.2.1
    hE₂.2.2.2.1 hW₂c hVL₂c hVR₂c hW₂0 hVL₂0 hVR₂0 hζ₂0
  -- the two-seed covers
  obtain ⟨G₁w, G₁l, G₁r, ζG₁, hQ₁, hG₁, hid₁⟩ := exists_twoSeed_cover ha hF hδ hδL hδR hpL hpR
    hthr hE₁ hW₁c hVL₁c hVR₁c hB₁c hW₁0 hVL₁0 hVR₁0 hζ₁0 hnull₁
  obtain ⟨G₂w, G₂l, G₂r, ζG₂, hQ₂, hG₂, hid₂⟩ := exists_twoSeed_cover ha hF hδ hδL hδR hpL hpR
    hthr hE₂ hW₂c hVL₂c hVR₂c hB₂c hW₂0 hVL₂0 hVR₂0 hζ₂0 hnull₂
  have hm₁ := measurable_stCode hG₁.2.1 hG₁.2.2.1 hG₁.2.2.2.1 fun t =>
    (hG₁.1.2.1 t).mono (𝓖₁.le t) le_rfl
  have hm₂ := measurable_stCode hG₂.2.1 hG₂.2.2.1 hG₂.2.2.2.1 fun t =>
    (hG₂.1.2.1 t).mono (𝓖₂.le t) le_rfl
  have hcode := map_stCode_eq_twoSeed ha hsL hsR hG₁ hG₂
  have hΨ := measurable_obsOfCode (nL := nL) (nR := nR) (xL := xL) (xR := xR) hδ
  -- the observations under the changed measures
  set θ₁ := weightDrift a δ ρL (seedW xL ρL) ρR (seedW xR ρR) (entT δ xL xR ζ₁' W₁' VL₁' VR₁') ζ₁'
    W₁' VL₁' VR₁' with hθ₁
  set θ₂ := weightDrift a δ ρL (seedW xL ρL) ρR (seedW xR ρR) (entT δ xL xR ζ₂' W₂' VL₂' VR₂') ζ₂'
    W₂' VL₂' VR₂' with hθ₂
  set Q₁ := girsanovMeasure P₁ 𝓖₁ B₁' θ₁ (1 + 1) with hQ₁def
  set Q₂ := girsanovMeasure P₂ 𝓖₂ B₂' θ₂ (1 + 1) with hQ₂def
  have e₁ : Q₁.map (observe (entT δ xL xR ζ₁' W₁' VL₁' VR₁') W₁' VL₁' VR₁' (girsanovProcess B₁' θ₁))
      = (Q₁.map (stCode ζG₁ G₁w G₁l G₁r (girsanovProcess B₁' θ₁))).map (obsOfCode δ xL xR) := by
    rw [Measure.map_map hΨ hm₁]
    exact Measure.map_congr (hid₁.mono fun ω h => h.symm)
  have e₂ : Q₂.map (observe (entT δ xL xR ζ₂' W₂' VL₂' VR₂') W₂' VL₂' VR₂' (girsanovProcess B₂' θ₂))
      = (Q₂.map (stCode ζG₂ G₂w G₂l G₂r (girsanovProcess B₂' θ₂))).map (obsOfCode δ xL xR) := by
    rw [Measure.map_map hΨ hm₂]
    exact Measure.map_congr (hid₂.mono fun ω h => h.symm)
  have hlawQ : Q₁.map (observe (entT δ xL xR ζ₁' W₁' VL₁' VR₁') W₁' VL₁' VR₁'
      (girsanovProcess B₁' θ₁)) = Q₂.map (observe (entT δ xL xR ζ₂' W₂' VL₂' VR₂') W₂' VL₂' VR₂'
      (girsanovProcess B₂' θ₂)) := by
    rw [e₁, e₂, hcode]
  -- reverse Girsanov, and the reduction to the observations
  have hlawP := hE₁.isSLEEvolutionUpTo.map_observe_brownian_eq hE₂.isSLEEvolutionUpTo
    (seedW xL ρL) (seedW xR ρR) hT₁le hT₂le hT₁ζ hT₂ζ hT₁1 hT₂1 hδ hlawQ
  exact IsIntegratedSLEEvolution.measure_killedState_eq_of_map_observe_eq ha hF hE₁ hE₂ hT₁m hT₂m
    (ae_of_all _ hT₁0) (ae_of_all _ hT₂0) hT₁ζ hT₂ζ hlawP n ts A hA

end Main

end Assembly3

end Sec2

/-- **Theorem 2.2, uniqueness in law** (Specification p. 21), in the provider form of the frozen
anchor `IsIntegratedSLEEvolution.measure_killedState_eq`: every argument implicit, the hypotheses
as auto-parameters. Separated words and threshold seeds are PROVE-SEC2-PATCH's
`measure_killedState_eq_of_separated_or_threshold`; the remaining ordered words have a left and a
right mark at `0` and a non-threshold seed (`Sec2.Assembly3.measure_killedState_eq_of_entrance`). -/
theorem IsIntegratedSLEEvolution.measure_killedState_eq_assembled {a : ℝ}
    (ha : 0 < a := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ := by assumption)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ := by assumption)
    {n : ℕ} {ts : Fin n → ℝ≥0} {A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)}
    (hA : ∀ j, MeasurableSet (A j) := by assumption) :
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈
          A j} := by
  by_cases hcase : (∀ i j, xL i < xR j) ∨ ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exact IsIntegratedSLEEvolution.measure_killedState_eq_of_separated_or_threshold ha hcase h₁ h₂
      n ts A hA
  · rw [not_or] at hcase
    obtain ⟨hsep, hthr⟩ := hcase
    simp only [not_forall, not_lt] at hsep
    obtain ⟨i, j, hij⟩ := hsep
    have hi : xL i = 0 := le_antisymm (hF.2.1 i) (le_trans (hF.2.2.2 j) hij)
    have hj : xR j = 0 := le_antisymm (hij.trans (hF.2.1 i)) (hF.2.2.2 j)
    exact Sec2.Assembly3.measure_killedState_eq_of_entrance ha hF hi hj hthr h₁ h₂ n ts A hA

end InteractingSLE
