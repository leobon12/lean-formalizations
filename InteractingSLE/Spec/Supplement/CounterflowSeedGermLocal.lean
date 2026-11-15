/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly3Entr
import InteractingSLE.Spec.Supplement.LPAssembly

/-!
# Germ properties of a seeded word are those of its two-seed word

Packet PROVE-CFNORETURN2 (PROVE-CFNORETURN §5 step 1, "localization to the seed-only word"). Let `E` be an integrated
`SLE_a(ρ)` evolution of an ordered force word with a left and a right mark at `0` and infinite lifetime. Its seed groups
have total weights `ρ⁰_L = seedSum xL ρL`, `ρ⁰_R = seedSum xR ρR` (both `> −2`: the seed is not a threshold state).
A property `Φ` of driving paths that only depends on the germ of the path at time `0` (`hΦ`) and that holds almost
surely for every evolution of the two-seed word `SLE_a(ρ⁰_L; ρ⁰_R)` holds almost surely for `E` (`ae_of_twoSeed`).

The proof is the localization of Theorem 2.2's uniqueness proof (`Sec2.Assembly3`, PROVE-SEC2-PATCH4): after a good
modification on a null set, the Girsanov change that removes the weights of the non-seed marks up to the positive
localization time `T` (the first time a non-seed mark comes within `δ` of the driver, capped at `1`) gives an equivalent
measure `Q` under which the merged seeds form a local two-seed evolution up to `T`; continued after `T` by the maximal
solution, it is a two-seed evolution `G` under `Q` whose driver agrees with the driver of `E` on `[0, T)`. So `Φ` holds
`Q`-almost surely for the driver of `G`, hence for the driver of `E`, and `P ≪ Q` transfers it to `P`.

* `exists_good_modification_ae`: `Sec2.Assembly3.exists_good_modification`, recording that the modified driver agrees
  with the original one almost surely (instead of the equality of killed laws);
* `exists_twoSeed_agree`: `Sec2.Assembly3.exists_twoSeed_cover`, recording `P ≪ Q` and the agreement of the drivers
  before the localization time (instead of the identification of observations);
* **`ae_of_twoSeed`**: the transfer.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.CfNoReturn.Germ

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-! ### A good modification that agrees with the evolution almost surely -/

open Classical in
/-- **A good modification of an evolution** (`Sec2.Assembly3.exists_good_modification`): changed on a null set, in the
usual augmentation, every path is continuous before the lifetime, every Brownian path is continuous, the initial
values hold for every `ω`, the lifetime is positive, null sets are in every `𝓖 t`, and the modified driver agrees with
the original one almost surely. -/
theorem exists_good_modification_ae (hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
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
      ∀ᵐ ω ∂P, ∀ t, W' t ω = W t ω := by
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
    fun ω => ?_, hnull, ?_⟩
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
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω t
    simp only [hω, ↓reduceIte]

/-! ### The two-seed evolution under the changed measure, agreeing with the driver before the stop -/

section Cover

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The two-seed cover, with agreement of the drivers** (`Sec2.Assembly3.exists_twoSeed_cover`, same proof). For a
good evolution of an admissible entrance there are an equivalent probability measure `Q` (`P ≪ Q`) and a two-seed
evolution under `Q`, with the seed weights, whose driver agrees `Q`-almost surely with the driver of the evolution on
an initial interval `[0, ε)`, `ε > 0`. -/
theorem exists_twoSeed_agree (ha : 0 < a) (hF : IsOrderedForceWord xL xR) {δ : ℝ} (hδ : 0 < δ)
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
    ∃ (Q : Measure Ω) (_ : IsProbabilityMeasure Q) (Gw : ℝ≥0 → Ω → ℝ) (Gl Gr : Fin 1 → ℝ≥0 → Ω → ℝ)
      (Bh : ℝ≥0 → Ω → ℝ) (ζG : Ω → ℝ≥0∞), P ≪ Q ∧
      IsIntegratedSLEEvolution a (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
        (fun _ => seedSum xL ρL) (fun _ => seedSum xR ρR) Q 𝓖 Gw Gl Gr Bh ζG ∧
      ∀ᵐ ω ∂Q, ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s : ℝ≥0, s < ε → Gw s ω = W s ω := by
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
  refine ⟨Q, hQp, _, _, _, Bh, _, hQ.ac', hG, ?_⟩
  filter_upwards [hN₂Q] with ω hω
  refine ⟨Tn ω, hTn0 ω, fun s hs => ?_⟩
  show concatAt (Tn ω) (Ws · ω) _ _ s = W s ω
  rw [concatAt_of_lt hs]
  exact hsEq hω s hs.le

end Cover

/-! ### The transfer -/

/-- An evolution with infinite lifetime almost surely does not start at a threshold state. -/
theorem not_thresholdCondition_of_ae_top {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := fun h => by
  obtain ⟨ω, h1, h2⟩ := (hE.ae_eq_zero_of_thresholdCondition.and hζ).exists
  rw [h1 h] at h2
  exact ENNReal.zero_ne_top h2

/-- **Localization of a germ property to the two-seed word.** For an evolution of an ordered word with a left and a
right mark at `0` and infinite lifetime, a property `Φ` of continuous driving paths from `0` that only depends on the
germ of the path at time `0`, and that holds almost surely for every evolution (on the same sample space) of the
two-seed word with the seed weights `seedSum xL ρL`, `seedSum xR ρR`, holds almost surely for the driver. -/
theorem ae_of_twoSeed (ha : 0 < a) (hF : IsOrderedForceWord xL xR) {pL : Fin nL} {pR : Fin nR}
    (hpL : xL pL = 0) (hpR : xR pR = 0) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {Φ : (ℝ≥0 → ℝ) → Prop}
    (hΦ : ∀ w w' : ℝ≥0 → ℝ, Continuous w → Continuous w' → w 0 = 0 → w' 0 = 0 →
      (∃ ε : ℝ≥0, 0 < ε ∧ ∀ s : ℝ≥0, s < ε → w s = w' s) → Φ w → Φ w')
    (h2 : ∀ (Q : Measure Ω) [IsProbabilityMeasure Q] (𝓖 : Filtration ℝ≥0 mΩ) (Gw : ℝ≥0 → Ω → ℝ)
      (Gl Gr : Fin 1 → ℝ≥0 → Ω → ℝ) (Bh : ℝ≥0 → Ω → ℝ) (ζG : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a LP.twoSeedXL LP.twoSeedXR (fun _ => seedSum xL ρL) (fun _ => seedSum xR ρR) Q 𝓖
        Gw Gl Gr Bh ζG → ∀ᵐ ω ∂Q, Φ (fun t => Gw t ω)) :
    ∀ᵐ ω ∂P, Φ (fun t => W t ω) := by
  classical
  -- the seed is not a threshold state
  have hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := not_thresholdCondition_of_ae_top hE hζ
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
  -- the good modification and the two-seed cover
  obtain ⟨𝓖, h𝓖, W', VL', VR', B', ζ', hE', hW'c, hVL'c, hVR'c, hB'c, hW'0, hVL'0, hVR'0, hζ'0, hnull,
    hWW'⟩ := exists_good_modification_ae hthr hE
  obtain ⟨Q, hQ, Gw, Gl, Gr, Bh, ζG, hPQ, hG, hag⟩ := exists_twoSeed_agree ha hF hδ hδL hδR hpL hpR hthr hE'
    hW'c hVL'c hVR'c hB'c hW'0 hVL'0 hVR'0 hζ'0 hnull
  have hΦG := h2 Q 𝓖 Gw Gl Gr Bh ζG hG
  have hGc : ∀ᵐ ω ∂Q, Continuous (fun t => Gw t ω) := by
    filter_upwards [Sec2.Assembly2.ae_lifetime_eq_top_twoSeed ha hG hsL hsR, hG.2.2.2.2] with ω hζω hp
    rw [hζω] at hp
    exact continuousOn_univ.1 (by simpa using hp.2.2.2.1)
  filter_upwards [hPQ.ae_le hΦG, hPQ.ae_le hag, hPQ.ae_le hGc, hζ, hE.2.2.2.2, hWW'] with ω hφ ⟨ε, hε, hεag⟩
    hgc hζω hp hww'
  rw [hζω] at hp
  have hwc : Continuous fun t => W t ω := continuousOn_univ.1 (by simpa using hp.2.2.2.1)
  have hw0 : W 0 ω = 0 := hp.1
  refine hΦ _ _ hgc hwc ?_ hw0 ⟨ε, hε, fun s hs => (hεag s hs).trans (hww' s)⟩ hφ
  rw [hεag 0 hε, hww' 0, hw0]

end InteractingSLE.CfNoReturn.Germ
