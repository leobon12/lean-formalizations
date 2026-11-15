/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly3Entr
import InteractingSLE.Spec.Sec7.ContinuityProb4Aux113

/-!
# §7.3: the seed entrance of Aux. lemma 103 (`SeedEntranceStatement`)

Packet PROVE-SEC7-C6. Specification p. 350, `source/spec/p337-384.md` L305: "If `D_0 = 0`, both nearest groups begin
at the seed. An inadmissible initial group gives an immediate threshold and requires no continuation. Otherwise retain
those two admissible seed groups and delete all other initially separated marks up to a sufficiently small gap
cutoff, stopped also at physical time one. Their drift is bounded, and the assumed seed two-force-point result gives a
continuous initial prefix through this positive stopping time, unless termination occurs earlier."

The deletion and the identification with the two-seed law are PROVE-SEC2-PATCH4's
`Sec2.Assembly3.exists_twoSeed_cover` (built for Theorem 2.2's uniqueness): after a modification on a null set, under
the Girsanov measure `Q ~ P` that deletes the non-seed marks before the localization time `entT ∈ (0, 1]`, there is a
full two-seed evolution (seed weights the group sums) on the same space whose driver agrees with the given one before
`entT`. The two-seed premise gives it a continuous generating trace, which is a trace of the given driver on
`[0, entT/2]`; `P ≪ Q` transfers this back.

## Main results

* `exists_good_modification_ae`: PATCH4's `exists_good_modification` with the conclusion that the modification agrees
  with the evolution almost surely (pathwise), in place of the equality of killed finite-dimensional laws.
* **`seedEntranceStatement`**: `SeedEntranceStatement κ` for every `κ > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace Positive

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3 Girsanov

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-! ### A good modification that agrees with the evolution almost surely -/

open Classical in
/-- **A good modification of an evolution, pathwise equal to it almost surely** (the construction of
`Sec2.Assembly3.exists_good_modification`: changed on a null set, in the usual augmentation of the null augmentation;
every path is continuous before the lifetime, every Brownian path is continuous, the initial values hold for every `ω`,
the lifetime is positive, null sets are in every `𝓖 t`, `𝓖` is right-continuous; off the null set nothing
changes). -/
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
      ∀ᵐ ω ∂P, ζ' ω = ζ ω ∧ ∀ t, W' t ω = W t ω := by
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
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    simp only [hω, hζ', ↓reduceIte, implies_true, and_self]

/-! ### The seed entrance -/

/-- **`SeedEntranceStatement κ`** (Specification p. 350, Aux. lemma 103 when `D_0 = 0`), every `κ > 0`: under the
two-seed premise, an evolution of an ordered word with a left and a right mark at the seed almost surely has lifetime
`0` (an inadmissible seed group) or a continuous generating trace on some `[0, ε]`, `ε > 0`. -/
theorem seedEntranceStatement {κ : ℝ} (hκ : 0 < κ) : SeedEntranceStatement.{u} κ := by
  intro h2 nL nR xL xR ρL ρR hF hns Ω mΩ P _ 𝓕 W VL VR B ζ hE
  classical
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · filter_upwards [hE.ae_eq_zero_of_thresholdCondition] with ω h
    exact Or.inl (h hthr)
  -- the two seeds
  obtain ⟨pL, pR, hpL, hpR⟩ : ∃ (pL : Fin nL) (pR : Fin nR), xL pL = 0 ∧ xR pR = 0 := by
    push Not at hns
    obtain ⟨i, j, hij⟩ := hns
    exact ⟨i, j, le_antisymm (hF.2.1 i) (le_trans (hF.2.2.2 j) hij),
      le_antisymm (le_trans hij (hF.2.1 i)) (hF.2.2.2 j)⟩
  have : Nonempty (Fin nL ⊕ Fin nR) := ⟨Sum.inl pL⟩
  obtain ⟨hsL, hsR⟩ := (not_thr_iff_seedSum xL xR ρL ρR).1 hthr
  -- the gap level
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
  obtain ⟨δ, hδ, hδf⟩ := exists_pos_forall_lt f hfpos
  have hδL : ∀ i, xL i ≠ 0 → δ < -xL i := fun i hi => by
    have := hδf (Sum.inl i)
    simpa only [hf, Sum.elim_inl, hi, ↓reduceIte] using this
  have hδR : ∀ j, xR j ≠ 0 → δ < xR j := fun j hj => by
    have := hδf (Sum.inr j)
    simpa only [hf, Sum.elim_inr, hj, ↓reduceIte] using this
  -- a good modification, equal to the evolution almost surely
  obtain ⟨𝓖, h𝓖, W', VL', VR', B', ζ', hE', hWc, hVLc, hVRc, hBc, hW0, hVL0, hVR0, hζ0, hnull, hag⟩ :=
    exists_good_modification_ae hthr hE
  -- the Girsanov measure deleting the non-seed marks before `entT` is equivalent to `P`
  have hTle : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | entT δ xL xR ζ' W' VL' VR' ω ≤ s} :=
    measurableSet_entT_le hδ.le hE'.2.1 hE'.2.2.1 hE'.2.2.2.1 hWc hVLc hVRc
  have hTζ : ∀ ω, entT δ xL xR ζ' W' VL' VR' ω ≤ ζ' ω := entT_le_lifetime hδ.le
  have hT1 : ∀ ω, entT δ xL xR ζ' W' VL' VR' ω ≤ ((1 : ℝ≥0) : ℝ≥0∞) := fun ω => by
    rw [ENNReal.coe_one]; exact entT_le_one ω
  have hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < entT δ xL xR ζ' W' VL' VR' ω →
      (∀ i, seedW xL ρL i ≠ ρL i → δ ≤ |W' t ω - VL' i t ω|) ∧
        ∀ j, seedW xR ρR j ≠ ρR j → δ ≤ |W' t ω - VR' j t ω| := ae_of_all _ fun ω t ht => by
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
  obtain ⟨hQ, -⟩ := hE'.isSLEEvolutionUpTo.girsanov_changeWeights hκ (seedW xL ρL) (seedW xR ρR) hTle hTζ
    hT1 hδ hgap
  have h0gap : ∀ ω k, δ < gapFam δ xL xR W' VL' VR' k 0 ω := by
    rintro ω (i | j)
    · simp only [gapFam, Sum.elim_inl]
      split_ifs with hi
      · linarith
      · rw [hW0, hVL0]; linarith [hδL i hi]
    · simp only [gapFam, Sum.elim_inr]
      split_ifs with hj
      · linarith
      · rw [hW0, hVR0]; linarith [hδR j hj]
  have hT0 : ∀ ω, 0 < entT δ xL xR ζ' W' VL' VR' ω := fun ω =>
    entT_pos hδ.le (hWc ω) (fun i => hVLc i ω) (fun j => hVRc j ω) (hζ0 ω) (h0gap ω)
  -- the two-seed cover
  obtain ⟨Gw, Gl, Gr, ζG, hQp, hG, hobs⟩ := exists_twoSeed_cover hκ hF hδ hδL hδR hpL hpR hthr hE' hWc
    hVLc hVRc hBc hW0 hVL0 hVR0 hζ0 hnull
  have htr := h2 _ _ hsL hsR _ _ _ _ _ _ _ hG
  -- under `Q`, the driver has a trace on `[0, entT/2]`
  have hQev : ∀ᵐ ω ∂(girsanovMeasure P 𝓖 B' (weightDrift κ δ ρL (seedW xL ρL) ρR (seedW xR ρR)
      (entT δ xL xR ζ' W' VL' VR') ζ' W' VL' VR') (1 + 1)),
      ∃ ε : ℝ≥0, 0 < ε ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ε η := by
    filter_upwards [htr, Sec2.Assembly2.ae_lifetime_eq_top_twoSeed hκ hG hsL hsR, hobs, hG.2.2.2.2]
      with ω ⟨η, hη, _⟩ hζω hob hp
    have hGc : Continuous fun t => Gw t ω := by
      have h := hp.2.2.2.1
      rw [hζω] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    have hTeq := congrArg Prod.snd hob
    have hagree : ∀ t : ℝ≥0, (t : ℝ≥0∞) < entT δ xL xR ζ' W' VL' VR' ω → Gw t ω = W' t ω := by
      intro t ht
      have h1 := congrArg (fun e : ObsSpace nL nR => (e.1 t).1) hob
      have ht' : (t : ℝ≥0∞) < codeT δ xL xR (stCode ζG Gw Gl Gr (girsanovProcess B' (weightDrift κ δ ρL
          (seedW xL ρL) ρR (seedW xR ρR) (entT δ xL xR ζ' W' VL' VR') ζ' W' VL' VR')) ω) := by
        have : codeT δ xL xR (stCode ζG Gw Gl Gr (girsanovProcess B' (weightDrift κ δ ρL
            (seedW xL ρL) ρR (seedW xR ρR) (entT δ xL xR ζ' W' VL' VR') ζ' W' VL' VR')) ω) =
            entT δ xL xR ζ' W' VL' VR' ω := hTeq
        rw [this]; exact ht
      simp only [obsOfCode, observe, killed_of_lt ht, killed_of_lt ht'] at h1
      rw [← h1]
      have hcW : cW (stCode ζG Gw Gl Gr (girsanovProcess B' (weightDrift κ δ ρL (seedW xL ρL) ρR
          (seedW xR ρR) (entT δ xL xR ζ' W' VL' VR') ζ' W' VL' VR')) ω) = enc fun s => Gw s ω := by
        funext n k
        simp only [cW, stCode, enc]
        exact killed_of_lt (by rw [hζω]; exact ENNReal.coe_lt_top)
      simp only [codeW, hcW]
      exact (dec_enc hGc.continuousWithinAt).symm
    -- the horizon `entT/2`
    have hTfin : entT δ xL xR ζ' W' VL' VR' ω ≠ ⊤ := entT_ne_top ω
    have hpos : 0 < (entT δ xL xR ζ' W' VL' VR' ω).toNNReal := ENNReal.toNNReal_pos (hT0 ω).ne' hTfin
    have hεT : (((entT δ xL xR ζ' W' VL' VR' ω).toNNReal / 2 : ℝ≥0) : ℝ≥0∞) <
        entT δ xL xR ζ' W' VL' VR' ω := by
      conv_rhs => rw [← ENNReal.coe_toNNReal hTfin]
      exact ENNReal.coe_lt_coe.2 (half_lt_self hpos)
    refine ⟨(entT δ xL xR ζ' W' VL' VR' ω).toNNReal / 2, half_pos hpos, η, ?_⟩
    rw [hζω] at hη
    exact IsGeneratingTrace.congr_lt (IsGeneratingTrace.mono_horizon hη le_top) fun t ht =>
      (hagree t (lt_trans ht hεT)).symm
  -- back to `P` and to the original driver
  filter_upwards [hQ.ac'.ae_le hQev, hag] with ω ⟨ε, hε, η, hη⟩ ⟨_, hWW⟩
  exact Or.inr ⟨ε, hε, η, IsGeneratingTrace.congr_lt hη fun t _ => (hWW t).symm⟩

end Positive

end Sec7

end InteractingSLE
