/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly3Entr

/-!
# Lemma DS3 in reach form, I: good modifications that agree with the evolution off a null set

Packet PROVE-T14-DS3. The landed `Sec2.Assembly3.exists_good_modification` (PROVE-SEC2-PATCH4) changes an evolution on
a null set, in the usual augmentation of its filtration, so that every path is continuous before the lifetime; it
records only that the killed finite-dimensional laws are unchanged. The reach events of DS2–DS3 involve whole paths, so
this file restates the same construction with the stronger conclusion that the modified processes agree with the
original ones off a null set (`exists_good_modification_eq`); the proof is the landed one.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace DS3Reach

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

open Classical in
/-- **A good modification of an evolution**: changed on a null set, in the usual augmentation,
every path is continuous before the lifetime, every Brownian path is continuous, the initial
values hold for every `ω`, the lifetime is positive, null sets are in every `𝓖 t`, and the killed
finite-dimensional laws are unchanged. -/
theorem exists_good_modification_eq (hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
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
      ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ ∀ ω, ω ∉ N → ζ' ω = ζ ω ∧ (∀ t, W' t ω = W t ω) ∧
        (∀ i t, VL' i t ω = VL i t ω) ∧ (∀ j t, VR' j t ω = VR j t ω) ∧
        IsIntegratedSLEPath a xL xR ρL ρR (W' · ω) (fun i t => VL' i t ω) (fun j t => VR' j t ω)
          (B' · ω) (ζ' ω) := by
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
    fun ω => ?_, hnull, N, hNm, hN0, fun ω hω => ?_⟩
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
  · have hω' : ω ∈ Nᶜ := hω
    simp only [hζ', hω, hω', ↓reduceIte, true_and]
    exact ⟨fun t => trivial, fun i t => trivial, fun j t => trivial, hpathω ω hω⟩

end DS3Reach

end Supp12

end InteractingSLE
