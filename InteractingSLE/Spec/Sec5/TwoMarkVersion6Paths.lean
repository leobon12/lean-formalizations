/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Girs
import InteractingSLE.Spec.Sec5.TwoMarkRegular5Barrier

/-!
# Continuous versions of an announced local image evolution

The existing local null-set modification is exposed with continuity of every
force coordinate and simultaneous almost-sure agreement of the entire paths.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Version6

/-- The same announced stops remain stopping times in the usual augmentation. -/
theorem isAnnouncingSeq_usualAugmentation {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {e : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0}
    (hT : Coupling.IsAnnouncingSeq 𝓕 P e T) :
    Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P e T :=
  ⟨fun n t => (Ito.le_usualAugmentation 𝓕 P t) _ (hT.1 n t), hT.2⟩

/-- The local null-set modification, retaining agreement and continuity of all coordinates. -/
theorem exists_continuous_state_modification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {a : ℝ} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {e : Ω → ℝ≥0∞}
    (hE : Sec2.IsSLEEvolutionUpTo a xL xR ρL ρR P 𝓕 W VL VR B e) :
    ∃ (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR' : Fin nR → ℝ≥0 → Ω → ℝ),
      Sec2.IsSLEEvolutionUpTo a xL xR ρL ρR P (usualAugmentation 𝓕 P) W' VL' VR' B e ∧
      (∀ ω, ContinuousOn (W' · ω) {t | (t : ℝ≥0∞) < e ω}) ∧
      (∀ i ω, ContinuousOn (VL' i · ω) {t | (t : ℝ≥0∞) < e ω}) ∧
      (∀ j ω, ContinuousOn (VR' j · ω) {t | (t : ℝ≥0∞) < e ω}) ∧
      ∀ᵐ ω ∂P, (W' · ω) = (W · ω) ∧
        (fun i t => VL' i t ω) = (fun i t => VL i t ω) ∧
        (fun j t => VR' j t ω) = (fun j t => VR j t ω) := by
  classical
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hE.ae_path)
  have hgood : ∀ ω, ω ∉ N → Sec2.IsSLEPathUpTo a xL xR ρL ρR
      (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (e ω) := by
    intro ω hω
    by_contra hp
    exact hω (hNsub hp)
  refine ⟨fun t ω => if ω ∈ N then 0 else W t ω,
    fun i t ω => if ω ∈ N then xL i else VL i t ω,
    fun j t ω => if ω ∈ N then xR j else VR j t ω, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Ito.isFilteredBrownianReal_usualAugmentation hE.brownian,
      Sec2.IsSLEEvolutionUpTo.adaptedBefore_ite_null hE.adapted_W hNm hN0 0,
      fun i => Sec2.IsSLEEvolutionUpTo.adaptedBefore_ite_null (hE.adapted_VL i) hNm hN0 (xL i),
      fun j => Sec2.IsSLEEvolutionUpTo.adaptedBefore_ite_null (hE.adapted_VR j) hNm hN0 (xR j), ?_⟩
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    simpa only [hω, ↓reduceIte] using hgood ω hω
  · intro ω
    by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]; exact continuousOn_const
    · simpa only [hω, ↓reduceIte] using (hgood ω hω).continuousOn_w
  · intro i ω
    by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]; exact continuousOn_const
    · simpa only [hω, ↓reduceIte] using (hgood ω hω).continuousOn_vL i
  · intro j ω
    by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]; exact continuousOn_const
    · simpa only [hω, ↓reduceIte] using (hgood ω hω).continuousOn_vR j
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    simp only [hω, ↓reduceIte, and_self]

end InteractingSLE.Sec5.TwoMark.Version6
