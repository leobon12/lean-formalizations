/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Girs

/-!
# Theorem 2.2, existence for separated words and threshold seeds

Packet PROVE-SEC2-PATCH3. The frozen conclusion of `exists_isIntegratedSLEEvolution` for every
ordered force word that is separated (`∀ i j, xL i < xR j`: no mark at the driver on both sides) or
whose seed satisfies the threshold condition:

* threshold seed: the evolution with lifetime `0` (`isIntegratedSLEPath_of_threshold`);
* separated, non-threshold word: the maximal local solution driven by a Brownian motion with
  continuous paths, in the usual augmentation of its filtration (`Assembly2Life`), with positive
  horizons by Girsanov (`Assembly2Girs.hasPosLife`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly2

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-- **A threshold seed has the solution with lifetime `0`.** -/
theorem isIntegratedSLEPath_of_threshold (hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (b : ℝ≥0 → ℝ) :
    IsIntegratedSLEPath a xL xR ρL ρR (fun _ => 0) (fun i _ => xL i) (fun j _ => xR j) b 0 := by
  have hno : ∀ {t : ℝ≥0}, ¬ (t : ℝ≥0∞) < 0 := fun h => absurd h (not_lt.2 bot_le)
  have hnull : ∀ (f g : ℝ≥0 → ℝ),
      volume {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < 0 ∧ f r.toNNReal = g r.toNNReal} = 0 :=
    fun f g => by
      have : {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < 0 ∧ f r.toNNReal = g r.toNNReal} = ∅ :=
        eq_empty_of_forall_notMem fun r hr => hno hr.2.1
      rw [this, measure_empty]
  refine ⟨rfl, fun _ => rfl, fun _ => rfl, continuousOn_const, fun _ => continuousOn_const,
    fun _ => continuousOn_const, fun t ht => absurd ht hno, fun t ht => absurd ht hno,
    fun t ht => absurd ht hno, fun t ht => absurd ht hno, fun t ht => absurd ht hno,
    fun t ht => absurd ht hno, fun t ht => absurd ht hno, fun t ht => absurd ht hno,
    fun t ht => absurd ht hno, fun i => hnull (fun _ => 0) (fun _ => xL i),
    fun j => hnull (fun _ => 0) (fun _ => xR j), fun t ht => absurd ht hno, fun _ => hthr,
    fun T hT h0 => ?_⟩
  exact absurd (show (T : ℝ≥0∞) = 0 from h0) (by exact_mod_cast hT.ne')

/-- **Theorem 2.2, existence, threshold seed** (frozen conclusion; lifetime `0`). -/
theorem exists_isIntegratedSLEEvolution_of_threshold
    (hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, B, hB, -, -⟩ := OneForce.exists_filteredBrownian
  have hadapt : ∀ X : ℝ≥0 → Ω → ℝ, AdaptedBefore 𝓕 (fun _ => 0) X := fun X t A _ => by
    have : {ω : Ω | (t : ℝ≥0∞) < 0 ∧ X t ω ∈ A} = ∅ :=
      eq_empty_of_forall_notMem fun ω hω => absurd hω.1 (not_lt.2 bot_le)
    rw [this]
    exact @MeasurableSet.empty Ω (𝓕 t)
  exact ⟨Ω, mΩ, P, hP, 𝓕, fun _ _ => 0, fun i _ _ => xL i, fun j _ _ => xR j, B, fun _ => 0,
    hB, hadapt _, fun _ => hadapt _, fun _ => hadapt _,
    ae_of_all _ fun ω => isIntegratedSLEPath_of_threshold hthr _⟩

/-- **Theorem 2.2, existence, separated word** (frozen conclusion): for an ordered force word with
no mark at the driver on both sides, an integrated `SLE_a(ρ)` evolution exists. -/
theorem exists_isIntegratedSLEEvolution_of_separated (ha : 0 < a) (hF : IsOrderedForceWord xL xR)
    (hsep : ∀ i j, xL i < xR j) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exact exists_isIntegratedSLEEvolution_of_threshold hthr
  obtain ⟨Ω, mΩ, P, hP, 𝓕, B, hB, hBc, -⟩ := OneForce.exists_filteredBrownian
  have hBU := Ito.isFilteredBrownianReal_usualAugmentation hB
  have hBm : ∀ t, Measurable (B t) := fun t => (hB.2.1 t).mono (𝓕.le t) le_rfl
  have hpos : HasPosLife a ρL ρR P B :=
    hasPosLife ha hB.1.toIsPreBrownianReal (measurable_pi_iff.2 hBm)
  have hs : GoodWord ρL ρR ((xL, xR) : MWord nL nR) := ⟨hsep, hF, hthr⟩
  exact ⟨Ω, mΩ, P, hP, usualAugmentation 𝓕 P, _, _, _, B, _,
    isIntegratedSLEEvolution_codeProc hpos hs hBU hBc⟩

/-- **Theorem 2.2, existence, for every ordered force word without an admissible entrance**
(separated, or with a threshold seed). -/
theorem exists_isIntegratedSLEEvolution_of_separated_or_threshold (ha : 0 < a)
    (hF : IsOrderedForceWord xL xR)
    (hcase : (∀ i j, xL i < xR j) ∨ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ :=
  hcase.elim (exists_isIntegratedSLEEvolution_of_separated ha hF)
    exists_isIntegratedSLEEvolution_of_threshold

end Assembly2

end Sec2

end InteractingSLE
