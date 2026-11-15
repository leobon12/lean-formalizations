/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzFill

/-!
# The retained past is determined by the records of the launched pieces

Packet PROVE-SB2-LCMEAN, round 15 (item 4, record matching). The relative past before stage `j`
(`Exist.Staged.pastMap`) is built stage by stage from the records of the launched pieces
(`Exist.StagedLaw.pastMap_succ`, `readRec_retained_succ`). Hence two families of regular drivers whose launched pieces
have the same records have the same retained past. Consequently, if every launched record is almost surely a
measurable function for a σ-algebra `𝓜`, then the retained past is contained in `𝓜` up to null sets:

* **`pastMap_eq_of_recOf_eq`** (deterministic);
* `comap_le_aeSigma_of_ae_eq`: a map almost surely equal to an `𝓜`-measurable one generates a σ-algebra contained in
  `𝓜` up to null sets;
* **`pastSigma_le_aeSigma_of_rec`**: the retained past before `k` is in `𝓜` up to null sets when a family `E'` of
  regular drivers measurable for `𝓜` has almost surely the same launched records as `E`.

All statements are standard (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Mz

open Exist Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **Families with the same launched records have the same retained past.** -/
theorem pastMap_eq_of_recOf_eq {Ω : Type*} (spec : ExplSpec) {E E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω} :
    ∀ {k : ℕ}, (∀ j < k, IsRegularDriver (E j ω)) → (∀ j < k, IsRegularDriver (E' j ω)) →
      (∀ i < k, (ExplState.run κ b jumps spec (fun j => E j ω) (i + 1)).2.2.2.1 i ≠ none →
        recOf (instrTime spec i) (E i ω) = recOf (instrTime spec i) (E' i ω)) →
      pastMap κ b jumps spec E k ω = pastMap κ b jumps spec E' k ω
  | 0, _, _, _ => funext fun i => Fin.elim0 i
  | k + 1, hr, hr', hrec => by
    have ih : pastMap κ b jumps spec E k ω = pastMap κ b jumps spec E' k ω :=
      pastMap_eq_of_recOf_eq spec (fun j hj => hr j (by omega)) (fun j hj => hr' j (by omega))
        fun i hi hl => hrec i (by omega) hl
    have hrun : ExplState.run κ b jumps spec (fun j => E j ω) k = ExplState.run κ b jumps spec (fun j => E' j ω) k :=
      run_eq_of_readRec_eq spec (fun j hj => hr j (by omega)) (fun j hj => hr' j (by omega))
        fun i hi => congrFun ih ⟨i, hi⟩
    have hl := launches_run_succ_of_run_eq spec hrun
    rw [pastMap_succ, pastMap_succ, ih, readRec_retained_succ, readRec_retained_succ]
    congr 1
    by_cases h : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none
    · have h' : (ExplState.run κ b jumps spec (fun j => E' j ω) (k + 1)).2.2.2.1 k = none := by
        rw [← congrFun hl k]; exact h
      simp only [h, h', ↓reduceIte]
    · have h' : (ExplState.run κ b jumps spec (fun j => E' j ω) (k + 1)).2.2.2.1 k ≠ none := by
        rw [← congrFun hl k]; exact h
      simp only [h, h', ↓reduceIte]
      exact hrec k (by omega) h

/-- A map almost surely equal to an `𝓜`-measurable one generates a σ-algebra contained in `𝓜` up to null sets. -/
theorem comap_le_aeSigma_of_ae_eq {Ω X : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace X] {μ : Measure Ω} {f g : Ω → X} (hg : Measurable[𝓜] g) (hfg : f =ᵐ[μ] g) :
    MeasurableSpace.comap f inferInstance ≤ LocalSets.aeSigma 𝓜 μ := by
  rintro A ⟨S, hS, rfl⟩
  refine ⟨g ⁻¹' S, hg hS, ?_⟩
  filter_upwards [hfg] with ω hω
  simp only [mem_preimage, hω]

/-- **The retained past is in `𝓜` up to null sets** when an `𝓜`-measurable family of regular drivers has almost
surely the same launched records. -/
theorem pastSigma_le_aeSigma_of_rec {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec) {E E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hE'm : ∀ j, Measurable[𝓜] (E' j))
    (hreg' : ∀ j ω, IsRegularDriver (E' j ω))
    (hrec : ∀ᵐ ω ∂μ, ∀ i < k, (ExplState.run κ b jumps spec (fun j => E j ω) (i + 1)).2.2.2.1 i ≠ none →
      recOf (instrTime spec i) (E i ω) = recOf (instrTime spec i) (E' i ω)) :
    pastSigma κ b jumps spec E k ≤ LocalSets.aeSigma 𝓜 μ := by
  rw [pastSigma_eq_comap]
  refine comap_le_aeSigma_of_ae_eq (g := pastMap κ b jumps spec E' k) ?_ ?_
  · let : MeasurableSpace Ω := 𝓜
    exact measurable_pastMap runMeasStatement hb spec (fun j _ => hE'm j) (fun j _ => hreg' j) k le_rfl
  · filter_upwards [hrec] with ω hω
    exact pastMap_eq_of_recOf_eq spec (fun j _ => hreg j ω) (fun j _ => hreg' j ω) hω

end InteractingSLE.Theorem14.SB.Mz
