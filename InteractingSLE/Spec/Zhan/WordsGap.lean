/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.AnnounceLifetime
import InteractingSLE.Spec.Zhan.SeparatedSeed

/-!
# The first time a gap falls below a level, capped at a horizon

Packet PROVE-ZHAN-B4. The localization of the whole-tail comparison: `minGap` is the smallest distance between the
driver and the marks (capped at `1`), `minGapStop G δ T` is the first time it falls below `δ`, capped at `T`, on a good
event `G` of the time-zero σ-algebra (and `0` off `G`). It is a stopping time of every right-continuous filtration in
which the state is adapted, it is at most `T`, and before it every gap is at least `δ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

open Coupling

variable {nL nR : ℕ}

/-- The gaps of a state, with a dummy entry `1`. -/
def gapOf (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : Option (Fin nL ⊕ Fin nR) → ℝ
  | none => 1
  | some (Sum.inl i) => |p.1 - p.2.1 i|
  | some (Sum.inr j) => |p.1 - p.2.2 j|

/-- The smallest gap between the driver and the marks, capped at `1`. -/
def minGap (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (gapOf p)

theorem continuous_minGap : Continuous (minGap (nL := nL) (nR := nR)) := by
  refine Continuous.finset_inf'_apply (f := fun k p => gapOf p k) _ fun k _ => ?_
  rcases k with _ | i | j
  · exact continuous_const
  · show Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => |p.1 - p.2.1 i|
    fun_prop
  · show Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => |p.1 - p.2.2 j|
    fun_prop

theorem le_minGap_iff {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} {δ : ℝ} :
    δ ≤ minGap p ↔ δ ≤ 1 ∧ (∀ i, δ ≤ |p.1 - p.2.1 i|) ∧ ∀ j, δ ≤ |p.1 - p.2.2 j| := by
  rw [minGap, Finset.le_inf'_iff]
  constructor
  · intro h
    exact ⟨h none (Finset.mem_univ _), fun i => h (some (Sum.inl i)) (Finset.mem_univ _),
      fun j => h (some (Sum.inr j)) (Finset.mem_univ _)⟩
  · rintro ⟨h1, hL, hR⟩ k -
    rcases k with _ | i | j
    · exact h1
    · exact hL i
    · exact hR j

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The first time the smallest gap falls below `δ`, on `G` (`⊤` off `G`). -/
def minGapHit (G : Set Ω) (δ : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) : Ω → WithTop ℝ≥0 := fun ω =>
  open Classical in
  if ω ∈ G then hitBelow (fun s => minGap (stateAt W VL VR s ω)) (ζ ω) δ else ⊤

/-- The gap time capped at the horizon `T` on `G`, and `0` off `G`. -/
def minGapStop (G : Set Ω) (δ : ℝ) (T : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) : Ω → ℝ≥0∞ := fun ω =>
  open Classical in
  if ω ∈ G then ((capTime (minGapHit G δ ζ W VL VR) T ω : ℝ≥0) : ℝ≥0∞) else 0

variable {G : Set Ω} {δ : ℝ} {T : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem minGapStop_le (ω : Ω) : minGapStop G δ T ζ W VL VR ω ≤ T := by
  unfold minGapStop
  split_ifs
  · have h := coe_capTime (minGapHit G δ ζ W VL VR) T ω
    have : (capTime (minGapHit G δ ζ W VL VR) T ω : WithTop ℝ≥0) ≤ T := by
      rw [h]; exact min_le_right _ _
    exact ENNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 this)
  · exact zero_le

theorem minGapStop_le_zeta (hG : ∀ ω ∈ G, ζ ω = ⊤) (ω : Ω) : minGapStop G δ T ζ W VL VR ω ≤ ζ ω := by
  by_cases hω : ω ∈ G
  · rw [hG ω hω]; exact le_top
  · simp [minGapStop, hω]

/-- On `G`, the capped gap time is `T` when the gaps stay at least `δ` on `[0, T]`. -/
theorem minGapStop_eq_of_le (hω : ω ∈ G)
    (hgap : ∀ s ≤ T, δ ≤ minGap (stateAt W VL VR s ω)) : minGapStop G δ T ζ W VL VR ω = T := by
  have hle : (T : WithTop ℝ≥0) ≤ minGapHit G δ ζ W VL VR ω := by
    simp only [minGapHit, hω, ↓reduceIte]
    refine le_hitBelow fun s _ hs => ?_
    by_contra hlt
    exact absurd (hgap s (not_le.1 hlt).le) (not_le.2 hs)
  have h := coe_capTime (minGapHit G δ ζ W VL VR) T ω
  rw [min_eq_right hle] at h
  simp only [minGapStop, hω, ↓reduceIte, WithTop.coe_eq_coe.1 h]

/-- Before the capped gap time every gap is at least `δ` (on `G`, with continuous state). -/
theorem le_minGap_of_lt_minGapStop (hω : ω ∈ G) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < minGapStop G δ T ζ W VL VR ω) (htζ : (t : ℝ≥0∞) < ζ ω) :
    δ ≤ minGap (stateAt W VL VR t ω) := by
  by_contra hlt
  push Not at hlt
  have h1 : minGapHit G δ ζ W VL VR ω ≤ t := by
    simp only [minGapHit, hω, ↓reduceIte]
    exact hitBelow_le htζ hlt
  have h := coe_capTime (minGapHit G δ ζ W VL VR) T ω
  have h2 : (capTime (minGapHit G δ ζ W VL VR) T ω : WithTop ℝ≥0) ≤ t := by
    rw [h]; exact (min_le_left _ _).trans h1
  have h3 : minGapStop G δ T ζ W VL VR ω ≤ t := by
    simp only [minGapStop, hω, ↓reduceIte]
    exact ENNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 h2)
  exact absurd ht (not_lt.2 h3)

/-- **The capped gap time is a stopping time** of a right-continuous filtration in which the state is adapted,
for a good event `G ∈ 𝓖₀` on which the state is continuous. -/
theorem measurableSet_minGapStop_le {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous]
    (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) (hG : MeasurableSet[𝓖 0] G)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω})
    (s : ℝ≥0) : MeasurableSet[𝓖 s] {ω | minGapStop G δ T ζ W VL VR ω ≤ s} := by
  have hst : IsStoppingTime 𝓖 (minGapHit G δ ζ W VL VR) := by
    classical
    exact isStoppingTime_hitBelow_state hW hVL hVR hG hGc continuous_minGap δ
  have hcap := (isStoppingTime_capTime hst T).measurableSet_le s
  have hGs : MeasurableSet[𝓖 s] G := 𝓖.mono (zero_le (a := s)) _ hG
  have e : {ω | minGapStop G δ T ζ W VL VR ω ≤ s} =
      (G ∩ {ω | (capTime (minGapHit G δ ζ W VL VR) T ω : WithTop ℝ≥0) ≤ s}) ∪ Gᶜ := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [minGapStop, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, true_and,
        mem_compl_iff, not_true_eq_false, or_false, ENNReal.coe_le_coe, WithTop.coe_le_coe]
    · simp [minGapStop, hω]
  rw [e]
  exact (hGs.inter hcap).union hGs.compl

end InteractingSLE.Zhan
