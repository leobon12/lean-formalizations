/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkClock7Meas

/-!
# The inverse clock of a separated local horizon

Use the inverse clock before its image horizon and the original horizon after it.
The process is zero off the specified good event. This is the local version of
`Zhan.Retarget.newT`, without force-word indices or maximality.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Clock7

open Zhan.Retarget

/-- The inverse clock stopped at its original horizon, set to zero off the good event. -/
def inverseTime {Ω : Type*} (G : Set Ω) (a : ℝ) (W V : ℝ≥0 → Ω → ℝ)
    (T : Ω → ℝ≥0∞) (u : ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ G then
    if (u : ℝ≥0∞) < newHorizon a (W · ω) (V · ω) (T ω) then
      ((invClk (rate a (W · ω) (V · ω)) u).toNNReal : WithTop ℝ≥0)
    else toWT (T ω)
  else 0

variable {Ω : Type*} {G : Set Ω} {a : ℝ} {W V : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞}

/-- The stopped inverse never passes its original horizon on a separated path. -/
theorem inverseTime_le_horizon {ω : Ω} (hω : ω ∈ G) (ha : 0 < a)
    (hs : SepUpTo (W · ω) (V · ω) (T ω)) (u : ℝ≥0) :
    inverseTime G a W V T u ω ≤ toWT (T ω) := by
  unfold inverseTime
  split_ifs with hu
  · exact (coe_le_toWT_iff _ _).2 (invClk_lt hs ha hu).le
  · exact le_rfl

/-- The inverse clock increases on every sample, including the exceptional ones. -/
theorem inverseTime_mono (ha : 0 < a) (hs : ∀ ω ∈ G, SepUpTo (W · ω) (V · ω) (T ω))
    (u v : ℝ≥0) (huv : u ≤ v) (ω : Ω) :
    inverseTime G a W V T u ω ≤ inverseTime G a W V T v ω := by
  by_cases hω : ω ∈ G
  · have hsep := hs ω hω
    by_cases hv : (v : ℝ≥0∞) < newHorizon a (W · ω) (V · ω) (T ω)
    · have hu := (ENNReal.coe_le_coe.2 huv).trans_lt hv
      simp only [inverseTime, hω, ↓reduceIte, hu, hv, WithTop.coe_le_coe]
      apply (invClk_le_iff hsep ha hu (invClk_lt hsep ha hv)).2
      obtain ⟨s, -, -, -, hm, heq⟩ := newTime_spec hsep ha hv
      rw [Real.coe_toNNReal _ hm.1, heq]
      exact_mod_cast huv
    · simpa only [inverseTime, hω, hv, ↓reduceIte] using inverseTime_le_horizon hω ha hsep u
  · simp only [inverseTime, hω, ↓reduceIte, le_refl]

/-- The horizon is below `r` exactly when every time in a cofinal sequence is. -/
theorem horizon_le_iff {ω : Ω} {A : ℕ → Ω → ℝ≥0}
    (hb : ∀ n, (A n ω : ℝ≥0∞) < T ω)
    (hc : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T ω → ∃ n, s ≤ A n ω) (r : ℝ≥0) :
    T ω ≤ r ↔ ∀ n, A n ω ≤ r := by
  constructor
  · intro h n
    exact ENNReal.coe_le_coe.1 ((hb n).le.trans h)
  · intro h
    by_contra hlt
    obtain ⟨s, hrs, hs⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (not_le.1 hlt)
    obtain ⟨n, hn⟩ := hc s hs
    exact (not_lt_of_ge (hn.trans (h n))) (ENNReal.coe_lt_coe.1 hrs)

/-- The inverse stopping event only uses the stopped clocks of a cofinal sequence. -/
theorem inverseTime_le_iff {ω : Ω} (hω : ω ∈ G) (ha : 0 < a)
    (hs : SepUpTo (W · ω) (V · ω) (T ω)) {A : ℕ → Ω → ℝ≥0}
    (hb : ∀ n, (A n ω : ℝ≥0∞) < T ω)
    (hc : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T ω → ∃ n, s ≤ A n ω) (u r : ℝ≥0) :
    inverseTime G a W V T u ω ≤ r ↔ T ω ≤ r ∨
      ∃ n, (u : ℝ) ≤ clk (rate a (W · ω) (V · ω)) (min r (A n ω)) := by
  constructor
  · intro h
    by_cases hr : T ω ≤ r
    · exact Or.inl hr
    have hrT : (r : ℝ≥0∞) < T ω := not_le.1 hr
    right
    obtain ⟨n, hn⟩ := hc r hrT
    refine ⟨n, ?_⟩
    rw [min_eq_left (NNReal.coe_le_coe.2 hn)]
    by_cases hu : (u : ℝ≥0∞) < newHorizon a (W · ω) (V · ω) (T ω)
    · simp only [inverseTime, hω, hu, ↓reduceIte, WithTop.coe_le_coe] at h
      exact (invClk_le_iff hs ha hu hrT).1 h
    · simp only [inverseTime, hω, hu, ↓reduceIte] at h
      exact (hr ((toWT_le_coe_iff _ _).1 h)).elim
  · rintro (hr | ⟨n, hn⟩)
    · exact (inverseTime_le_horizon hω ha hs u).trans ((toWT_le_coe_iff _ _).2 hr)
    · have hrT : ((min r (A n ω) : ℝ≥0) : ℝ≥0∞) < T ω :=
        (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt (hb n)
      obtain ⟨h0, hlt⟩ := clk_lt_newHorizon' hs ha hrT
      have hu : (u : ℝ≥0∞) < newHorizon a (W · ω) (V · ω) (T ω) :=
        (ENNReal.coe_le_coe.2 ((Real.le_toNNReal_iff_coe_le h0).2 hn)).trans_lt hlt
      simp only [inverseTime, hω, hu, ↓reduceIte, WithTop.coe_le_coe]
      exact ((invClk_le_iff hs ha hu hrT).2 hn).trans (min_le_left _ _)

end InteractingSLE.Sec5.TwoMark.Clock7
