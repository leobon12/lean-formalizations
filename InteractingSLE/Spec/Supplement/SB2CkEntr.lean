/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwStage0
import InteractingSLE.Spec.Supplement.SB2CjK2

/-!
# The entrance time at `R` with a stopping convention

Packet PROVE-SB2-CONDFIN (round 5; root route, step 1). `Lk.visitTime` (hence `Na.rootEntry`) is `0` when the piece
never visits `R`, so `{rootEntry ≤ r}` contains every sample whose piece never reaches `R` — an event the piece
capped at `r` cannot decide. The entrance time used for the root line family must therefore carry a stopping convention:

* **`entrTime s e R`**: the first visit of `R` if the piece visits it (before or at its lifetime), the lifetime
  otherwise;
* **`entrTime_le_iff`**: for a launched regular piece, `entrTime ≤ r` iff the piece visits `R` by time `min r ζ`, or
  its lifetime is at most `r` — information of the piece capped at `r` (its record capped at `r` knows `min r ζ`, the
  flag `ζ ≤ r` and the points up to `min r ζ`);
* `entrTime_eq_visitTime`: on a visit it is `Lk.visitTime` (so `Na.rootEntry` on the root event).

Deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Ck

open Exist Exist.Staged Exist.StagedLaw Lk GW1W LuM

open Classical in
/-- **The entrance time at `R` with a stopping convention**: the first visit of `R` if the piece visits it, its
lifetime otherwise. -/
def entrTime (s : ExplState) (e : Drv) (R : ℝ) : ℝ≥0∞ :=
  if ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ e.2 ∧ pcPt s e t = (R : ℂ) then (visitTime s e R : ℝ≥0∞) else e.2

theorem entrTime_eq_visitTime {s : ExplState} {e : Drv} {R : ℝ}
    (h : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ e.2 ∧ pcPt s e t = (R : ℂ)) : entrTime s e R = visitTime s e R := by
  classical
  unfold entrTime
  rw [ite_eq_left h]

theorem entrTime_eq_life {s : ExplState} {e : Drv} {R : ℝ}
    (h : ¬ ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ e.2 ∧ pcPt s e t = (R : ℂ)) : entrTime s e R = e.2 := by
  classical
  unfold entrTime
  rw [ite_eq_right h]

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- **The entrance time is decided by the piece capped at `r`**: for a launched piece of a walk with regular launches,
`entrTime ≤ r` iff the piece visits `R` by time `min r ζ` or its lifetime is at most `r`. -/
theorem entrTime_le_iff (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) (R : ℝ)
    (r : ℝ≥0∞) :
    entrTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R ≤ r ↔
      (∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ min r (D n).2 ∧
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = (R : ℂ)) ∨
        (D n).2 ≤ r := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  by_cases hv : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 ∧ pcPt s (D n) t = (R : ℂ)
  · obtain ⟨hτζ, hτR, hτmin⟩ := visitTime_spec hP hl hv
    rw [entrTime_eq_visitTime hv]
    constructor
    · intro hτ
      exact Or.inl ⟨visitTime s (D n) R, le_min hτ hτζ, hτR⟩
    · rintro (⟨t, ht, htR⟩ | hζ)
      · exact (ENNReal.coe_le_coe.2 (hτmin t (ht.trans (min_le_right _ _)) htR)).trans (ht.trans (min_le_left _ _))
      · exact hτζ.trans hζ
  · rw [entrTime_eq_life hv]
    constructor
    · exact Or.inr
    · rintro (⟨t, ht, htR⟩ | hζ)
      · exact absurd ⟨t, ht.trans (min_le_right _ _), htR⟩ hv
      · exact hζ

end InteractingSLE.Theorem14.SB.Ck
