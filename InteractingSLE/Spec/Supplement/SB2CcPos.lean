/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YmSel
import InteractingSLE.Spec.Supplement.SB2CtStmt
import InteractingSLE.Spec.Supplement.SB2NcLive
import InteractingSLE.Spec.Supplement.SB2NeRoot
import InteractingSLE.Spec.Supplement.SB2CkEntr

/-!
# The root event lies in the positive relative roots

Packet PROVE-SB2-CANON, round 9 (the root branch of (P1)'s step). **`posRootAt_of_rootEv`**: on NOJUMP's walk facts
(`Nc.WalkGood`), a sample of the root event `Ne.rootEv ℓ` is a positive relative root at `ℓ` (`Ct.PosRootAt`): R has
entered by stage `ℓ` (otherwise the root would be a zero root, SB2LIFT's `Sz.zeroRoot_of_relOffEvent`), and since
`entrR < ζ_ℓ` the piece visits `R` (`Ck.entrTime_eq_life`), so `entrR` is the visit time, which is the relative shift
`shiftD 0` at `relOff = ℓ`. This is the converse of ROOTX's `Ro.rootEv_of_posRootAt`. **`ae_posRootAt_of_rootEv`**:
almost surely.

No probabilistic input besides the walk facts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Exist Exist.Staged Exist.StagedLaw Lk Mz

/-- **A sample of the root event is a positive relative root** (one sample, on the walk facts). -/
theorem posRootAt_of_rootEv {Ω : Type*} {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {ω : Ω}
    (hg : Nc.WalkGood κ b jumps E u l k ω) (hr : ω ∈ Ne.rootEv κ b jumps E u l k ℓ) :
    Ct.PosRootAt (κ := κ) b jumps E u l k ℓ ω := by
  classical
  obtain ⟨⟨-, hl⟩, hrel, hZ, hentr⟩ := hr
  have hro := Nc.relOffEvent_of_walkGood hg
  rw [hrel] at hro
  have hent : Ent κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ := by
    by_contra hne
    exact hZ (Sz.zeroRoot_of_relOffEvent hro hne)
  have hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ∧
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) t =
        ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) := by
    by_contra hv
    have he : Nd.entrR κ b jumps E u l k ℓ ω = (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 :=
      Ck.entrTime_eq_life hv
    rw [he] at hentr
    exact lt_irrefl _ hentr
  have he : Nd.entrR κ b jumps E u l k ℓ ω = (visitTime (ExplState.run κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) (realMax (upperPrefix κ b jumps E u l k ω)) :
      ℝ≥0∞) :=
    Ck.entrTime_eq_visitTime hvis
  have hsh : (shiftD κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) 0 : ℝ≥0∞) =
      (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) (realMax (upperPrefix κ b jumps E u l k ω)) :
        ℝ≥0∞) := by
    unfold shiftD
    rw [ite_eq_left rfl, hrel]
  refine ⟨hl, ⟨hent, hrel⟩, ?_⟩
  change (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 - (shiftD κ (-(Real.pi / 2)) b jumps
    (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) 0 :
    ℝ≥0∞) ≠ 0
  rw [hsh, ← he]
  exact (tsub_pos_iff_lt.2 hentr).ne'

end InteractingSLE.Theorem14.SB.Cz
