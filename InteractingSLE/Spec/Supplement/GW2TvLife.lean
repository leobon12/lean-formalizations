/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmClaimS
import InteractingSLE.Spec.Supplement.GW2TrCap
import InteractingSLE.Spec.Supplement.GW2TlDeath

/-!
# Claim(k), piece (R1): the prefix candidate of an entry's angle is alive up to the entry's end

Packet PROVE-GW2-RELDET (round 33), for PROVE-GW2-STAGEMEAN's Claim(k) step (STAGEMEAN's handoff, "For RELDET").
Let `e :: l'` be a history and `a'` a candidate of `e`'s angle whose cap reaches past `e`'s end. In the history's
program the entry `e` is the canonical piece of its angle after the pieces of `l'`, stopped at the entry's duration
`δ = T − T'`. The prefix candidate's piece is the SAME canonical drive (same earlier pieces, same angle: RELDET's
`canonDrive_congr_angle`), so the history's success (the entry's death flag is `false`, i.e. `δ < ζ`) says that the
prefix candidate lives past `δ`:

* `specDelta_hist_last`: the entry's duration in the history's program is `T − T'`;
* `canonDrive_hist_last_eq`: the entry's canonical drive is the prefix candidate's current piece;
* **`prefixLifeStatement`**: `GW2Psm.PrefixLifeStatement` (every sample).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31

section Life

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)

/-- **The entry's duration in the history's program** is the entry's end minus the prefix's end. -/
theorem specDelta_hist_last (θe : c.Θ) (qe : c.Q) (l' : List (EntryIdx c.Θ c.Q)) :
    specDelta (schedSpec (rootPt r.1) (historyProgram c r ((θe, qe) :: l'))) (historyProgram c r l').length =
      (((historyTime c r ((θe, qe) :: l') - historyTime c r l' : ℝ≥0)) : ℝ≥0∞) := by
  rw [historyProgram_cons c r l' θe qe, RootH29.specDelta_last, Gm.historyTime_cons c r l' θe qe]
  rfl

/-- **The entry's canonical drive is the prefix candidate's current piece** (candidate of the entry's angle). -/
theorem canonDrive_hist_last_eq (θe : c.Θ) (qe : c.Q) (l' : List (EntryIdx c.Θ c.Q)) (a' : ℕ)
    (hθ : candidateAngle c r a' = (θe : ℝ)) (ω : Ω) :
    canonDrive c.hκ c.h12p c.βA c.c₀ (rootPt r.1)
        (specAngle (schedSpec (rootPt r.1) (historyProgram c r ((θe, qe) :: l'))))
        (specDelta (schedSpec (rootPt r.1) (historyProgram c r ((θe, qe) :: l')))) (c.h ω)
        (historyProgram c r l').length =
      GW2Olm.futFam c r l' a' (GW2Olm.curIdx c r l') ω := by
  have hH := historyProgram_cons c r l' θe qe
  refine canonDrive_congr_angle c.hκ c.h12p c.βA c.c₀ (rootPt r.1) (c.h ω) (fun j hj => ?_) (fun j hj => ?_)
  · rcases lt_or_eq_of_le hj with hj | rfl
    · rw [hH, specAngle_schedSpec_append _ _ hj]
      change _ = specAngle (schedSpec (rootPt r.1) (historyProgram c r l' ++ _)) j
      rw [specAngle_schedSpec_append _ _ hj]
    · rw [hH, RootH29.specAngle_last]
      change _ = specAngle (schedSpec (rootPt r.1) (historyProgram c r l' ++ _)) _
      rw [RootH29.specAngle_last, hθ]
  · rw [hH, specDelta_schedSpec_append _ _ hj]
    change _ = specDelta (schedSpec (rootPt r.1) (historyProgram c r l' ++ _)) j
    rw [specDelta_schedSpec_append _ _ hj]

/-- **(R1) The prefix candidate of an entry's angle is alive up to the entry's end** on the history's success (every
sample): `GW2Psm.PrefixLifeStatement`. -/
theorem prefixLifeStatement : GW2Psm.PrefixLifeStatement.{u} := by
  intro Ω _ c r e l' a' hθ _ ω hold
  obtain ⟨θe, qe⟩ := e
  have hH := historyProgram_cons c r l' θe qe
  have hj : (historyProgram c r l').length < (historyProgram c r ((θe, qe) :: l')).length := by
    rw [hH, List.length_append, List.length_singleton]
    exact Nat.lt_succ_self _
  have hflag := hold ⟨(historyProgram c r l').length, hj⟩
  change (recOf (specDelta (schedSpec (rootPt r.1) (historyProgram c r ((θe, qe) :: l')))
      (historyProgram c r l').length)
    (canonDrive c.hκ c.h12p c.βA c.c₀ (rootPt r.1)
      (specAngle (schedSpec (rootPt r.1) (historyProgram c r ((θe, qe) :: l'))))
      (specDelta (schedSpec (rootPt r.1) (historyProgram c r ((θe, qe) :: l')))) (c.h ω)
      (historyProgram c r l').length)).2.2 = false at hflag
  rw [Sec7.StripSideHeightProb.recOf_flag_eq_false_iff, specDelta_hist_last c r θe qe l',
    canonDrive_hist_last_eq c r θe qe l' a' hθ ω] at hflag
  exact hflag

end Life

end InteractingSLE.Theorem14.GW2Rd
