/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdStgEnc
import InteractingSLE.Spec.Supplement.GW2FbDual

/-!
# GW2's stage identity: decoding the stage record

Packet PROVE-GW2-RELDET, ruling R106. The stage step (`GW2Rd.ae_isStopDrvMatch_stage`) needs measurable decoders of the
stage record `x = stageEncRec c r l` (the Borel-encoded stage-start history). This file gives the two exact ones:

* `stgRecDec N x` — the counterflow record. It decodes to GB6's record `gb6Rec s W ζ` of the source
  (`stgRecDec_stageEncRec`; `cfRec = gb6Rec` definitionally). It is the decoder `σ` of the stage step.
* `stgPastDec N x` — the `N` stopped canonical piece records (`stgPastDec_stageEncRec`). The physical explored
  path up to the stage start is a measurable function of these: ROOT2's
  `RootJ31.joinedRecord` / `joinedRead`. This is the input of the remaining decoders `A` (relative start) and `pre`
  (relative prefix).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24

/-- The counterflow record of a stage record. -/
def stgRecDec (N : ℕ) (x : RecData) : RecData := ((stageEnc N).symm x).1

/-- The stopped piece records of a stage record. -/
def stgPastDec (N : ℕ) (x : RecData) : Fin N → RecData := ((stageEnc N).symm x).2

theorem measurable_stgRecDec (N : ℕ) : Measurable (stgRecDec N) :=
  measurable_fst.comp (stageEnc N).symm.measurable

theorem measurable_stgPastDec (N : ℕ) : Measurable (stgPastDec N) :=
  measurable_snd.comp (stageEnc N).symm.measurable

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The stage record decodes to GB6's counterflow record.** -/
theorem stgRecDec_stageEncRec (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (ω : Ω) : stgRecDec ((entryList l).length + 1) (stageEncRec c r l ω) = Supp8.GB6.gb6Rec c.s c.W c.ζ ω := by
  rw [stgRecDec, stageEnc_symm_stageEncRec]
  rfl

/-- **The stage record decodes to the stopped canonical pieces.** -/
theorem stgPastDec_stageEncRec (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (ω : Ω) : stgPastDec ((entryList l).length + 1) (stageEncRec c r l ω) =
      fun j : Fin ((entryList l).length + 1) => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j ω := by
  rw [stgPastDec, stageEnc_symm_stageEncRec]
  rfl

end InteractingSLE.Theorem14.GW2Rd
