/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootC24Data

/-!
# GW2's joint determination and ROOT2's retained histories

Packet PROVE-GW2-RELDET (orchestrator question: do JOINTDET R11's two properties for ROOT2's construction follow
from `GW2Rd.gw2JointDetC2Statement_of_thm12_thm13_mean_thr`?). The structural fact behind the answer, checked here:

* **`measurable_rootPiece_sigma`**: every retained σ-algebra of ROOT2's source, `c.sigma r l` (`rootSigma`, the
  stage-start σ-algebra), already at the EMPTY history `l = []` reads the root piece of the schedule (the canonical
  flow line of `h` from `rootPt r.1` at the root angle, stopped at the root switching time), besides the counterflow
  record (`measurable_cfRec_sigma`).

GW2's joint determination conditions on the counterflow record ALONE and its explored curve is the root flow line
itself (from `0`). The futures in JOINTDET R11's `RetainedStoppedSDEStatement` are the NEXT canonical pieces after a
retained history that contains the root piece, read in the counterflow's joint chart; so they are not instances of
the joint determination. See the handoff (round 7) for the exact ingredients the R11 property needs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open GW2TipSystem GW2TipSystem.RootC24

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Every retained history of ROOT2's source conditions on the counterflow record.** -/
theorem measurable_cfRec_sigma (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    Measurable[c.sigma r l] (cfRec c.s c.W c.ζ) :=
  measurable_fst.comp (comap_measurable _)

/-- **Every retained history of ROOT2's source, already the empty one, conditions on the root piece**: the record of
the root's canonical piece stopped at its switching time is `c.sigma r l`-measurable. -/
theorem measurable_rootPiece_sigma (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    Measurable[c.sigma r l] (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) 0) :=
  (measurable_pi_apply (⟨0, Nat.succ_pos _⟩ : Fin ((entryList l).length + 1))).comp
    (measurable_snd.comp (comap_measurable
      (stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ (schedSpecOf r.1 l) ((entryList l).length + 1))))

end InteractingSLE.Theorem14.GW2Rd
