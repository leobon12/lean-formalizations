/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BfJ32Cross
import InteractingSLE.Spec.Supplement.GW2BfJ32Slow

/-!
# J32's start at alive histories and in live form (S2, S4)

Packet PROVE-GW2-BUF. Two inputs of PROVE-GW2-SDE's `RootPairInputsSched` concern J32's start value
`GW2Sdh.rootStart32`.

* **The shell (S4).** At every alive nonempty history the start of every candidate lies in `(−9/4, −7/4)`
  (`ae_rootStart32_mem_of_alive`): it is minus the passed reading (`ae_sourceDriver_cons_zero_all`), and the passed
  reading lies in the band `(7/4, 9/4)`. This is the start clause of `startsU` in `GW2Sdg.ShellFact`.
* **The frozen start (S2) in live form.** `rootStartFrozen32_live`: for a time-ordered history, the start equals the
  retained functional `histStart` at every live sample of every candidate (`ae_j32Start_eq_histStart`). SDE's
  `RootStartFrozen32` asks this on the WHOLE gate. Its consumer, the read clause of the slow buffer fact, is vacuous at
  dead samples, so the live form suffices there (handoff).
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bf

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24

variable {Ω : Type u} [MeasurableSpace Ω]

/-- SDE's J32 start value is this file's `j32Start`. -/
theorem rootStart32_eq_j32Start (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (ξ : Ω) : GW2Sdh.rootStart32 c r l a ξ = j32Start c r l a ξ := rfl

/-- **SDE's J32 start value is the stage driver at `0`.** -/
theorem rootStart32_eq_sourceDriver_zero (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ξ : Ω) :
    GW2Sdh.rootStart32 c r l a ξ = RootJ32.sourceDriver c r l a ξ 0 := by
  change _ = (-1) ^ l.length * (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) * (RootJ32.capacityDriverRead (rootPt r.1) c.s
    (RootJ31.historyTime c r l + RootJ31.candidateCap c r a)
    ((RootH29.forwardCapacity (rootPt r.1) c.s (RootJ31.historyTime c r l)
      (RootJ31.futurePair c r l a ξ)).toNNReal + 0 / ((2 : ℝ≥0) ^ r.2) ^ 2) (RootJ31.futurePair c r l a ξ) - _)
  rw [zero_div, add_zero]
  rfl

/-- **At every alive nonempty history, every candidate's start lies in `(−9/4, −7/4)`** (Theorem 1.3 for the live
clock). -/
theorem ae_rootStart32_mem_of_alive [StandardBorelSpace Ω] (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (x : EntryIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) (x :: l) →
      GW2Sdh.rootStart32 c r (x :: l) a ω ∈ Ioo (-(9 / 4)) (-(7 / 4)) := by
  filter_upwards [ae_sourceDriver_cons_zero_all h13 c r] with ω hcross x l a halive
  obtain ⟨hl, hx⟩ := halive
  obtain ⟨a₀, ha₀⟩ := mem_iUnion.1 hx
  obtain ⟨hang, htest⟩ := mem_iUnion.1 ha₀
  have hxe : x = (RootJ31.candidateAngle c r a₀, x.2) := Prod.ext hang.symm rfl
  have hband : RootJ32.sourceX c r l a₀ ω (x.2 : ℝ≥0) ∈ Ioo (7 / 4) (9 / 4) := htest.2.2.2
  rw [rootStart32_eq_sourceDriver_zero, hxe, hcross l a₀ x.2 a hl htest]
  exact ⟨by linarith [hband.2], by linarith [hband.1]⟩

/-- **The frozen start in live form**: for a time-ordered history there is a retained functional equal, almost surely
on the gate, to every candidate's start at every live sample. -/
theorem rootStartFrozen32_live [StandardBorelSpace Ω] (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (hord : Sec5.Prop513Schedule.TimeOrdered 0 (RootJ31.historyProgram c r l)) :
    ∃ S : Ω → ℝ, Measurable[c.sigma r l] S ∧ ∀ᵐ ξ ∂c.P, ∀ a, 0 < (RootJ32.sourceSample c r l a ξ).1 →
      GW2Sdh.rootStart32 c r l a ξ = S ξ := by
  refine ⟨histStart c r l, measurable_histStart c r l, ?_⟩
  filter_upwards [ae_j32Start_eq_histStart h13 c r l (v0_le_historyTime c r l hord)] with ξ h a hlive
  rw [rootStart32_eq_j32Start]
  exact h a (hlive.trans_eq (RootJ32.sourceSample_fst c r l a ξ))

end InteractingSLE.Theorem14.GW2Bf
