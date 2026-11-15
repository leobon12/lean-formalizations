/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxKer

/-!
# GW2's open lines: the launch chart of the current piece is a domain chart

Packet PROVE-GW2-STAGEMEAN, R121 round. Almost surely, at a launch `(cL, θ)` of the current piece of the actual
schedule (any root), `cL` is a domain chart of its own domain (`SB.Lw.isDomainChart_runChart` on the run's success):

* **`ae_isDomainChart_curLaunch`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open LocalSets WholeField Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Sdi Restart.MarkovChart GW4Fix GW4Fix.CLoc Sec5.Prop513Schedule GW2Rd

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The launch chart of the current piece is a domain chart of its domain**, almost surely. -/
theorem ae_isDomainChart_curLaunch (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω₀ ∂c.P, ∀ (cL : Chart) (θ : ℝ), GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) →
      IsDomainChart (cL.dom : Set ℂ) cL := by
  set x := rootPt r.1 with hx
  set L := futureProgram c r l a with hL
  set spec := GW2Olm.futSpec c r l a with hspec
  set E := GW2Olm.futFam c r l a with hEdef
  set k := GW2Olm.curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := fun j ω =>
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x (specAngle spec) (specDelta spec) (c.h ω) j
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS hreg
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  filter_upwards [hR.ae_pieceRegular] with ω₀ hpr
  intro cL θ hl
  obtain ⟨-, -, hcL⟩ := eq_launch_of_launches (κ := c.κ) (b := c.b) (jumps := c.jumps) spec (fun j => E j ω₀) hl
  have hs : AllSucc (specDelta spec) (fun j => E j ω₀) k := by
    by_contra hn
    have h0 := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl (isFlowProg_spec x true L)
      (specDelta_ne_top _) (fun j => E j ω₀) (show k < spec.2.2.length by omega)).2 hn
    have h1 : GW2Olm.curLaunch c r l a ω₀ = none := h0
    rw [h1] at hl
    simp at hl
  have hlive := ((run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl (isFlowProg_spec x true L)
    (specDelta_ne_top _) (fun j => E j ω₀) k (by omega)).1 hs).1
  have hnot : stStatus (ExplState.run c.κ c.b c.jumps spec (fun j => E j ω₀) k) ≠ GW1Conn.stDone := by
    rcases hlive with h | h <;> rw [h] <;> exact fun h' => by cases h'
  have hdc := SB.Lw.isDomainChart_runChart (κ := c.κ) (b := c.b) (jumps := c.jumps) spec (fun j => E j ω₀)
    hpr k hnot
  have hdc' : IsDomainChart (H \ fillH (SB.prefixPhysSet c.κ c.b c.jumps spec (fun j => E j ω₀) k)) cL := by
    rw [hcL]
    exact hdc
  rw [hdc'.coe_dom]
  exact hdc'

end InteractingSLE.Theorem14.GW2Psm
