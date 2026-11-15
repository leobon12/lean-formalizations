/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxKer
import InteractingSLE.Spec.Supplement.GW2GmJoin

/-!
# GW2's open lines: the launch of the current piece under the conditional kernel

Packet PROVE-GW2-STAGEMEAN, R120 round (per-sample assembly). Under `ν = condExpKernel P pastG ω₀` the earlier pieces
are those of `ω₀` (run equality, `CondDriverBridge.ae_ae_run_eq_of_le`), so the launch of the current piece at `ω₀`
is, `ν`-almost surely, the launch at the sample itself, and the history succeeded there:

* **`curLaunch_eq_of_run_eq`**: equal runs before the current piece give the same launch (`GW2Schedule.run_gw2`'s
  live/stuck dichotomy and the run chart);
* `oldSuccess_of_allSucc_cur`: success of the earlier pieces of the future program is the history's success;
* **`ae_ae_launch_cur`**: for `P`-a.e. `ω₀`, `ν`-a.s. the launch at `ω₀` is the launch at the sample, with success.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Schedule GW2Tip Exist Exist.Staged Exist.StagedLaw

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **Equal runs before the current piece give the same launch.** -/
theorem curLaunch_eq_of_run_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) {ω₀ ω : Ω}
    (hrun : ExplState.run c.κ c.b c.jumps (GW2Olm.futSpec c r l a) (fun j => GW2Olm.futFam c r l a j ω)
        (GW2Olm.curIdx c r l) =
      ExplState.run c.κ c.b c.jumps (GW2Olm.futSpec c r l a) (fun j => GW2Olm.futFam c r l a j ω₀)
        (GW2Olm.curIdx c r l))
    {cL : Chart} {θ : ℝ} (hl : GW2Olm.curLaunch c r l a ω₀ = some (cL, θ)) :
    GW2Olm.curLaunch c r l a ω = some (cL, θ) := by
  set spec := GW2Olm.futSpec c r l a with hspec
  set k := GW2Olm.curIdx c r l with hk
  set L := futureProgram c r l a with hL
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  have hprog := isFlowProg_spec (rootPt r.1) true L
  have hgw : spec.2.1 = true := rfl
  set D₀ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => GW2Olm.futFam c r l a j ω₀ with hD₀
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => GW2Olm.futFam c r l a j ω with hD
  have hk' : k < spec.2.2.length := by omega
  have hs₀ : AllSucc (specDelta spec) D₀ k := by
    by_contra hn
    have h0 := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) hgw hprog (specDelta_ne_top _) D₀
      hk').2 hn
    have h1 : GW2Olm.curLaunch c r l a ω₀ = none := h0
    rw [h1] at hl
    simp at hl
  have hr₀ := (run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) hgw hprog (specDelta_ne_top _) D₀ k hk'.le).1 hs₀
  have hs : AllSucc (specDelta spec) D k := by
    by_contra hn
    have hst := (run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) hgw hprog (specDelta_ne_top _) D k hk'.le).2 hn
    rw [hrun] at hst
    rcases hr₀.1 with h | h <;> rcases hst with h' | ⟨o, h'⟩ <;> rw [h] at h' <;> cases h'
  have hr := (run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) hgw hprog (specDelta_ne_top _) D k hk'.le).1 hs
  have hl₀ := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) hgw hprog (specDelta_ne_top _) D₀ hk').1
    hs₀
  have hl' := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) hgw hprog (specDelta_ne_top _) D hk').1 hs
  have h1 : GW2Olm.curLaunch c r l a ω₀ = some (succChart spec.1 (specDelta spec) D₀ k, specAngle spec k) := hl₀
  rw [hl] at h1
  obtain ⟨hc, hθ⟩ := Prod.mk.inj (Option.some.inj h1)
  have hchart : succChart spec.1 (specDelta spec) D k = cL := by
    rw [← hr.2, hrun, hr₀.2, hc]
  change (ExplState.run c.κ c.b c.jumps spec D (k + 1)).2.2.2.1 k = some (cL, θ)
  rw [hl', hchart, hθ]

/-- **Success of the earlier pieces of the future program is the history's success.** -/
theorem oldSuccess_of_allSucc_cur (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) {ω : Ω}
    (hs : AllSucc (specDelta (GW2Olm.futSpec c r l a)) (fun j => GW2Olm.futFam c r l a j ω)
      (GW2Olm.curIdx c r l)) :
    oldSuccess c r l ω := by
  intro j
  have h := (RootCv.recOf_flag_eq_false_iff _ _).mpr (hs j j.isLt)
  change (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (futureProgram c r l a)) j ω).2.2 = false at h
  rw [futureProgram, stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ j.isLt ω] at h
  exact h

variable [StandardBorelSpace Ω]

/-- **The launch at `ω₀` is, under the conditional kernel, the launch at the sample, with success.** -/
theorem ae_ae_launch_cur (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω₀ ∂c.P, ∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), ∀ (cL : Chart) (θ : ℝ),
      GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) → GW2Olm.curLaunch c r l a ω = some (cL, θ) ∧
        oldSuccess c r l ω := by
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
  have h𝒢 : GW2Olm.pastG c r l a ≤ mΩ := hS.2.1 k
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  filter_upwards [CondDriverBridge.ae_ae_run_eq_of_le (P := c.P) (κ := c.κ) (b := c.b) (jumps := c.jumps) spec
    (fun j _ ω => hreg j ω) h𝒢 le_rfl] with ω₀ hω₀
  filter_upwards [hω₀] with ω hω cL θ hl
  have h1 := curLaunch_eq_of_run_eq c r l a hω hl
  refine ⟨h1, oldSuccess_of_allSucc_cur c r l a ?_⟩
  by_contra hn
  have h0 := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl (isFlowProg_spec x true L)
    (specDelta_ne_top _) (fun j => E j ω) (show k < spec.2.2.length by omega)).2 hn
  have h2 : GW2Olm.curLaunch c r l a ω = none := h0
  rw [h2] at h1
  simp at h1

end InteractingSLE.Theorem14.GW2Omx
