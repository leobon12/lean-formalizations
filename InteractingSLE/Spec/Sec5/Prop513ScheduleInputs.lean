/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleRegularize
import InteractingSLE.Spec.Sec5.Prop513ScheduleHeights

/-!
# The earlier extraction inputs under the R51 and R56 source premises

This file exposes the proved inputs for the original, almost surely regular
family, including the closed availability predicate and nonemptiness.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.AdmCode Prop513TreeExtract Theorem14.StagedReg

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  (c : BoundaryWord) (hc : ExtremeHeights κ c)
  (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
  {E : Schedule → ℕ → Ω → Driver}
  (hE : ∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (E s))
  (hR : ∀ s, StagedPiecesRegular κ c.fn c.jumps P (scheduleSpec s) (E s))

include h44 hκ hκ4 c hc hh hE hR

theorem prefixTraceRegularity_of_stagedPiecesRegular :
    PrefixTraceRegularity P (fun _ => univ) E := by
  have hreg := prefixTraceRegularity h44 hκ hκ4 c hc hh
    (fun s => isStagedHistory_regHist c.isPiecewiseConstantBoundaryData (hE s) (hR s))
    (fun _ _ _ => isRegularDriver_regHist _ _)
  intro s
  filter_upwards [hreg s, ae_prefixDriver_regHist h44 hκ hκ4 c hc hh hE hR]
    with ω hω he _
  have hp := hω (mem_univ _)
  rwa [he s] at hp

theorem prefixFieldDrivers_of_stagedPiecesRegular : PrefixFieldDrivers P (fun _ => univ) h E := by
  obtain ⟨D, hDm, hDe⟩ := prefixFieldDrivers h44 hκ hκ4 c hc hh
    (fun s => isStagedHistory_regHist c.isPiecewiseConstantBoundaryData (hE s) (hR s))
    (fun _ _ _ => isRegularDriver_regHist _ _)
  refine ⟨D, hDm, fun s => ?_⟩
  filter_upwards [hDe s, ae_prefixDriver_regHist h44 hκ hκ4 c hc hh hE hR]
    with ω hω he ha t ht
  simpa only [he s] using hω ha t ht

theorem ae_all_available_of_stagedPiecesRegular :
    ∀ᵐ ω ∂P, ∀ s, scheduleAvailable E s ω ∧ scheduleAvailableClosed E s ω := by
  have hav := ae_all_schedules_available h44 hκ hκ4 c hc hh
    (fun s => isStagedHistory_regHist c.isPiecewiseConstantBoundaryData (hE s) (hR s))
    (fun _ _ _ => isRegularDriver_regHist _ _)
  simpa only [scheduleAvailable, scheduleAvailableClosed, regHist_snd] using hav

theorem prefixAvailabilityFieldStatement_of_stagedPiecesRegular :
    PrefixAvailabilityFieldStatement P h E := by
  refine ⟨fun _ _ => true, fun _ => measurable_const, ?_⟩
  exact (ae_all_available_of_stagedPiecesRegular h44 hκ hκ4 c hc hh hE hR).mono
    fun _ hω s => ⟨fun _ => (hω s).1, fun _ => rfl⟩

theorem prefixEndpointCompatibility_of_stagedPiecesRegular :
    PrefixEndpointCompatibility P E := by
  have hcompat := prefixEndpointCompatibility h44 hκ hκ4 c hc hh
    (fun s => isStagedHistory_regHist c.isPiecewiseConstantBoundaryData (hE s) (hR s))
    (fun _ _ _ => isRegularDriver_regHist _ _)
  have hav := ae_all_schedules_available h44 hκ hκ4 c hc hh
    (fun s => isStagedHistory_regHist c.isPiecewiseConstantBoundaryData (hE s) (hR s))
    (fun _ _ _ => isRegularDriver_regHist _ _)
  filter_upwards [hcompat, hav, ae_prefixDriver_regHist h44 hκ hκ4 c hc hh hE hR]
    with ω hcω ha he n m _ _ η η' hη hη'
  apply hcω n m (ha _).1 (ha _).1 η η'
  · rwa [he]
  · rwa [he]

theorem ae_nonempty_and_strict_iff_closed_of_stagedPiecesRegular :
    ∀ᵐ ω ∂P, (∃ n, scheduleAvailable E (scheduleAt n) ω) ∧
      ∀ s, scheduleAvailable E s ω ↔ scheduleAvailableClosed E s ω :=
  (ae_all_available_of_stagedPiecesRegular h44 hκ hκ4 c hc hh hE hR).mono fun _ hω =>
    ⟨⟨0, (hω _).1⟩, fun s => ⟨fun _ => (hω s).2, fun _ => (hω s).1⟩⟩

end InteractingSLE.Sec5.Prop513Schedule
