/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR11NearCore

/-!
# C24 near and slow comparisons for an arbitrary construction

Only the two named construction properties of `GW2JDetR11Facts` are used.
The shared comparison family is data; it carries no probability inequality.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR11

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 Sec5

/-- The arbitrary construction's near comparison follows from the actual
stopped dynamics and deterministic buffer facts. No Theorem 1.3 or new
crossing probability premise is needed for this transfer. -/
theorem retainedNearModelsStatement_of_stoppedSDE_buffer
    (D : ConstructionFamily.{u}) (C : ComparisonFamily.{u})
    (hSDE : RetainedStoppedSDEStatement D C) (hBuffer : RetainedBufferStatement D C) :
    RetainedNearModelsStatement D := by
  intro Ω _ _ c r
  dsimp only
  intro l
  filter_upwards [hSDE.near Ω c r l, hBuffer.near Ω c r l] with ω hs hb hω
  let z := (C Ω c r).near l ω
  refine ⟨z.family, fun n => ?_⟩
  filter_upwards [hs hω n, hb hω n] with m hmSDE hmBuffer
  refine ⟨z.candidate n m, ?_⟩
  change z.family.crossProb m n ≤
    ((condExpKernel c.P (c.sigma r l) ω).map
      (((D Ω c).experiment r).data.sample l (z.candidate n m)))
      (((D Ω c).experiment r).data.reach l (z.candidate n m))
  exact near_comparison c.hκ (condExpKernel c.P (c.sigma r l) ω) z
    (fun a => ((D Ω c).experiment r).sampleMeas l a)
    (((D Ω c).experiment r).data.reach l) n m hmSDE hmBuffer

/-- The arbitrary construction's slow comparison follows from the local
stopped SDE. All full-model and first-zero window data are constructed. -/
theorem retainedSlowComparisonsStatement_of_stoppedSDE_buffer
    (D : ConstructionFamily.{u}) (C : ComparisonFamily.{u})
    (hSDE : RetainedStoppedSDEStatement D C) (hBuffer : RetainedBufferStatement D C) :
    RetainedSlowComparisonsStatement D := by
  intro Ω _ _ c r
  dsimp only
  intro k l hl a
  filter_upwards [hSDE.slow Ω c r k l hl a, hBuffer.slow Ω c r k l hl a]
    with ω hs hb hω
  let z := (C Ω c r).slow l a ω
  obtain ⟨hφ, hy, hC, hstop, hread⟩ := hb hω
  have hE := hs hω
  obtain ⟨win, hwin⟩ := GW2JDetR10.exists_slowWindow_of_stoppedEvolution
    c.hκ c.hκ4 z.ρL₀ z.ρR₀ z.mL z.mR z.φ hφ z.xL z.xR z.start hy
    (condExpKernel c.P (c.sigma r l) ω) z.dynamics.filtration z.dynamics.W
    z.dynamics.VL z.dynamics.VR z.dynamics.B z.dynamics.stop hE.1 hE.2
    (((D Ω c).experiment r).sampleMeas l a) hstop hread
  change ∃ win : RootS5.RestartWindow.{u} c.κ ((D Ω c).experiment r).driftBound
    (Icc (-angleWeightBound c.κ) (angleWeightBound c.κ)),
      win.e.P win.slowEvent ≤ ((condExpKernel c.P (c.sigma r l) ω).map
        (((D Ω c).experiment r).data.sample l a)) RootV7.slowSet
  rw [hC]
  exact ⟨win, hwin⟩

/-- Both unchanged C24 binders from precisely the two named properties. -/
theorem retainedComparisons_of_stoppedSDE_buffer
    (D : ConstructionFamily.{u}) (C : ComparisonFamily.{u})
    (hSDE : RetainedStoppedSDEStatement D C) (hBuffer : RetainedBufferStatement D C) :
    RetainedNearModelsStatement D ∧ RetainedSlowComparisonsStatement D :=
  ⟨retainedNearModelsStatement_of_stoppedSDE_buffer D C hSDE hBuffer,
    retainedSlowComparisonsStatement_of_stoppedSDE_buffer D C hSDE hBuffer⟩

end InteractingSLE.Theorem14.GW2JDetR11
