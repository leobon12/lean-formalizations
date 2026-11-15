/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkMarkSeedLaw

/-! # The four original walk-side leaves from Theorems 1.2 and 1.3 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkMarkSeed

open Exist.Staged Exist.StagedLaw

/-- The last remaining named walk-side input follows from the actual staged
law. Its off-sector and nonempty-jump restrictions are unnecessary here. -/
theorem offAmbientNoZeroStatement_of_mem {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) :
    WalkFreshRecord.OffAmbientNoZeroStatement.{u} θ right := by
  intro κ hκ _ b jumps hb Ω _ _ P _ h hh E hE _ hreg _ _
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  exact ae_noZeroLaterLaunchData hκ hb hh (hE _ hw)
    (fun j ω => hreg (boundaryWalkSpec b jumps θ right) j ω)

/-- All four unchanged original packet leaves. Every seed, finite-exit,
freshness, and later-lifetime input is discharged by the staged law. -/
theorem prefixInputs_of_thm12_thm13
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    WalkSide.PrefixMarkedLocalStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixChartVersionStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixMarkedLocalStatement.{u} (Real.pi / 2) false ∧
    WalkSide.PrefixChartVersionStatement.{u} (Real.pi / 2) false :=
  WalkFreshRecord.prefixInputs_of_noZero h12 h13
    (offAmbientNoZeroStatement_of_mem ⟨le_rfl, by linarith only [Real.pi_pos]⟩ true)
    (offAmbientNoZeroStatement_of_mem ⟨by linarith only [Real.pi_pos], le_rfl⟩ false)

end InteractingSLE.Theorem14.WalkMarkSeed
