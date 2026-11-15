/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UaStmt
import InteractingSLE.Spec.Wire.T14GdBase

/-!
# The stopped stage law on guarded histories (decision D84 (A))

Packet PROVE-GW2-RELDET (round 39, decision D84). `GW2Rd.StageLawXSStatement` (`GW2UaStmt`, landed, untouched) asks
for the canonical stopped driver at every good root. Its tip exclusion (a first contact at the counterflow's tip is
excluded almost surely) is a law statement and needs the stage law of the instances, which exists on **guarded**
histories only (`Wire.T14Gd.Guard`: a strictly ordered history, and the root `0` or in `lowerArcRoots`). The consumers
read the law only on alive, hence guarded, histories (BUF's `GW2BxMain`/`GW2BxFacts`, NEARIMG2's `GW2NhLaw`).

* **`StageLawXSGStatement h13 ver`**: `StageLawXSStatement h13 ver` with the extra premise `Wire.T14Gd.Guard c r l`.
  RELDET proves it on NOTHR's stop family; BUF and NEARIMG2 switch to it (D84).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rv GW2Sde GW2Sdh

/-- **The stage law in version form, on the stopped curve, on guarded histories** (decision D84 (A); the guarded
successor of `StageLawXSStatement`). -/
def StageLawXSGStatement (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l → Wire.T14Gd.Guard c r l →
    ∀ᵐ ξ ∂c.P, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
      ∃ Wc : ℝ≥0 → ℝ, IsCanonXS c r l a (ver Ω c r l a).R (ver Ω c r l a).V ξ Wc

/-- The unguarded stopped stage law gives the guarded one. -/
theorem StageLawXSStatement.guarded {h13 : Exist.Theorem13Statement.{u}} {ver : SchedVerXFamily.{u}}
    (h : StageLawXSStatement h13 ver) : StageLawXSGStatement h13 ver :=
  fun Ω _ _ c r l a hg hord _ => h Ω c r l a hg hord

end InteractingSLE.Theorem14.GW2Rd
