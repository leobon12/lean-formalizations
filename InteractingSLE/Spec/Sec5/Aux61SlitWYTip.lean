/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWXTip
import InteractingSLE.WangWu.ReverseContactBdrySide

/-!
# The full forward-tip input from the existing simple-trace theorem

The existing Wang--Wu theorem gives convergence throughout the own slit
complement. The forward map takes that complement into the half-plane,
which strengthens its target filter to the one required by the assembly.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.Sec5.Aux61SlitWY
open Aux61SlitW Aux61SlitWX
universe u

/-- The named deterministic input is already a consequence of the landed
whole-domain simple-trace limit, with its half-plane range recorded. -/
theorem simpleTipForwardLimit : SimpleTipForwardLimit := by
  intro W η hW hW0 hη harc r hr
  refine tendsto_nhdsWithin_iff.2 ⟨WangWu.tendsto_fwdMap_tip hη harc hW hW0
    (NNReal.coe_pos.2 hr), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW r.coe_nonneg hz

/-- The actual source flow has the full own-domain forward-tip limit,
without an additional deterministic or stochastic premise. -/
theorem ownTipForwardLimit (S : SourceSetting.{u}) : OwnTipForwardLimit S :=
  ownTipForwardLimit_of_simpleTip simpleTipForwardLimit S

end InteractingSLE.Sec5.Aux61SlitWY
