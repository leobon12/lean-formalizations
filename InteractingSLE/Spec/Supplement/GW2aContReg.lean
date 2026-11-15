/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aContStep
import InteractingSLE.Spec.Wire.Thm1415Now14

/-!
# Lemma GW2a, containment, under ruling R51: the assembly

Packet PROVE-GW2AC. **`gw2aContainmentRegStatement_of_inputs`**: Theorem 1.4's leaf in its R51 form
(`GW2aContainmentRegStatement`) from

* GB6 for one flow line at an interior tip (`GW2Later.GB6PrefixPairStatement`) and GB6's restart law
  (`Supp8.GB6.GB6RestartStatement`) — both landed consequences of GB6's hull identity and Theorems 1.2–1.3
  (`BRLeaf.gb6PrefixPairStatement_of_hullDet`, `Wire.gb6RestartStatement_of_hullDet_now`; the variant
  **`gw2aContainmentRegStatement_of_hullDet`** takes the hull identity);
* BW1 for one flow line at a real endpoint (`BW1PrefixPairStatement`, named input);
* GW2a's connector step (`GW2aConnectorStepStatement`, named input: BR6 and BR4a in the conditional world);
* Theorem 1.3 (at universes `u` and `0`).

Proof. Replace the staged history by its regularization (`StagedReg.regHist`: staged, regular at every sample, almost
surely the same runs and hence the same physical set; ruling R51). Run GW1's induction on the kernels of the retained
pasts (`ae_physSet_subset_of_steps`): the datum before the first instruction is the original counterflow
(`hasStatePair_zero`); the step is `ae_hasStatePair_succ`; the connectors are `ae_arc_subset`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aCont

open Exist.Staged Exist.StagedLaw GW2Later CounterflowRange GW2aMulti

/-- **Lemma GW2a, containment, under ruling R51** (module docstring). -/
theorem gw2aContainmentRegStatement_of_inputs (hG : GB6PrefixPairStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hBW1 : BW1PrefixPairStatement.{u})
    (hCon : GW2aConnectorStepStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) : GW2aContainmentRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR p hp
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  have hbc : IsBoundaryContinuedProgram (⟨0, false, p⟩ : ExplSpec).2.2 := hp
  have hS := hE ⟨0, false, p⟩ hbc
  have hRs := hR ⟨0, false, p⟩ hbc
  -- the regularized history
  set E' := StagedReg.regHist ⟨0, false, p⟩ (E ⟨0, false, p⟩) with hE'
  have hS' : IsStagedHistory κ b jumps P h ⟨0, false, p⟩ E' := StagedReg.isStagedHistory_regHist hb hS hRs
  have hR' : StagedPiecesRegular κ b jumps P ⟨0, false, p⟩ E' := WalkLaw.stagedPiecesRegular_regHist hRs
  have hreg' : ∀ j ω, IsRegularDriver (E' j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have hmain := ae_physSet_subset_of_steps hGB6 hGW0 hT13 hκ hκ4 hb hcf hζ' hp hS' hR' hreg'
    (fun j => ae_hasStatePair_succ hG hBW1 hCon hT13 hκ hκ4 hb hh hcf hζ' hp hS' hR' hreg' j)
    (fun k => ae_arc_subset hCon hκ hκ4 hb hh hcf hζ' hp hS' hR' hreg' k)
  filter_upwards [hmain, StagedReg.ae_run_regHist hRs] with ω h1 h2
  rwa [← StagedReg.physSet_eq_of_run_eq (h2 _)]

/-- **Lemma GW2a, containment, under ruling R51, from GB6's hull identity**: as
`gw2aContainmentRegStatement_of_inputs`, with GB6's two forms derived from `Supp8.GB6.GB6HullDetStatement` and
Theorems 1.2–1.3 (`BRLeaf.gb6PrefixPairStatement_of_hullDet`, `Wire.gb6RestartStatement_of_hullDet_now`). -/
theorem gw2aContainmentRegStatement_of_hullDet (hD : Supp8.GB6.GB6HullDetStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hBW1 : BW1PrefixPairStatement.{u}) (hCon : GW2aConnectorStepStatement.{u}) :
    GW2aContainmentRegStatement.{u} :=
  gw2aContainmentRegStatement_of_inputs (BRLeaf.gb6PrefixPairStatement_of_hullDet hD h12 h13 h12₀ h13₀)
    (Wire.gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD) hBW1 hCon h13 h13₀

end GW2aCont

end Theorem14

end InteractingSLE
