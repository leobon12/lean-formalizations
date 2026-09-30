import QuantumZipper.Proofs.Zipper.CfgFMVarMain
import QuantumZipper.Proofs.Zipper.CfgFMVarEnergy
import QuantumZipper.Proofs.Zipper.CfgFMPot
import QuantumZipper.Proofs.Zipper.CfgFMVarDisp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FM-VAR (5): node CFG-FM-VAR holds

`CfgFM.cfgFMVarStmt_holds`: the Kolmogorov assembly `cfgFMVar_of_energy`, the time energy node
`tEnergy_of_lip`, the uniform potential Lipschitz bound `tPushPotLip_holds` and the Hölder
displacement `tDisp_of_good`. Bookkeeping only.
-/

namespace QuantumZipper.E6
namespace CfgFM

open RegUnif RegCont CharFun

/-- **Node CFG-FM-VAR holds.** -/
theorem cfgFMVarStmt_holds (κ T : ℝ) (hT : 0 < T) : CfgFMVarStmt κ T hT :=
  cfgFMVar_of_energy κ T hT fun f hf =>
    tEnergy_of_lip (continuous_Wof κ T hT.le f) (Wof_zero_of_GoodP hT.le κ hf)
      (tPushPotLip_holds (continuous_Wof κ T hT.le f) (Wof_zero_of_GoodP hT.le κ hf) T)
      (tDisp_of_good κ hT hf)

end CfgFM
end QuantumZipper.E6
