import GaussianLQG.LQG.Dimension
import LQGMetric.Assembly.MainReducedS
import LQGMetric.Assembly.MainOpenI

/-!
# Unconditional GM/DFGPS/DG inputs used by track CC

Several Gwynne–Miller lemmas in `LQGMetric` take the Ding–Gwynne and DFGPS estimates as hypotheses
(for example `GM.gm_L2_11_closed (h41 : DFGPSProp4_1) (hXi : GMXiQBound)`, GM Lemma 2.11 = [3]
Lemma 3.10). `LQGMetric` discharges them on its route to Theorems 1.1–1.2 (`Assembly/MainOpenI.lean`,
`Assembly/MainFinal.lean`), and `GaussianLQG` packages `DG.DGThm1_5` (`GaussianLQG.dgThm1_5_holds`).
This file re-exports the same discharges as named theorems, so that consumers (CC9) cite them
directly. Nothing here is new mathematics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SmallGammaGeodesics.GMInputs

open LQGMetric LQGMetric.Blueprint

/-- the DZZ-level inputs of the Ding–Gwynne chain, as in `LQGMetric.theorem12_openI` -/
theorem dzzInputsDGForm_holds : DG.DZZInputsDGForm :=
  DG.dzzInputsDGForm_of (DZZ.dzzInputsDG_of_exp (DZZ.dzzLem53ExpAll_of_hbadB l53HbadBAll_proved))

/-- Ding–Gwynne Theorem 1.5, uniform form (`DG.wire_dgThm1_5KU_of`) -/
theorem dgThm1_5KU_holds : DGThm1_5KU :=
  DG.wire_dgThm1_5KU_of DG.L37Q.dgLem3_7 (DG.dgProp3_16_of_lem37 DG.L37Q.dgLem3_7)
    dzzInputsDGForm_holds

/-- Ding–Gwynne Proposition 3.21 (`DG.wire_dgProp3_21_of`) -/
theorem dgProp3_21_holds : DGProp3_21 :=
  DG.wire_dgProp3_21_of DG.L37Q.dgLem3_7 dzzInputsDGForm_holds

/-- DFGPS Theorem 1.5 (optimal scaling of the constants), as in `LQGMetric.theorem12_openG` -/
theorem dfgpsScaling_holds : DFGPSScaling :=
  DFGPS.dfgpsScaling_of_lem3_6 LM.lmLem3_1a (DFGPS.L36.lem3_6_of_DG dgThm1_5KU_holds dgProp3_21_holds)

/-- DFGPS Proposition 4.1 (= GM Lemma 2.10) -/
theorem dfgpsProp4_1_holds : DFGPSProp4_1 :=
  DFGPS.P41.dfgpsProp4_1_of_DG LM.lmLem3_1a GaussianLQG.dgThm1_5_holds dgThm1_5KU_holds
    dgProp3_21_holds

/-- the bound `ξ Q > 1`-type input of GM (`Blueprint.GMXiQBound`) -/
theorem gmXiQBound_holds : GMXiQBound :=
  DG.gmXiQBound_of_dgThm1_5' GaussianLQG.dgThm1_5_holds

/-- **GM Lemma 2.11 on the closed annulus** (= [3] Lemma 3.10), unconditionally -/
theorem l2_11c_holds : GM.L2_11c :=
  GM.gm_L2_11_closed dfgpsProp4_1_holds gmXiQBound_holds

/-- **GM Proposition 2.2** (bi-Lipschitz equivalence of weak metrics), unconditionally -/
theorem p2_2_holds : GM.P2_2 :=
  GM.Bilip.gm_P2_2' LM.lmThm1_6 GM.Tight.blueprint_GMS2_4a GM.Tight.blueprint_GMS2_4c

end SmallGammaGeodesics.GMInputs
