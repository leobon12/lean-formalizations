import LQGMetric.Papers.DFGPS.L217R
import LQGMetric.Papers.DFGPS.T12Blueprint
import LQGMetric.Field.MarkovFinal
import LQGMetric.Papers.DFGPS.P29SqC

/-!
# DFGPS Theorem 1.2 (existence) with DDDF Proposition 29 on the square only (P2-DDDFP29b)

`dfgps_existence_reduced'`: `dfgps_existence_reduced` (Assembly/ExistenceReduced.lean) with
`Blueprint.DDDFProp29` replaced by `DDDF.DDDFProp29Sq` (DDDF Prop 29 for `D = (−1,2)²`, the only
domain DFGPS uses, T:877–881), through the primed chain Papers/DFGPS/P29Sq{A,B,C}.lean.
Wiring only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint DDDF

/-- **DFGPS Lemma 2.17** from the cited inputs, DDDF Prop 29 on the square only. -/
theorem lem2_17Sq (h11 : DDDFThm1_1) (h12 : DDDFThm1_2) (h29 : DDDFProp29Sq) (hLM : LMLem2_1)
    (h699 : DDDFEq6_99) : Lem2_17 :=
  lem2_17_of_core' (lem2_8_proved' h11 h12 h29 hLM h699)
    (lem2_17Core hLM (lem2_8_proved' h11 h12 h29 hLM h699) lem2_1GffApprox)

/-- **DFGPS Lemma 2.20** from the cited inputs, DDDF Prop 29 on the square only. -/
theorem lem2_20Sq (hLM8 : LMCor1_8) (h11 : DDDFThm1_1) (h12 : DDDFThm1_2)
    (h29 : DDDFProp29Sq) (hLM : LMLem2_1) (h13 : DDDFEq1_3) (h699 : DDDFEq6_99) : Lem2_20 :=
  lem2_20_of_bilip hLM8 (lem2_8_proved' h11 h12 h29 hLM h699) (lem2_17Sq h11 h12 h29 hLM h699)
    (lem2_20Bilip (lem2_13' h11 h12 h29 hLM h13 h699) lem2_20Transl)

namespace T12

end T12

end LQGMetric.DFGPS
