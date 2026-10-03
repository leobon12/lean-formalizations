import LQGMetric.Papers.DFGPS.P3_1
import LQGMetric.Papers.DFGPS.L3_2Main
import LQGMetric.Papers.DFGPS.L36UpperFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 3.1 and Theorem 1.5: assembly

DFGPS (Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380): Proposition 3.1 (T:1414–1420) from
Lemma 3.2 (`lem3_2`, which uses LM Lemma 3.1) and Theorem 1.5 (`Blueprint.DFGPSScaling`,
T:1659–1723) from Proposition 3.1 and Lemma 3.6.
-/

namespace LQGMetric.DFGPS

open Blueprint

/-- **DFGPS Proposition 3.1**, from LM Lemma 3.1 only -/
theorem prop3_1 (h31a : LMLem3_1a) : Prop3_1 :=
  prop3_1_of_lem3_2 (lem3_2 h31a)

/-- **DFGPS Theorem 1.5** (`Blueprint.DFGPSScaling`), from LM Lemma 3.1 and DFGPS Lemma 3.6 -/
theorem dfgpsScaling_of_lem3_6 (h31a : LMLem3_1a) (h36 : Lem3_6) : DFGPSScaling :=
  dfgpsScaling_of_lem3_2 (lem3_2 h31a) h36

end LQGMetric.DFGPS
