/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux85Junction
import InteractingSLE.Spec.Supplement.RetZoneMean

/-!
# Theorem 1.5's leaf 2 from Lemma 7.5 alone

Packet PROVE-T15-AUX85. With Aux. lemma 85 in the retained chart proved (`Aux85.retTouchZonesStatement`) and
Aux. lemma 82 proved from Lemma 7.5 (PROVE-T15-RET6, `retCollarMeanStatement_of_lemma75`), the touching-pair chart
boundary values and the touching-pair mean word (leaf 2 of the retained conditional determination) follow from
Lemma 7.5 alone.

R43/R48: Lemma 7.5 only; for Theorem 1.5.
-/

set_option autoImplicit false

universe u

namespace InteractingSLE

namespace RLC

/-- **The touching-pair chart boundary values from Lemma 7.5** (Aux. lemmas 82, 83 and 85 all proved). -/
theorem retTouchChartBoundaryStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u}) :
    RetTouchChartBoundaryStatement.{u} :=
  retTouchChartBoundaryStatement_of_zones hL75 Aux85.retTouchZonesStatement

/-- **Leaf 2 (`RetTouchMeanWordStatement`) from Lemma 7.5 alone.** -/
theorem retTouchMeanWordStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u}) :
    RetTouchMeanWordStatement.{u} :=
  retTouchMeanWordStatement_of_zones hL75 Aux85.retTouchZonesStatement

end RLC

end InteractingSLE
