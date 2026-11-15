/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux70
import InteractingSLE.Spec.Sec7.Lemma77RealLens

/-!
# Lemma 7.7 and Theorem 1.5's first-contact input with Aux. lemma 70 reduced

Packet PROVE-LEMMA76. The landed `lemma77Statement_of_aux70_of_lemma76` and
`w8FirstContactStatement_of_aux70_of_lemma76` (`Lemma77RealLens.lean`) take Aux. lemma 70 as an input;
`aux70Statement_of_inputs` (`Aux70.lean`) reduces it to Lemma 7.5, Aux. lemma 56 at first entrance times, the
single-path side heights and the chart geometry of a stopped reverse arc. These are the compositions (conditional
helpers: Lemma 7.6 and the four inputs of Aux. lemma 70's reduction are not proved).
-/

set_option autoImplicit false

namespace InteractingSLE

namespace Sec7

universe u

/-- **Lemma 7.7** from Lemma 7.6, Lemma 7.5, Aux. lemma 56 at first entrance times, the single-path side heights and
the chart geometry of a stopped reverse arc (a conditional helper). -/
theorem lemma77Statement_of_lemma76_of_inputs (h76 : Lemma76Statement.{u})
    (hL75 : Theorem15.Lemma75Statement.{u}) (hA56 : Restart.RetainedRangeEntranceStatement.{u})
    (hside : SinglePathSideHeightStatement.{u}) (hgeom : ReverseArcChartStatement) :
    Supp10.Lemma77Statement.{u} :=
  lemma77Statement_of_aux70_of_lemma76 (aux70Statement_of_inputs hL75 hA56 hside hgeom) h76

/-- **Theorem 1.5's first-contact input** from the same inputs (a conditional helper). -/
theorem w8FirstContactStatement_of_lemma76_of_inputs (h76 : Lemma76Statement.{u})
    (hL75 : Theorem15.Lemma75Statement.{u}) (hA56 : Restart.RetainedRangeEntranceStatement.{u})
    (hside : SinglePathSideHeightStatement.{u}) (hgeom : ReverseArcChartStatement) :
    Theorem15.W8FirstContactStatement.{u} :=
  w8FirstContactStatement_of_aux70_of_lemma76 (aux70Statement_of_inputs hL75 hA56 hside hgeom) h76

end Sec7

end InteractingSLE
