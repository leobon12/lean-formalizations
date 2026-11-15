/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71TWire
import InteractingSLE.Spec.Sec5.Cond44Ref
import InteractingSLE.Spec.Sec5.Prop55N

/-!
# Lemma 7.1's pocket-chart statement from the proved boundary result

The deterministic `MidRealOffStatement` is now proved in Lemma71T. This adapter supplies the pocket chart required by
Theorem 1.3 from the §4.2 reference and the three-curve-space consequences of Propositions 4.11 and 5.1.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Sec7.Lemma71CFromMid

/-- The pocket-chart statement follows from the reference, the half-plane statement, and Lemma 6.13's contact input. -/
theorem lemma71PocketChartStatement_of_reference
    (href : Lemma71H.Cond44ReferenceStatement.{u}) (h55 : Lemma71H.Prop55HalfPlaneStatement.{u})
    (hMD : Lemma71I.Lemma613ContactStatement.{u}) : Lemma71C.Lemma71PocketChartStatement.{u} := by
  have hpin : Lemma71F.Lemma71PocketPinStatement.{u} :=
    Lemma71T.lemma71PocketPinStatement href h55 hMD
  exact Lemma71C.lemma71PocketChartStatement_of_pocketCurve
    (Lemma71E.lemma71PocketCurveStatement_of_pocket (Lemma71F.lemma71PocketStatement_of_pin hpin))

/-- The pocket-chart statement from Proposition 4.11 and Proposition 5.1. -/
theorem lemma71PocketChartStatement_of_prop411Q_of_prop51Q
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) :
    Lemma71C.Lemma71PocketChartStatement.{u} := by
  have href : Lemma71H.Cond44ReferenceStatement.{u} :=
    Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  have h55 : Lemma71H.Prop55HalfPlaneStatement.{u} :=
    Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hMD : Lemma71I.Lemma613ContactStatement.{u} := Lemma613.lemma613ContactStatement_of_prop55 href h55
  exact lemma71PocketChartStatement_of_reference href h55 hMD

end InteractingSLE.Sec7.Lemma71CFromMid

end
