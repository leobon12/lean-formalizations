/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtJLaw
import InteractingSLE.Spec.Sec7.LocalExtJRef

/-!
# Aux. lemma 54 for stopped seed couplings: what remains

Packet PROVE-LOCEXT-J. With (U) (`stoppedTwoSeedLawStatement`) and the standard reference
(`stdTwoSeedReferenceStatement`) proved, Aux. lemma 54 for stopped seed couplings (`StoppedSeedExtensionStatement κ`)
follows from PROVE-LOCEXT-H's two remaining named inputs on a record extension: the protected kernel before the local stop
(`ExtPreStopStatement κ`, (K-pre)) and locality (`ExtLocalityStatement κ`, (Loc)).
-/

set_option autoImplicit false

universe u

namespace InteractingSLE

namespace LocalExt

/-- **Aux. lemma 54 for stopped seed couplings** from (K-pre) and (Loc) alone. -/
theorem stoppedSeedExtensionStatement_of_preLoc {κ : ℝ} (hκ : 0 < κ) (hPre : ExtPreStopStatement.{u} κ)
    (hLoc : ExtLocalityStatement.{u} κ) : StoppedSeedExtensionStatement.{u} κ :=
  stoppedSeedExtensionStatement_of_lawPreLoc hκ (stoppedTwoSeedLawStatement hκ) hPre hLoc

end LocalExt

end InteractingSLE
