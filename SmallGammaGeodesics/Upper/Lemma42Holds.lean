import SmallGammaGeodesics.Upper.Coupling42
import SmallGammaGeodesics.NIC.Main

/-!
# Lemma 4.2′ holds unconditionally

`Lemma42` (the probe coupling, blueprint `lem:coupling`) follows from the near-identity coupling `CC.NICInput`
(`lemma42_of_NIC`, packet P-G3), which is proved (`NIC.nicInput_holds`, packet P-G2).
-/

set_option autoImplicit false

namespace SmallGammaGeodesics

/-- **Lemma 4.2′**, with no hypotheses. -/
theorem lemma42_holds : Lemma42 := lemma42_of_NIC NIC.nicInput_holds

end SmallGammaGeodesics
