import SupercriticalLQGUniqueness.B2.PfeLocal.R68LocMain
import SupercriticalLQGUniqueness.B2.Final.OpenInputs5

 
















set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
theorem s2LocalitySite_proved : Final.S2LocalitySite := by
  intro _ ξ Q m e c V Ω' _ _ P' _ h' hN L hB hSA hAT _ Φ _ hII _ hFFW hId Ω _ P _ h hh U
  exact r68_patchWitness_locality_of_gffPlusCont ξ m e hB hSA hAT Φ hII
    (Final.patchWeylIdentity_of_identification hId) hFFW
    (Final.normalizedLimitGeometry_of_coupling hB Φ hII) P h hh U

end SupercriticalLQGUniqueness.B2.PfeLocal
