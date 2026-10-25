import SupercriticalLQGUniqueness.B2.QPos.P2Main
import SupercriticalLQGUniqueness.B2.QPos.P3CircuitMass

 




set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 
theorem dgffCircuitLower_proved : Inputs.DGFFCircuitLower :=
  dgffCircuitLower_of_circuitMass circuitMass_proved

end SupercriticalLQGUniqueness.B2.QPos
