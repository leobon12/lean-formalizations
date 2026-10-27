import MatedCRTHarmonic
import Mathlib.Util.AssertNoSorry

/-! Axiom audit for the seven advertised results of *Harmonic functions on mated-CRT maps*.
The reports should contain only `propext`, `Classical.choice`, and `Quot.sound`.
The publication verifier also audits every declaration in the included modules. -/
set_option autoImplicit false

assert_no_sorry MatedCRTHarmonic.theorem3_2
#print axioms MatedCRTHarmonic.theorem3_2

assert_no_sorry MatedCRTHarmonic.theorem1_3
#print axioms MatedCRTHarmonic.theorem1_3

assert_no_sorry MatedCRTHarmonic.theorem1_4
#print axioms MatedCRTHarmonic.theorem1_4

assert_no_sorry MatedCRTHarmonic.theorem1_5
#print axioms MatedCRTHarmonic.theorem1_5

assert_no_sorry MatedCRTHarmonic.theorem1_5_simplyConnected
#print axioms MatedCRTHarmonic.theorem1_5_simplyConnected

assert_no_sorry MatedCRTHarmonic.corollary1_6
#print axioms MatedCRTHarmonic.corollary1_6

assert_no_sorry MatedCRTHarmonic.corollary1_6_simplyConnected
#print axioms MatedCRTHarmonic.corollary1_6_simplyConnected
