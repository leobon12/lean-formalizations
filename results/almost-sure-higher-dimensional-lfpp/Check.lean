import HigherDimLFPPAS.Frozen.AsConvergence
import HigherDimLFPPAS.Frozen.AsConvergenceNonneg
import HigherDimLFPPAS.Frozen.AsConvergenceMedianOne
import HigherDimLFPPAS.Frozen.Assumption11Nonvacuous
import HigherDimLFPPAS.Frozen.AsConvergenceNonvacuous
import HigherDimLFPPAS.Frozen.ConvKernelSeed
import HigherDimLFPPAS.Frozen.ConvMollifySpecSeed
import HigherDimLFPPAS.Frozen.ConvMollifyJointSeed
import Mathlib.Util.AssertNoSorry

/-! Release audit of the advertised theorems: the eight frozen theorem anchors of `HigherDimLFPPAS` (the two frozen
definitions `IsAdmissibleSeed` and `Assumption11` are imported through them). Every `#print axioms` report must list
only axioms among `propext`, `Classical.choice` and `Quot.sound` (any subset). -/
set_option autoImplicit false

-- Theorem 1.2: signed seeds, under Assumption 1.1.
assert_no_sorry HigherDimLFPPAS.asConvergence
#print axioms HigherDimLFPPAS.asConvergence

-- Theorem 1.2 for nonnegative seeds, with no assumption: one median-one strong limit, and every median-one strong limit.
assert_no_sorry HigherDimLFPPAS.asConvergence_nonneg
#print axioms HigherDimLFPPAS.asConvergence_nonneg
assert_no_sorry HigherDimLFPPAS.asConvergence_medianOne
#print axioms HigherDimLFPPAS.asConvergence_medianOne

-- Non-vacuity of Assumption 1.1 and of the hypotheses of Theorem 1.2.
assert_no_sorry HigherDimLFPPAS.assumption11_nonvacuous
#print axioms HigherDimLFPPAS.assumption11_nonvacuous
assert_no_sorry HigherDimLFPPAS.asConvergence_nonvacuous
#print axioms HigherDimLFPPAS.asConvergence_nonvacuous

-- The kernel and the convolution field on the signed carrier.
assert_no_sorry HigherDimLFPPAS.convKernel_seed
#print axioms HigherDimLFPPAS.convKernel_seed
assert_no_sorry HigherDimLFPPAS.convMollify_spec_seed
#print axioms HigherDimLFPPAS.convMollify_spec_seed
assert_no_sorry HigherDimLFPPAS.convMollify_joint_seed
#print axioms HigherDimLFPPAS.convMollify_joint_seed
