import SupercriticalConformalCovariance.Frozen.ConformalCovariance
import SupercriticalConformalCovariance.Frozen.DomainMetric_ae_eq_of_isDomainRealization
import SupercriticalConformalCovariance.Root.AllXi
import SupercriticalConformalCovariance.GMForm.Base
import SupercriticalConformalCovariance.GMForm.Countable
import SupercriticalConformalCovariance.GMForm.Functional
import SupercriticalConformalCovariance.GMForm.ZeroBoundaryCovariance
import SupercriticalConformalCovariance.GMForm.Realization
import Mathlib.Util.AssertNoSorry

/-! Release audit of the advertised theorems: the two frozen theorems, then the supporting theorems (proved and
independently audited, not frozen). Every `#print axioms` report must list only axioms among `propext`,
`Classical.choice` and `Quot.sound` (any subset). -/
set_option autoImplicit false

-- Frozen theorems.
assert_no_sorry SupercriticalConformalCovariance.conformal_covariance
#print axioms SupercriticalConformalCovariance.conformal_covariance
assert_no_sorry SupercriticalConformalCovariance.domainMetric_ae_eq_of_isDomainRealization
#print axioms SupercriticalConformalCovariance.domainMetric_ae_eq_of_isDomainRealization

-- Theorem 1.1 for every ξ > 0.
assert_no_sorry SupercriticalConformalCovariance.Root.conformal_covariance_all_xi
#print axioms SupercriticalConformalCovariance.Root.conformal_covariance_all_xi

/-- The all-ξ theorem implies the frozen Theorem 1.1 (drop the hypothesis `xiCrit < ξ`). -/
example : type_of% @SupercriticalConformalCovariance.conformal_covariance :=
  fun ξ _ => SupercriticalConformalCovariance.Root.conformal_covariance_all_xi ξ

/-- The two statements differ exactly by that hypothesis. -/
example : (type_of% @SupercriticalConformalCovariance.conformal_covariance) =
    ∀ ξ : Set.Ioi (0 : ℝ), SupercriticalConformalCovariance.xiCrit < (ξ : ℝ) →
      type_of% (SupercriticalConformalCovariance.Root.conformal_covariance_all_xi ξ) := rfl

-- Gwynne–Miller form: Axiom IV on the field's own probability space (one law; countably many laws and maps).
assert_no_sorry SupercriticalConformalCovariance.GMForm.gm_axiomIV_on_base
#print axioms SupercriticalConformalCovariance.GMForm.gm_axiomIV_on_base
assert_no_sorry SupercriticalConformalCovariance.GMForm.exists_countably_universal_gm_axiomIV_on_base
#print axioms SupercriticalConformalCovariance.GMForm.exists_countably_universal_gm_axiomIV_on_base

-- Gwynne–Miller form: the intermediate statements on extensions of the probability space.
assert_no_sorry SupercriticalConformalCovariance.GMForm.gm_direction_of_root
#print axioms SupercriticalConformalCovariance.GMForm.gm_direction_of_root
assert_no_sorry SupercriticalConformalCovariance.GMForm.gm_zeroBoundary_covariance_on_extension
#print axioms SupercriticalConformalCovariance.GMForm.gm_zeroBoundary_covariance_on_extension
assert_no_sorry SupercriticalConformalCovariance.GMForm.exists_fieldwise_gm_axiomIV_on_extension
#print axioms SupercriticalConformalCovariance.GMForm.exists_fieldwise_gm_axiomIV_on_extension
assert_no_sorry SupercriticalConformalCovariance.GMForm.exists_countably_universal_gm_axiomIV_on_extensions
#print axioms SupercriticalConformalCovariance.GMForm.exists_countably_universal_gm_axiomIV_on_extensions
