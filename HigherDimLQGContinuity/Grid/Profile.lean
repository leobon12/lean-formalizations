import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Norm.Rho
import HigherDimLQGContinuity.Param.Defs
import HigherDimLQGMetric.Frozen.Theorem12

/-!
# Logarithmic profiles on a positive parameter window

The canonical strong assignment is chosen only for constructing the countable grids.  All version
statements quantify over arbitrary strong assignments.  The profile transforms are those of Part C,
§5.1 of the corrected blueprint.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- An arbitrary, but fixed, strong assignment at each subcritical positive parameter. -/
def strongAt (d : ℕ) (ξ : ℝ) : DistRd d → ContMetric d :=
  by
    classical
    exact if h : 3 ≤ d ∧ ξ ∈ subcritSet d then
      Classical.choose (theorem12 d ξ h.1 h.2.1 h.2.2).1
    else fun _ => HigherDimLQGMetric.fieldLfppMetric 0 0

theorem strongAt_spec {d : ℕ} (hd : 3 ≤ d) {ξ : ℝ} (hξ : ξ ∈ subcritSet d) :
    IsStrongExpMetric d ξ (distExp d ξ) (strongAt d ξ) := by
  classical
  unfold strongAt
  split_ifs with h
  · exact (Classical.choose_spec (theorem12 d ξ h.1 h.2.1 h.2.2).1).1
  · exact (h ⟨hd, hξ⟩).elim

/-- The inverse transform to the logarithmic profile on nonnegative functions. -/
def expProfile {d : ℕ} (F : C(Rd d × Rd d, ℝ)) : C(Rd d × Rd d, ℝ) :=
  ⟨fun p => Real.exp (F p) - 1, (Real.continuous_exp.comp F.continuous).sub continuous_const⟩

theorem continuous_logProfile {d : ℕ} :
    Continuous (logProfile (d := d)) := by
  have h := ContinuousMap.continuous_postcomp (X := Rd d × Rd d)
    (⟨fun u : ℝ => Real.log (1 + |u|),
    (continuous_const.add continuous_id.abs).log fun u =>
      (show (0 : ℝ) < 1 + |u| by positivity).ne'⟩ : C(ℝ, ℝ))
  exact h

theorem continuous_expProfile {d : ℕ} :
    Continuous (expProfile (d := d)) := by
  have h := ContinuousMap.continuous_postcomp (X := Rd d × Rd d)
    (⟨fun u : ℝ => Real.exp u - 1, Real.continuous_exp.sub continuous_const⟩ : C(ℝ, ℝ))
  exact h

theorem expProfile_logProfile {d : ℕ} (F : C(Rd d × Rd d, ℝ))
    (hF : 0 ≤ F) : expProfile (logProfile F) = F := by
  ext p
  have hp : 0 ≤ F p := hF p
  simp only [expProfile, logProfile, ContinuousMap.coe_mk]
  rw [abs_of_nonneg hp, Real.exp_log (by linarith : 0 < 1 + F p)]
  ring

theorem logProfile_nonneg {d : ℕ} (F : C(Rd d × Rd d, ℝ)) : 0 ≤ logProfile F := by
  intro p
  exact Real.log_nonneg (by have := abs_nonneg (F p); linarith)

/-- The canonical log-profile, defined at every parameter; outside the subcritical set it is junk. -/
def gridProfile (d : ℕ) (ξ : ℝ) (g : DistRd d) : C(Rd d × Rd d, ℝ) :=
  logProfile (rho (strongAt d ξ) g).1

theorem measurable_gridProfile {d : ℕ} (hd : 3 ≤ d) {ξ : ℝ} (hξ : ξ ∈ subcritSet d) :
    Measurable (gridProfile d ξ) := by
  exact continuous_logProfile.measurable.comp
    ((measurable_subtype_coe.comp
      (measurable_rho (strongAt_spec hd hξ).measurable)))

theorem gridProfile_nonneg (d : ℕ) (ξ : ℝ) (g : DistRd d) :
    0 ≤ gridProfile d ξ g := logProfile_nonneg _

end HigherDimLQGContinuity
