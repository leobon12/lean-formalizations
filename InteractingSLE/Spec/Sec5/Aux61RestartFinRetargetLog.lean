import InteractingSLE.Spec.Sec5.Aux61RestartFinActual

/-!
# The inherited branch of right-target retargeting

Packet PROVE-AUX61-R1. `-2 log(1-z)` is an analytic derivative logarithm of
`z/(1-z)` on H, with value zero at the original seed. Pulling the canonical
retained-hull logarithm back by this map uses the exact analytic chain rule.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61Restart

open Restart

theorem stripRightRetarget_eq (z : ℂ) : stripRightRetarget z = z / (1 - z) := by
  simp only [stripRightRetarget, QuantumZipper.CA.realMobius, ofReal_one, one_mul,
    ofReal_zero, add_zero, ofReal_neg, neg_one_mul]
  congr 1
  ring

/-- The branch of the target change fixed at the original seed, with no reset. -/
def stripRightRetargetLog (z : ℂ) : ℂ := -2 * log (1 - z)

theorem isDerivLog_stripRightRetarget :
    IsDerivLog stripRightRetarget stripRightRetargetLog H := by
  have hslit : ∀ z ∈ H, 1 - z ∈ slitPlane := by
    intro z hz
    apply Or.inr
    rw [sub_im, one_im, zero_sub]
    exact neg_ne_zero.mpr (ne_of_gt hz)
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · exact (((differentiableAt_log (hslit z hz)).comp z
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)).const_mul
        (-2 : ℂ)).differentiableWithinAt
  · have hne : 1 - z ≠ 0 := slitPlane_ne_zero (hslit z hz)
    have hder : deriv stripRightRetarget z = ((1 - z) ^ 2)⁻¹ := by
      have hd := ((hasDerivAt_id z).div
        ((hasDerivAt_const z 1).sub (hasDerivAt_id z)) hne).deriv
      change deriv (fun w : ℂ => w / (1 - w)) z = _ at hd
      calc
        deriv stripRightRetarget z =
            (1 * (1 - z) - z * (0 - 1)) / (1 - z) ^ 2 := by
          rw [show stripRightRetarget = (fun w : ℂ => w / (1 - w)) from
            funext stripRightRetarget_eq]
          exact hd
        _ = ((1 - z) ^ 2)⁻¹ := by field_simp; ring
    rw [stripRightRetargetLog, hder,
      show -2 * log (1 - z) = -((2 : ℕ) * log (1 - z)) by push_cast; ring,
      exp_neg, exp_nat_mul, exp_log hne]

/-- The retargeting branch is fixed at zero at the original seed in Q. -/
theorem tendsto_stripRightRetargetLog_seed :
    Tendsto stripRightRetargetLog (𝓝 (0 : ℂ)) (𝓝 0) := by
  have hc : ContinuousAt stripRightRetargetLog (0 : ℂ) := by
    have hlin : ContinuousAt (fun z : ℂ => 1 - z) 0 :=
      continuousAt_const.sub continuousAt_id
    have hlog : ContinuousAt log ((fun z : ℂ => 1 - z) 0) := by
      simpa only [sub_zero] using (continuousAt_clog one_mem_slitPlane)
    exact (hlog.comp hlin).const_mul (-2 : ℂ)
  simpa only [stripRightRetargetLog, sub_zero, log_one, mul_zero] using hc.tendsto

/-- The inherited physical logarithm of the retained chart before translating
its seed to zero. -/
def physicalRestartLog (B : Set ℂ) (z : ℂ) : ℂ :=
  canonDerivLog B (stripRightRetarget z) + stripRightRetargetLog z

theorem isDerivLog_physicalRestartLog {D B : Set ℂ} (hDo : IsOpen D)
    (hB : IsHPHull B) (hDH : D ⊆ H)
    (hmaps : MapsTo stripRightRetarget D (H \ B)) :
    IsDerivLog (ConformalImage.mapOut B ∘ stripRightRetarget) (physicalRestartLog B) D :=
  IsDerivLog.comp hDo hB.isOpen (ConformalImage.isMapOut_mapOut hB).1.1
    (isConformalBijection_stripRightRetarget.1.mono hDH) hmaps
    (isCanonicalDerivLog_canonDerivLog hB).1 (isDerivLog_stripRightRetarget.mono hDH)

/-- The physical retained logarithm inherits the exact additional logarithm
from the own retargeted hull, including its integer branch. -/
theorem physicalRestartLog_chain {A B : Set ℂ} (hA : IsHPHull A) (hB : IsHPHull B)
    (hAB : A ⊆ B) {z : ℂ} (hz : stripRightRetarget z ∈ H \ B) :
    physicalRestartLog B z =
      restartAdditionalLog A B (ConformalImage.mapOut A (stripRightRetarget z)) +
        physicalRestartLog A z := by
  rw [physicalRestartLog, restart_canonicalLog_chain hA hB hAB hz, physicalRestartLog]
  exact add_assoc _ _ _

end InteractingSLE.Sec5.Aux61Restart
