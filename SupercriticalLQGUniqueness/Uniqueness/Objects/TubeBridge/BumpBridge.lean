import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge.TubeSetBridge
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Bump




 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge

theorem bumpFormula_eq_convolution (T : Objects.CorrectedEvent.TubeData) (Amax Asup : ℝ) (x : ℂ) :
    Objects.CorrectedEvent.bumpFormula T Amax Asup x =
      Amax * convolution
        ((Objects.CorrectedEvent.tubeV T (Asup / 2)).indicator (fun _ => (1 : ℝ)))
        (fun y => T.mollifier y) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  classical
  unfold Objects.CorrectedEvent.bumpFormula
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rfl


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge
