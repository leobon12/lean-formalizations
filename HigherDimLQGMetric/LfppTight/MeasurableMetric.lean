import HigherDimLQGMetric.B3.Interfaces
import HigherDimLQGMetric.Main.LFPPMedian

/-!
# Measurability of random continuous metric functions

The totalizer `toCMapRd` chooses zero on a discontinuous sample.  If the
underlying random function is continuous almost surely, coordinatewise a.e.
measurability is enough for the continuous-map-valued random variable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Coordinatewise a.e. measurability and a.s. continuity make the canonical
continuous-map totalization a.e. measurable. -/
theorem l6a_aemeasurable_toCMapRd {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Rd d × Rd d → ℝ)
    (hm : ∀ p, AEMeasurable (fun ω => X ω p) P)
    (hc : ∀ᵐ ω ∂P, Continuous (X ω)) :
    AEMeasurable (fun ω => toCMapRd (X ω)) P := by
  classical
  let Y : Rd d × Rd d → Ω → ℝ := fun p ω =>
    if hcont : Continuous (X ω) then X ω p else 0
  have hYc : ∀ ω, Continuous fun p => Y p ω := by
    intro ω
    by_cases hcont : Continuous (X ω)
    · have heq : (fun p => Y p ω) = X ω := by
        funext p
        exact dite_eq_left hcont
      rw [heq]
      exact hcont
    · have heq : (fun p => Y p ω) = fun _ => 0 := by
        funext p
        exact dite_eq_right hcont
      rw [heq]
      exact continuous_const
  have hYm : ∀ p, AEMeasurable (Y p) P := by
    intro p
    have heq : Y p =ᵐ[P] fun ω => X ω p := by
      filter_upwards [hc] with ω hω
      exact dite_eq_left hω
    exact (aemeasurable_congr heq.symm).1 (hm p)
  have hCM : AEMeasurable
      (fun ω => (⟨fun p => Y p ω, hYc ω⟩ : C(Rd d × Rd d, ℝ))) P := by
    have key : @Measurable (NullMeasurableSpace Ω P) C(Rd d × Rd d, ℝ) _ _
        (fun ω => (⟨fun p => Y p ω, hYc ω⟩ : C(Rd d × Rd d, ℝ))) := by
      refine (ContinuousMap.measurable_iff_eval (Z := NullMeasurableSpace Ω P)).2 fun p => ?_
      exact (hYm p).nullMeasurable
    exact (show NullMeasurable
      (fun ω => (⟨fun p => Y p ω, hYc ω⟩ : C(Rd d × Rd d, ℝ))) P
      from fun s hs => key hs).aemeasurable
  have heq : (fun ω => (⟨fun p => Y p ω, hYc ω⟩ : C(Rd d × Rd d, ℝ))) =
      fun ω => toCMapRd (X ω) := by
    funext ω
    by_cases hcont : Continuous (X ω)
    · apply ContinuousMap.ext
      intro p
      simp only [Y, toCMapRd, dite_eq_left hcont]
    · apply ContinuousMap.ext
      intro p
      simp only [Y, toCMapRd, dite_eq_right hcont, ContinuousMap.zero_apply]
      rfl
  rwa [heq] at hCM

end HigherDimLQGMetric
