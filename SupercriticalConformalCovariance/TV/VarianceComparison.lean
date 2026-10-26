import Mathlib.Probability.Moments.Variance

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalConformalCovariance.TV

/-- A domain with larger zero-boundary variance has smaller complementary
harmonic variance when both independent sums have the same law. -/
theorem harmonic_variance_le_of_zb_variance_mono
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X H X' H' : Ω → ℝ}
    (hX : MemLp X 2 P) (hH : MemLp H 2 P)
    (hX' : MemLp X' 2 P) (hH' : MemLp H' 2 P)
    (hind : IndepFun X H P) (hind' : IndepFun X' H' P)
    (hsum : Var[fun ω => X ω + H ω; P] =
      Var[fun ω => X' ω + H' ω; P])
    (hmono : Var[X'; P] ≤ Var[X; P]) :
    Var[H; P] ≤ Var[H'; P] := by
  rw [hind.variance_fun_add hX hH, hind'.variance_fun_add hX' hH'] at hsum
  linarith


end SupercriticalConformalCovariance.TV
