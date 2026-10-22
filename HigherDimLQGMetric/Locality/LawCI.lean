import HigherDimLQGMetric.Locality.ScaledChain
import LQGMetric.Papers.DFGPS.L2_17Core3G

/-! Transfer conditional independence through two representations of the
same marked metric law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HigherDimLQGMetric

theorem l7a_condIndepEv_of_equal_laws
    {Ω E S : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    [mS : MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure E) [IsProbabilityMeasure Q]
    (X : Ω → S) (Y : E → S) (hX : Measurable X) (hY : Measurable Y)
    (hlaw : Q.map Y = P.map X)
    (G A B : MeasurableSpace S)
    (hG : G ≤ mS) (hA : A ≤ mS) (hB : B ≤ mS)
    (hCI : LQGMetric.CondIndepEv (G.comap Y) (A.comap Y) (B.comap Y) Q) :
    LQGMetric.CondIndepEv (G.comap X) (A.comap X) (B.comap X) P := by
  letI : MeasurableSpace S := mS
  have hLawCI : LQGMetric.CondIndepEv G A B (Q.map Y) :=
    LQGMetric.DFGPS.L217.condIndepEv_map hY hG hA hB hCI
  rw [hlaw] at hLawCI
  exact LQGMetric.DFGPS.L217.condIndepEv_comap_of_map hX hG hA hB hLawCI

end HigherDimLQGMetric
