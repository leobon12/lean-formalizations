import SupercriticalLQGUniqueness.B2.DG20Lim.FullGoodNormalize
import SupercriticalLQGUniqueness.B2.DG20Lim.GoodAnnulusCoordLaw

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem finite_bad_ratio_probability_of_joint_coord_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (D : Ω → ContMetric) (hD : AEMeasurable D P)
    (Y : Ω' → (CoordJ → ℝ) × RatCoords) (hY : Measurable Y)
    (hLaw : P'.map Y = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)))
    (A : ℕ → RatAnnulus) (S : Finset ℕ) (C b : ℝ≥0∞)
    (hSource : P {ω | ∀ i ∈ S,
      C * finiteCircleCoords (D ω) ((A i).inner, (A i).outer) <
        finiteAroundCoords (D ω) (A i)} ≤ b) :
    P' {ω | ∀ i ∈ S,
      C * (Y ω).2.1 ((A i).inner, (A i).outer) <
        (Y ω).2.2 (A i)} ≤ b := by
  let bad : Set ((CoordJ → ℝ) × RatCoords) :=
    {v | ∀ i ∈ S, C * v.2.1 ((A i).inner, (A i).outer) < v.2.2 (A i)}
  have hbad : MeasurableSet bad := by
    classical
    have heq : bad = ⋂ i ∈ S,
        {v : (CoordJ → ℝ) × RatCoords |
          C * v.2.1 ((A i).inner, (A i).outer) < v.2.2 (A i)} := by
      ext v
      simp only [bad, mem_setOf_eq, mem_iInter]
    rw [heq]
    apply Finset.measurableSet_biInter S
    intro i hi
    have hAcross : Measurable fun v : (CoordJ → ℝ) × RatCoords =>
        v.2.1 ((A i).inner, (A i).outer) :=
      (measurable_pi_apply ((A i).inner, (A i).outer)).comp
        (measurable_fst.comp measurable_snd)
    have hAround : Measurable fun v : (CoordJ → ℝ) × RatCoords =>
        v.2.2 (A i) :=
      (measurable_pi_apply (A i)).comp (measurable_snd.comp measurable_snd)
    exact measurableSet_lt (measurable_const.mul hAcross) hAround
  let V : Ω → (CoordJ → ℝ) × RatCoords :=
    fun ω => (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)
  have hV : Measurable V :=
    ((measurable_pairJ ⊤).comp hh).prodMk
      (measurable_measurableRatCoordsVersion D hD)
  have hVersion : V ⁻¹' bad =ᵐ[P]
      {ω | ∀ i ∈ S,
        C * finiteCircleCoords (D ω) ((A i).inner, (A i).outer) <
          finiteAroundCoords (D ω) (A i)} := by
    filter_upwards [ae_eq_measurableRatCoordsVersion D hD] with ω hω
    change (∀ i ∈ S,
      C * (measurableRatCoordsVersion D hD ω).1 ((A i).inner, (A i).outer) <
        (measurableRatCoordsVersion D hD ω).2 (A i)) = _
    rw [← hω]
    rfl
  calc
    P' {ω | ∀ i ∈ S,
      C * (Y ω).2.1 ((A i).inner, (A i).outer) < (Y ω).2.2 (A i)} =
        (P'.map Y) bad := by rw [Measure.map_apply hY hbad]; rfl
    _ = (P.map V) bad := by rw [hLaw]
    _ = P (V ⁻¹' bad) := Measure.map_apply hV hbad
    _ = P {ω | ∀ i ∈ S,
        C * finiteCircleCoords (D ω) ((A i).inner, (A i).outer) <
          finiteAroundCoords (D ω) (A i)} := measure_congr hVersion
    _ ≤ b := hSource

end SupercriticalLQGUniqueness.B2.DG20Lim
