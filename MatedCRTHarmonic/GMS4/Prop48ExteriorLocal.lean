import MatedCRTHarmonic.GMS4.Prop48FarA3

/-!
# Exterior measurability of a distant local observation

For off-diagonal pairs in [18] (4.36), the local field restriction and its
circle averages at the distant point lie in the exterior sigma algebra at the
first point. This is the geometric locality needed to apply Appendix A.3.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Metric Set LQGMetric LQGMetric.Blueprint

namespace MatedCRTHarmonic.GMS4

/-- The full local field observation at `w` is measurable in the exterior
field sigma algebra about `z` when its ball and averaging circle miss that
exterior ball. -/
theorem prop48_localObservation_exterior_measurable
    {Ω : Type} [MeasurableSpace Ω] (h hIG : Ω → DistC)
    (localRadius averageRadius r : ℝ) (z w : ℂ)
    (hball : (ballO w localRadius : Set ℂ) ⊆ (Metric.ball z r)ᶜ)
    (hsphere : Metric.sphere w |averageRadius| ⊆ (Metric.ball z r)ᶜ) :
    Measurable[prop48ExteriorSigma h hIG r z]
      (prop48LocalFieldObservation h hIG localRadius averageRadius w) := by
  let m := prop48ExteriorSigma h hIG r z
  have hhfield : Measurable[m]
      (fun ω => restrictTo (ballO w localRadius) (h ω)) := by
    have hbase : Measurable[fieldSigma h (ballO w localRadius)]
        (fun ω => restrictTo (ballO w localRadius) (h ω)) :=
      comap_measurable _
    exact hbase.mono
      ((LQGMetric.DFGPS.L217.fieldSigma_le_fieldSigmaClosed_of_subset h hball).trans
        (le_sup_left : fieldSigmaClosed h (Metric.ball z r)ᶜ ≤ m)) le_rfl
  have hhIGfield : Measurable[m]
      (fun ω => restrictTo (ballO w localRadius) (hIG ω)) := by
    have hbase : Measurable[fieldSigma hIG (ballO w localRadius)]
        (fun ω => restrictTo (ballO w localRadius) (hIG ω)) :=
      comap_measurable _
    exact hbase.mono
      ((LQGMetric.DFGPS.L217.fieldSigma_le_fieldSigmaClosed_of_subset hIG hball).trans
        (le_sup_right : fieldSigmaClosed hIG (Metric.ball z r)ᶜ ≤ m)) le_rfl
  have hhavg : Measurable[m] (fun ω => circleAvg (h ω) averageRadius w) :=
    (GM.measurable_circleAvg_fieldSigmaClosed h averageRadius w hsphere).mono
      (le_sup_left : fieldSigmaClosed h (Metric.ball z r)ᶜ ≤ m) le_rfl
  have hhIGavg : Measurable[m] (fun ω => circleAvg (hIG ω) averageRadius w) :=
    (GM.measurable_circleAvg_fieldSigmaClosed hIG averageRadius w hsphere).mono
      (le_sup_right : fieldSigmaClosed hIG (Metric.ball z r)ᶜ ≤ m) le_rfl
  exact (hhfield.prodMk hhIGfield).prodMk (hhavg.prodMk hhIGavg)

/-- The source guard `|z-w|>2r` ensures exterior locality for a local ball
of radius at most `r` and the circle of radius `r`. -/
theorem prop48_localObservation_exterior_of_far
    {Ω : Type} [MeasurableSpace Ω] (h hIG : Ω → DistC)
    {localRadius r : ℝ} (hr : 0 ≤ r) (hlocal : localRadius ≤ r)
    (z w : ℂ) (hfar : 2 * r < dist z w) :
    Measurable[prop48ExteriorSigma h hIG r z]
      (prop48LocalFieldObservation h hIG localRadius r w) := by
  have hball : (ballO w localRadius : Set ℂ) ⊆ (Metric.ball z r)ᶜ := by
    intro y hy
    have hy' : dist y w < localRadius := by simpa [ballO] using hy
    change ¬ dist y z < r
    intro hnear
    have htri := dist_triangle z y w
    rw [dist_comm y z] at hnear
    linarith
  have hsphere : Metric.sphere w |r| ⊆ (Metric.ball z r)ᶜ := by
    intro y hy
    change dist y w = |r| at hy
    rw [abs_of_nonneg hr] at hy
    change ¬ dist y z < r
    intro hnear
    have htri := dist_triangle z y w
    rw [dist_comm y z] at hnear
    linarith
  exact prop48_localObservation_exterior_measurable h hIG localRadius r r z w
    hball hsphere

/-- An exterior-measurable version of the centered masked density at the
distant point. The version uses the source local factor and the actual
circle-average conditional mean, and agrees almost surely with (4.28). -/
theorem prop48_distant_centered_exterior_version
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hIG : Ω → DistC} {L : Prop48LocalizedObservable P}
    {ε q ζ γ : ℝ}
    (F : Prop48LocalObservableProducer P h hIG L ε q ζ γ)
    (z w : ℂ) (hw : w ∈ L.domain)
    (hr : 0 ≤ F.averageRadius)
    (hlocal : F.localRadius ≤ F.averageRadius)
    (hfar : 2 * F.averageRadius < dist z w) :
    ∃ Z : Ω → ℝ,
      StronglyMeasurable[prop48ExteriorSigma h hIG F.averageRadius z] Z ∧
      Z =ᵐ[P] prop48PointwiseCentered L w := by
  let Y : Ω → ℝ := prop48MaskedDensity L w
  let A : Ω → ℝ := P[Y | MeasurableSpace.comap
    (prop48CircleAverageObservation h hIG F.averageRadius w) inferInstance]
  let Z : Ω → ℝ := fun ω =>
    F.localFactor w (prop48LocalFieldObservation h hIG F.localRadius F.averageRadius w ω) -
      A ω
  have hobs : Measurable[prop48ExteriorSigma h hIG F.averageRadius z]
      (prop48LocalFieldObservation h hIG F.localRadius F.averageRadius w) :=
    prop48_localObservation_exterior_of_far h hIG hr hlocal z w hfar
  have hcircle : Measurable[prop48ExteriorSigma h hIG F.averageRadius z]
      (prop48CircleAverageObservation h hIG F.averageRadius w) :=
    measurable_snd.comp hobs
  have hA : StronglyMeasurable[prop48ExteriorSigma h hIG F.averageRadius z] A :=
    stronglyMeasurable_condExp.mono hcircle.comap_le
  have hZ : StronglyMeasurable[prop48ExteriorSigma h hIG F.averageRadius z] Z :=
    ((F.localFactor_measurable w).comp hobs).stronglyMeasurable.sub hA
  refine ⟨Z, hZ, ?_⟩
  filter_upwards [F.localFactor_eq_truncated_density w hw,
    F.conditionalMean_eq w hw] with ω hY hmean
  change F.localFactor w
      (prop48LocalFieldObservation h hIG F.localRadius F.averageRadius w ω) -
      A ω =
    (L.localEvent w).indicator (fun ω' => L.uStar ω' w) ω -
      L.conditionalMean ω w
  rw [hY]
  dsimp only [A, Y, prop48MaskedDensity]
  rw [F.averageRadius_eq]
  rw [F.averageRadius_eq] at hmean
  exact congrArg
    (fun a : ℝ => (L.localEvent w).indicator (fun ω' => L.uStar ω' w) ω - a)
    hmean.symm

end MatedCRTHarmonic.GMS4

