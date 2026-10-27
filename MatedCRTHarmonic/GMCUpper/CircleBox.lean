import MatedCRTHarmonic.GMCUpper.Model
import MatedCRTHarmonic.GMCFacts.OuterMoment
import LQGMetric.Papers.DGo.CouplingTail

/-!
# A Gaussian tail on one circle-average box

For a normalized whole-plane GFF, the circle-average process at radius `r`
has variance at most `log(1/r) + O(1)` on a bounded box and increments of
variance at most `2|z-w|/r`. Borell--TIS and the pinned Fernique estimate
therefore give a tail with an `O(1)` supremum offset on a box of side `r`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric LQGMetric

namespace MatedCRTHarmonic.GMCUpper

/-- A jointly continuous circle-average version of a normalized whole-plane
GFF has the same finite-dimensional Gaussian law as the canonical version. -/
theorem isGFFCircleAverage_of_version {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
    (hX : IsNormalizedWPGFF X P)
    (hH : DFGPS.IsCircleAvgVersion X P H) :
    LQGDimension.IsGFFCircleAverage H P := by
  obtain ⟨H₀, hH₀, hG₀⟩ := exists_circleAvgVersion_normalized hX
  have hae : ∀ r, 0 < r → ∀ z, H r z =ᵐ[P] H₀ r z := by
    intro r hr z
    exact (hH.ae_eq r hr z).trans (hH₀.ae_eq r hr z).symm
  refine ⟨hG₀.isProbabilityMeasure, ?_, ?_, ?_, ?_⟩
  · exact hG₀.isGaussianProcess.congr fun p => (hae p.1 p.1.2 p.2).symm
  · intro r hr z
    rw [integral_congr_ae (hae r hr z)]
    exact hG₀.integral_eq_zero r hr z
  · intro r hr s hs z w
    rw [LQGMetric.CircleAvg.covariance_congr_ae (hae r hr z) (hae s hs w)]
    exact hG₀.covariance_eq r hr s hs z w
  · intro r hr ω
    exact continuousOn_univ.1
      ((hH.cont ω).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun z _ => ⟨hr, mem_univ z⟩))

/-- The sharp-scale one-box tail used by the covering argument for
`CircleAverageSupBoundModel`. -/
theorem circleAverage_oneBox_tail {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
    (hX : IsNormalizedWPGFF X P)
    (hH : DFGPS.IsCircleAvgVersion X P H)
    (hG : LQGDimension.IsGFFCircleAverage H P)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {y : ℂ} (hy : ‖y‖ ≤ 2) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | SupTail.ferniqueCF * Real.sqrt 2 + u ≤
      ⨆ z : SupTail.ferniqueBox y r, H r z ω} ≤
      Real.exp (-u ^ 2 / (2 * (Real.sqrt (-Real.log r + 2 * Real.log 5 + 1)) ^ 2)) := by
  let Y : ℂ → Ω → ℝ := fun z ω => H r z ω
  have hYG : IsGaussianProcess Y P :=
    hG.isGaussianProcess.comp_right (fun z => (⟨r, hr⟩, z))
  have hY0 : ∀ z, ∫ ω, Y z ω ∂P = 0 := fun z => hG.integral_eq_zero r hr z
  have hYc : ∀ ω, ContinuousOn (fun z => Y z ω) (SupTail.ferniqueBox y r) :=
    fun ω => (hG.continuous r hr ω).continuousOn
  have hinc : ∀ z ∈ SupTail.ferniqueBox y r, ∀ w ∈ SupTail.ferniqueBox y r,
      ∫ ω, (Y w ω - Y z ω) ^ 2 ∂P ≤ (2 / r) * ‖z - w‖ := by
    intro z _ w _
    have h := hH.integral_sq_sub hX.1 hr hr w z
    simp only [sub_self, abs_zero, zero_add, min_self] at h
    calc ∫ ω, (Y w ω - Y z ω) ^ 2 ∂P ≤ 2 * (‖w - z‖ / r) := h
      _ = (2 / r) * ‖z - w‖ := by rw [norm_sub_rev]; ring
  let s2 : ℝ := -Real.log r + 2 * Real.log 5 + 1
  have hs2 : 0 < s2 := by
    dsimp [s2]
    have hlog : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
    have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    linarith
  have hvar : ∀ z ∈ SupTail.ferniqueBox y r, Var[Y z; P] ≤ (Real.sqrt s2) ^ 2 := by
    intro z hz
    have hyz : ‖z‖ ≤ 4 := by
      have hyy : y ∈ SupTail.ferniqueBox y r := SupTail.mem_ferniqueBox_self hr.le
      have hdist := DGo.norm_sub_le_of_mem_ferniqueBox hyy hz
      calc ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
            have := norm_add_le (z - y) y
            simpa only [sub_add_cancel] using this
        _ ≤ 4 := by rw [norm_sub_rev] at hdist; linarith
    have hm : AEMeasurable (Y z) P := hYG.aemeasurable z
    rw [← covariance_self hm, hG.covariance_eq r hr r hr z z,
      Real.sq_sqrt hs2.le]
    exact (GMCFacts.gffCircleCov_self_le hr hr1 hyz).trans (by dsimp [s2]; linarith)
  have htail := DGo.box_sup_tail hYG hY0 hr (div_pos (by norm_num) hr)
    hYc (fun z hz w hw => hinc z hz w hw) hvar hu
  have he : (2 / r) * r = 2 := div_mul_cancel₀ 2 hr.ne'
  simpa only [he] using htail

/-- The same one-box estimate for the negative of the circle-average field. -/
theorem circleAverage_oneBox_tail_neg {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
    (hX : IsNormalizedWPGFF X P)
    (hH : DFGPS.IsCircleAvgVersion X P H)
    (hG : LQGDimension.IsGFFCircleAverage H P)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {y : ℂ} (hy : ‖y‖ ≤ 2) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | SupTail.ferniqueCF * Real.sqrt 2 + u ≤
      ⨆ z : SupTail.ferniqueBox y r, -H r z ω} ≤
      Real.exp (-u ^ 2 / (2 * (Real.sqrt (-Real.log r + 2 * Real.log 5 + 1)) ^ 2)) := by
  let Y : ℂ → Ω → ℝ := fun z ω => -H r z ω
  have hYG : IsGaussianProcess Y P := by
    have h := (hG.isGaussianProcess.comp_right (fun z => (⟨r, hr⟩, z))).smul
      (fun _ => (-1 : ℝ))
    simpa [Y, smul_eq_mul] using h
  have hY0 : ∀ z, ∫ ω, Y z ω ∂P = 0 := by
    intro z
    simp only [Y, integral_neg, hG.integral_eq_zero r hr z, neg_zero]
  have hYc : ∀ ω, ContinuousOn (fun z => Y z ω) (SupTail.ferniqueBox y r) :=
    fun ω => (hG.continuous r hr ω).neg.continuousOn
  have hinc : ∀ z ∈ SupTail.ferniqueBox y r, ∀ w ∈ SupTail.ferniqueBox y r,
      ∫ ω, (Y w ω - Y z ω) ^ 2 ∂P ≤ (2 / r) * ‖z - w‖ := by
    intro z _ w _
    have h := hH.integral_sq_sub hX.1 hr hr w z
    simp only [sub_self, abs_zero, zero_add, min_self] at h
    have he : (fun ω => (Y w ω - Y z ω) ^ 2) =
        fun ω => (H r w ω - H r z ω) ^ 2 := by
      funext ω
      dsimp [Y]
      ring
    rw [he]
    calc ∫ ω, (H r w ω - H r z ω) ^ 2 ∂P ≤ 2 * (‖w - z‖ / r) := h
      _ = (2 / r) * ‖z - w‖ := by rw [norm_sub_rev]; ring
  let s2 : ℝ := -Real.log r + 2 * Real.log 5 + 1
  have hs2 : 0 < s2 := by
    dsimp [s2]
    have hlog : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
    have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    linarith
  have hvar : ∀ z ∈ SupTail.ferniqueBox y r, Var[Y z; P] ≤ (Real.sqrt s2) ^ 2 := by
    intro z hz
    have hyz : ‖z‖ ≤ 4 := by
      have hyy : y ∈ SupTail.ferniqueBox y r := SupTail.mem_ferniqueBox_self hr.le
      have hdist := DGo.norm_sub_le_of_mem_ferniqueBox hyy hz
      calc ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
            have := norm_add_le (z - y) y
            simpa only [sub_add_cancel] using this
        _ ≤ 4 := by rw [norm_sub_rev] at hdist; linarith
    have hm : AEMeasurable (H r z) P :=
      (hG.isGaussianProcess.comp_right (fun z => (⟨r, hr⟩, z))).aemeasurable z
    change Var[-(H r z); P] ≤ _
    rw [variance_neg, ← covariance_self hm, hG.covariance_eq r hr r hr z z,
      Real.sq_sqrt hs2.le]
    exact (GMCFacts.gffCircleCov_self_le hr hr1 hyz).trans (by dsimp [s2]; linarith)
  have htail := DGo.box_sup_tail hYG hY0 hr (div_pos (by norm_num) hr)
    hYc (fun z hz w hw => hinc z hz w hw) hvar hu
  have he : (2 / r) * r = 2 := div_mul_cancel₀ 2 hr.ne'
  simpa only [he] using htail

end MatedCRTHarmonic.GMCUpper
