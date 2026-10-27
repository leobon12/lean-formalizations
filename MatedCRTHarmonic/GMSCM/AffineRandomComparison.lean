import MatedCRTHarmonic.GMSCM.AffineNormalization
import MatedCRTHarmonic.GMSCM.MarkovComparison
import LQGMetric.Papers.DG.L2_2D

/-!
# Comparing a raw translated GFF with its unit-circle recentering

The random circle average is cut off inside a larger Markov disk. The cutoff
is one on the observation disk, so the local shifted law is exactly the raw
translate. The Gaussian square moment gives an `L^p` density for some `p>1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric
open LQGMetric LQGMetric.GM LQGMetric.MarkovZB LQGMetric.CircleAvg
open MatedCRTHarmonic.MoTPort MatedCRTHarmonic.MoTPort.GFFBdry
open MatedCRTHarmonic.MoTPort.IG.GFFAbsCont
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCM

/-- On the smaller observation disk, the smooth cutoff of a constant has the
same distributional restriction as the constant itself. -/
theorem resOn_cutoff_const {V W : Opens ℂ} (hWV : W ≤ V)
    (χ : zsSub (V : Set ℂ)) (hχ : ∀ z ∈ (W : Set ℂ), χ.1 z = 1)
    (k : DistC) (c : ℝ) :
    resOn W V (restrictTo V k + ofFunOn V ((0 : zsSub (V : Set ℂ)) + c • (-χ)).1) =
      restrictTo W (addConst k (-c)) := by
  ext φ
  rw [resOn_add, resOn_restrictTo hWV]
  rw [LQGMetric.DG.L22T.restrictTo_addConst]
  simp only [add_apply]
  rw [resOn_apply, ofFunOn_zsSub_apply]
  have he : ∫ x, ((0 : zsSub (V : Set ℂ)) + c • (-χ)).1 x *
      (GM.testIncl W V φ) x = (∫ x, φ x) * -c := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ (W : Set ℂ)
    · simp only [GM.coe_testIncl hWV]
      simp [hχ x hx, mul_comm]
    · have hφ : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport fun ht => hx (φ.tsupport_subset ht)
      simp [GM.coe_testIncl hWV, hφ]
  rw [he]

/-- After translation, the local raw GFF law dominates the recentered law
with a density having a finite moment above one. The hypotheses express the
separation of the Markov disk from the two normalization circles. -/
theorem rawTranslate_recentered_local_reverse
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (w : ℂ) {V W : Opens ℂ}
    (hWV : W ≤ V) (hK : IsCompact (closure (W : Set ℂ)))
    (hKV : closure (W : Set ℂ) ⊆ (V : Set ℂ))
    (hadm : ZBAdmissible V) (hne : (V : Set ℂ).Nonempty)
    (hV₁ : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1))
    (hVR : Disjoint (V : Set ℂ) (sphere (-w) 1)) :
    ∃ p : ℝ, 1 < p ∧ p < 2 ∧ ∃ D : DistOn W → ℝ≥0∞,
      Measurable D ∧
      P.map (fun ω => restrictTo W (recenteredTranslate h w ω)) =
        (P.map (fun ω => restrictTo W (affineComp 1 w (h ω)))).withDensity D ∧
      ∫⁻ y, D y ^ p ∂(P.map fun ω => restrictTo W (affineComp 1 w (h ω))) < ⊤ := by
  let : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  obtain ⟨χ, hχ, hχ1⟩ := exists_cutoff_of_isCompact hK V.isOpen hKV
  let χz : zsSub (V : Set ℂ) := ⟨χ, hχ⟩
  let t := recenteredTranslate h w
  have ht : IsNormalizedWPGFF t P := (recenteredTranslate_normalized hh w).1
  obtain ⟨M⟩ := exists_localMarkov ht V hV₁
  obtain ⟨p, hp, hp2, D, hDm, hLaw, hMom⟩ :=
    M.randomShift_local_reverse ht hWV hadm hne 1 (-w) one_pos hV₁ hVR
      0 (-χz)
  have hshift : (fun ω => resOn W V
      (restrictTo V (t ω) + ofFunOn V
        ((0 : zsSub (V : Set ℂ)) + cInc t 1 (-w) 1 0 ω • (-χz)).1)) =ᵐ[P]
      (fun ω => restrictTo W (affineComp 1 w (h ω))) := by
    filter_upwards [recenteredTranslate_cInc hh w] with ω hω
    rw [resOn_cutoff_const hWV χz (fun z hz => hχ1 z (subset_closure hz))]
    rw [hω]
    simpa only [neg_neg] using
      (congrArg (restrictTo W) (rawTranslate_eq_recentered_addConst h w ω)).symm
  refine ⟨p, hp, hp2, D, hDm, ?_, ?_⟩
  · rw [← Measure.map_congr hshift]
    exact hLaw
  · rw [← Measure.map_congr hshift]
    exact hMom

/-- The concrete normalization comparison for translation by `w=1/2` on an
origin-containing disk. -/
theorem halfRawTranslate_recentered_local_reverse
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) {ρ : ℝ} (hρ : ρ < 1 / 4) :
    let W : Opens ℂ := ⟨ball (0 : ℂ) ρ, isOpen_ball⟩
    let w : ℂ := ((1 / 2 : ℝ) : ℂ)
    ∃ p : ℝ, 1 < p ∧ p < 2 ∧ ∃ D : DistOn W → ℝ≥0∞,
      Measurable D ∧
      P.map (fun ω => restrictTo W (recenteredTranslate h w ω)) =
        (P.map (fun ω => restrictTo W (affineComp 1 w (h ω)))).withDensity D ∧
      ∫⁻ y, D y ^ p ∂(P.map fun ω => restrictTo W (affineComp 1 w (h ω))) < ⊤ := by
  let W : Opens ℂ := ⟨ball (0 : ℂ) ρ, isOpen_ball⟩
  let V : Opens ℂ := ⟨ball (0 : ℂ) (1 / 4), isOpen_ball⟩
  let w : ℂ := ((1 / 2 : ℝ) : ℂ)
  have hw : ‖w‖ = 1 / 2 := by simp [w]
  have hclose : closure (W : Set ℂ) ⊆ closedBall (0 : ℂ) ρ :=
    Metric.closure_ball_subset_closedBall
  have hK : IsCompact (closure (W : Set ℂ)) :=
    (isCompact_closedBall (0 : ℂ) ρ).of_isClosed_subset isClosed_closure hclose
  have hKV : closure (W : Set ℂ) ⊆ (V : Set ℂ) := by
    intro x hx
    have hxρ : ‖x‖ ≤ ρ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hclose hx
    simpa [V, Metric.mem_ball, dist_zero_right] using (lt_of_le_of_lt hxρ hρ)
  have hWV : W ≤ V := fun _ hx => hKV (subset_closure hx)
  have hadm : ZBAdmissible V := zbAdmissible_of_isBounded isBounded_ball
  have hne : (V : Set ℂ).Nonempty := ⟨0, by simp [V]⟩
  have hV₁ : Disjoint (V : Set ℂ) (sphere (0 : ℂ) 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hx1
    have hsmall : ‖x‖ < 1 / 4 := by
      simpa [V, Metric.mem_ball, dist_zero_right] using hx
    have hnorm : ‖x‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hx1
    linarith
  have hVR : Disjoint (V : Set ℂ) (sphere (-w) 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hx1
    have hsmall : ‖x‖ < 1 / 4 := by
      simpa [V, Metric.mem_ball, dist_zero_right] using hx
    have hnorm : ‖x + w‖ = 1 := by simpa [mem_sphere, dist_eq_norm] using hx1
    have htri := norm_add_le x w
    rw [hw] at htri
    linarith
  exact rawTranslate_recentered_local_reverse hh w hWV hK hKV hadm hne hV₁ hVR

end MatedCRTHarmonic.GMSCM
