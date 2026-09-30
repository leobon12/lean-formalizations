import QuantumZipper.Proofs.LQG.WedgeCanonical
import QuantumZipper.Proofs.GFF.CoordRegLog

/-!
# M4-A5-WEDGE (TASKS R23): the local density rule for the wedge field

TASKS R23 / AUDIT8 §3.1, route for (a): "the wedge field is `X` (regularized) plus `ofFun` of the
radial function `wedgeProfile x A Q`, so a local density rule `μ_{X + g} = e^{γ g} μ_X` on `ℍ`
holds (on a circle `|z| = a`, `e^{γ g}` is the constant `e^{γ g(a)}`)".

This file proves exactly that: `qAreaMeasure_wedgeField_eq`, for a *good* free-field sample `x`
(regular with a witness `F` that also gives the raw values at the dyadic circles, which holds a.s.
by `WedgeTK.IsRegVersion.raw`) and a continuous radial process `A`, the area measure of the wedge
field is the free-field measure weighted by `e^{γ · wedgeProfile x A Q}`.

Ingredients:
* `avgReg_wedgeField_eq`: the wedge field has the same dyadic averages as `x + ofFun (wedgeProfile
  x A Q)` — the two samples differ only through `evalReg x` vs `x` at the dyadic circles (equal by
  hypothesis `hraw`) and the split of the two integrals (needs integrability on that circle);
* `integrable_radAvgReg_foldedCircle`, `integrable_Alog_foldedCircle`: on a folded circle that
  misses `0`, the two pieces of the profile are bounded, hence integrable;
* `continuousOn_wedgeProfile_H`: the profile is continuous on `ℍ`;
* the transfer to measures (`areaApprox_congr_of_avgReg_ae`, `qAreaMeasure_congr_of_areaApprox`)
  uses that `‖z‖ = radius k` is Lebesgue-null (`MeasureTheory.Measure.addHaar_sphere`).

Source: Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), (5.1) (the local
rule `h ↦ h + g`); the small-`|z|`/large-`|z|` behaviour of the profile is the drift of the wedge
radial process (R23).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper

namespace WedgeCan

open LocalRule

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {Q γ : ℝ}

/-! ## 1. Integrability of the profile on folded circles avoiding `0` -/

/-- The modulus on a folded circle is bounded below by `|‖w‖ − r|`: a.e. point of the circle is
the fold of a point at distance `r` from `w`, and folding preserves the modulus. -/
theorem ae_fc_abs_le_norm {w : ℂ} {r : ℝ} (hr : 0 < r) :
    ∀ᵐ u ∂foldedCircle w r, |‖w‖ - r| ≤ ‖u‖ := by
  unfold foldedCircle
  refine (ae_map_iff measurable_foldH.aemeasurable
    (measurableSet_le measurable_const measurable_norm)).2 ?_
  filter_upwards [KernelId.ae_norm_sub_center w hr] with u hu
  rw [SmoothConv.norm_foldH_sc]
  have hle : |‖u‖ - ‖w‖| ≤ r := by
    rw [← hu]
    exact abs_norm_sub_norm_le u w
  have hle' := abs_le.1 hle
  have htri : (r : ℝ) ≤ ‖u‖ + ‖w‖ := by
    have := norm_sub_le u w
    rwa [hu] at this
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- On a folded circle through `w ∈ Hbar` of radius `r` with `‖w‖ ≠ r` (so the circle misses
`0`), the regularized radial average is bounded, hence integrable. -/
theorem integrable_radAvgReg_foldedCircle (hG : WedgeTK.GoodRad x F) {w : ℂ} (hw : w ∈ Hbar)
    {r : ℝ} (hr : 0 < r) (hne : ‖w‖ ≠ r) :
    Integrable (fun u : ℂ => radAvgReg x ‖u‖) (foldedCircle w r) := by
  set m : ℝ := |‖w‖ - r| with hm
  have hm0 : 0 < m := abs_pos.2 (sub_ne_zero.2 hne)
  have hcont : ContinuousOn (fun t : ℝ => F (0, t)) (Set.Icc m (‖w‖ + r)) :=
    ContinuousOn.comp hG.1.1 (continuousOn_const.prodMk continuousOn_id) fun t ht =>
      ⟨GaussTK.zero_mem_Hbar, lt_of_lt_of_le hm0 ht.1⟩
  have hbdd : BddAbove ((fun t : ℝ => |F (0, t)|) '' Set.Icc m (‖w‖ + r)) :=
    isCompact_Icc.bddAbove_image hcont.abs
  refine Integrable.of_bound (measurable_radAvgReg_norm x).aestronglyMeasurable
    (sSup ((fun t : ℝ => |F (0, t)|) '' Set.Icc m (‖w‖ + r))) ?_
  filter_upwards [LocalRule.ae_fc_mem_closedBall hw hr, ae_fc_abs_le_norm hr] with u hu hlo
  have h1 : |‖u‖ - ‖w‖| ≤ r := by
    have h2 := Metric.mem_closedBall.1 hu
    rw [dist_eq_norm] at h2
    exact (abs_norm_sub_norm_le u w).trans h2
  have hu_hi : ‖u‖ ≤ ‖w‖ + r := by linarith [abs_le.1 h1]
  have hmu : m ≤ ‖u‖ := by rw [hm]; exact hlo
  have hpos : 0 < ‖u‖ := lt_of_lt_of_le hm0 hmu
  rw [Real.norm_eq_abs, hG.radAvgReg_eq hpos]
  exact le_csSup hbdd ⟨‖u‖, ⟨hmu, hu_hi⟩, rfl⟩

/-- On a folded circle through `w ∈ Hbar` of radius `r` with `‖w‖ ≠ r`, the continuous radial
process read at `−log‖·‖` is bounded, hence integrable. -/
theorem integrable_Alog_foldedCircle (hA : Continuous A) {w : ℂ} (hw : w ∈ Hbar) {r : ℝ}
    (hr : 0 < r) (hne : ‖w‖ ≠ r) :
    Integrable (fun u : ℂ => A (-Real.log ‖u‖)) (foldedCircle w r) := by
  set m : ℝ := |‖w‖ - r| with hm
  have hm0 : 0 < m := abs_pos.2 (sub_ne_zero.2 hne)
  have hbdd : BddAbove ((fun t : ℝ => |A t|) ''
      Set.Icc (-Real.log (‖w‖ + r)) (-Real.log m)) :=
    isCompact_Icc.bddAbove_image (hA.continuousOn.abs)
  refine Integrable.of_bound ?_
    (sSup ((fun t : ℝ => |A t|) '' Set.Icc (-Real.log (‖w‖ + r)) (-Real.log m))) ?_
  · exact (hA.measurable.comp ((Real.measurable_log.comp measurable_norm).neg)).aestronglyMeasurable
  · filter_upwards [LocalRule.ae_fc_mem_closedBall hw hr, ae_fc_abs_le_norm hr] with u hu hlo
    have h1 : |‖u‖ - ‖w‖| ≤ r := by
      have h2 := Metric.mem_closedBall.1 hu
      rw [dist_eq_norm] at h2
      exact (abs_norm_sub_norm_le u w).trans h2
    have hu_hi : ‖u‖ ≤ ‖w‖ + r := by linarith [abs_le.1 h1]
    have hmu : m ≤ ‖u‖ := by rw [hm]; exact hlo
    have hpos : 0 < ‖u‖ := lt_of_lt_of_le hm0 hmu
    have hlog_lo : -Real.log (‖w‖ + r) ≤ -Real.log ‖u‖ := by
      have := Real.log_le_log hpos hu_hi
      linarith
    have hlog_hi : -Real.log ‖u‖ ≤ -Real.log m := by
      have := Real.log_le_log hm0 hmu
      linarith
    rw [Real.norm_eq_abs]
    exact le_csSup hbdd ⟨-Real.log ‖u‖, ⟨hlog_lo, hlog_hi⟩, rfl⟩

/-- The integrand `Q * −log‖·‖` is integrable on every folded circle. -/
theorem integrable_logProfile_foldedCircle (Q : ℝ) (w : ℂ) (r : ℝ) :
    Integrable (fun u : ℂ => Q * -Real.log ‖u‖) (foldedCircle w r) :=
  (CoordReg.integrable_log_norm_foldedCircle w r).neg.const_mul Q

/-! ## 2. Continuity of the profile on `ℍ` -/

theorem notMem_H_zero : (0 : ℂ) ∉ H := by simp [H]

/-- The wedge profile is continuous on `ℍ` for a good radial sample and a continuous `A`. -/
theorem continuousOn_wedgeProfile_H (hG : WedgeTK.GoodRad x F) (hA : Continuous A) (Q : ℝ) :
    ContinuousOn (wedgeProfile x A Q) H := by
  have hne : ∀ z ∈ H, z ≠ 0 := fun z hz h0 => notMem_H_zero (h0 ▸ hz)
  have hrad : ContinuousOn (fun z : ℂ => radAvgReg x ‖z‖) H :=
    ContinuousOn.congr (ContinuousOn.comp hG.1.1 (continuousOn_const.prodMk continuous_norm.continuousOn)
        fun z hz => ⟨GaussTK.zero_mem_Hbar, norm_pos_iff.2 (hne z hz)⟩)
      fun z hz => hG.radAvgReg_eq (norm_pos_iff.2 (hne z hz))
  have hlogc : ContinuousOn (fun z : ℂ => -Real.log ‖z‖) H := fun z hz =>
    ((Real.continuousAt_log (norm_ne_zero_iff.2 (hne z hz))).comp
      continuous_norm.continuousAt).neg.continuousWithinAt
  have hAc : ContinuousOn (fun z : ℂ => A (-Real.log ‖z‖)) H := hA.comp_continuousOn hlogc
  unfold wedgeProfile
  exact (hrad.neg.add (continuousOn_const.mul hlogc)).add hAc

/-! ## 3. The dyadic averages of the wedge field -/

/-- **The wedge field has the same dyadic averages as `x + ofFun (wedgeProfile x A Q)`.** The two
samples differ only in `evalReg x` vs `x` at the dyadic circles (equal by `hraw`) and in the split
of the two integrals, which needs integrability on that circle; the circle through `0` is
excluded. -/
theorem avgReg_wedgeField_eq (hG : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (Q : ℝ) {k : ℕ} {z : ℂ} (hz : z ∈ Hbar) (hne : ‖z‖ ≠ radius k) :
    avgReg (wedgeField (lateralPart x) A Q) k z =
      avgReg (x + ofFun (wedgeProfile x A Q)) k z := by
  have hF := hG.1
  have hev : ∀ᶠ n : ℕ in atTop, ‖dyadicRoundC n z‖ ≠ radius k := by
    have hδ0 : 0 < |‖z‖ - radius k| := abs_pos.2 (sub_ne_zero.2 hne)
    have hb : ∀ᶠ n : ℕ in atTop,
        |‖dyadicRoundC n z‖ - ‖z‖| < |‖z‖ - radius k| :=
      ((RegClosure.tendsto_dyadicRoundC z).norm.eventually
        (Metric.ball_mem_nhds _ hδ0)).mono fun n hn => by
        simpa [Metric.mem_ball, Real.dist_eq] using hn
    filter_upwards [hb] with n hn
    exact fun hcon => absurd (by rw [hcon, abs_sub_comm] at hn; exact hn) (lt_irrefl _)
  have heq : (fun n : ℕ => wedgeField (lateralPart x) A Q
        (foldedCircle (dyadicRoundC n z) (radius k))) =ᶠ[atTop]
      fun n => (x + ofFun (wedgeProfile x A Q))
        (foldedCircle (dyadicRoundC n z) (radius k)) := by
    filter_upwards [hev] with n hn
    have hdn : dyadicRoundC n z ∈ Hbar := CircleCont.dyadicRoundC_mem_Hbar hz n
    have h0 := integrable_radAvgReg_foldedCircle hG hdn (radius_pos k) hn
    have hAint := integrable_Alog_foldedCircle hA hdn (radius_pos k) hn
    have hL := integrable_logProfile_foldedCircle Q (dyadicRoundC n z) (radius k)
    have hsplit1 : ∫ u, (-radAvgReg x ‖u‖ + Q * -Real.log ‖u‖)
        ∂foldedCircle (dyadicRoundC n z) (radius k) =
        ∫ u, -radAvgReg x ‖u‖ ∂foldedCircle (dyadicRoundC n z) (radius k) +
          ∫ u, Q * -Real.log ‖u‖ ∂foldedCircle (dyadicRoundC n z) (radius k) :=
      integral_add h0.neg hL
    have hsplit2 : ∫ u, (-radAvgReg x ‖u‖ + Q * -Real.log ‖u‖ + A (-Real.log ‖u‖))
        ∂foldedCircle (dyadicRoundC n z) (radius k) =
        ∫ u, (-radAvgReg x ‖u‖ + Q * -Real.log ‖u‖)
          ∂foldedCircle (dyadicRoundC n z) (radius k) +
          ∫ u, A (-Real.log ‖u‖) ∂foldedCircle (dyadicRoundC n z) (radius k) :=
      integral_add (h0.neg.add hL) hAint
    have hneg : ∫ u, -radAvgReg x ‖u‖ ∂foldedCircle (dyadicRoundC n z) (radius k) =
        -∫ u, radAvgReg x ‖u‖ ∂foldedCircle (dyadicRoundC n z) (radius k) := integral_neg _
    have hp : ∫ u, wedgeProfile x A Q u ∂foldedCircle (dyadicRoundC n z) (radius k) =
        -∫ u, radAvgReg x ‖u‖ ∂foldedCircle (dyadicRoundC n z) (radius k) +
          (∫ u, Q * -Real.log ‖u‖ ∂foldedCircle (dyadicRoundC n z) (radius k) +
            ∫ u, A (-Real.log ‖u‖) ∂foldedCircle (dyadicRoundC n z) (radius k)) := by
      rw [show ∫ u, wedgeProfile x A Q u ∂foldedCircle (dyadicRoundC n z) (radius k) =
          ∫ u, (-radAvgReg x ‖u‖ + Q * -Real.log ‖u‖ + A (-Real.log ‖u‖))
            ∂foldedCircle (dyadicRoundC n z) (radius k) from rfl, hsplit2, hsplit1, hneg]
      ring
    have hR : (x + ofFun (wedgeProfile x A Q)) (foldedCircle (dyadicRoundC n z) (radius k)) =
        x (foldedCircle (dyadicRoundC n z) (radius k)) +
          ∫ u, wedgeProfile x A Q u ∂foldedCircle (dyadicRoundC n z) (radius k) := rfl
    rw [wedgeField_eq_evalReg_add_ofFun h0 hL hAint, hR, hraw n z hz k,
      hF.evalReg_fc_of_mem hdn (radius_pos k), hp]
  unfold avgReg limUnder
  rw [Filter.map_congr heq]

/-! ## 4. The density rule -/

/-- Area approximations only read the dyadic averages a.e. on `ℍ`. -/
theorem areaApprox_congr_of_avgReg_ae {y y' : FieldSample} (γ : ℝ)
    (h : ∀ᵐ z ∂(volume.restrict H), ∀ k : ℕ, avgReg y k z = avgReg y' k z) :
    areaApprox γ y = areaApprox γ y' := by
  funext k
  unfold areaApprox
  refine withDensity_congr_ae ?_
  filter_upwards [h] with z hz
  simp only [hz k]

/-- **The local density rule for the wedge field** (route of TASKS R23 for (a)), for a good free
sample `x` and a continuous radial process `A`. -/
theorem qAreaMeasure_wedgeField_eq (hG : WedgeTK.GoodRad x F) (hA : Continuous A) {Q γ : ℝ}
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hex : ∃ μ, IsVagueLimitOn H (areaApprox γ x) μ) :
    qAreaMeasure γ (wedgeField (lateralPart x) A Q) =
      (qAreaMeasure γ x).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * wedgeProfile x A Q z))) := by
  have hae : ∀ᵐ z ∂(volume.restrict H), ∀ k : ℕ,
      avgReg (wedgeField (lateralPart x) A Q) k z =
        avgReg (x + ofFun (wedgeProfile x A Q)) k z := by
    rw [ae_all_iff]
    intro k
    rw [ae_restrict_iff' isOpen_H.measurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (MeasureTheory.Measure.addHaar_sphere (volume : Measure ℂ) 0 (radius k))] with z hz hzH
    have hz' : ‖z‖ ≠ radius k := fun hcon =>
      hz (by simpa [Metric.mem_sphere, dist_zero_right] using hcon)
    exact avgReg_wedgeField_eq hG hraw hA Q (H_subset_Hbar hzH) hz'
  rw [qAreaMeasure_congr_of_areaApprox (areaApprox_congr_of_avgReg_ae γ hae),
    LocalRule.qAreaMeasure_add_ofFun' ⟨F, hG.1⟩ hex isOpen_H subset_rfl
      ((continuousOn_wedgeProfile_H hG hA Q).mono Set.inter_subset_left)]

end WedgeCan

end QuantumZipper
