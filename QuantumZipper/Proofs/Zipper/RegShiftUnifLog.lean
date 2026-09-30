import QuantumZipper.Proofs.Zipper.RegShiftUnifBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# REGSHIFT-UNIF, deterministic log part: `RegShift` of `b·log|·|` along unzipped circles

The log singularity `b·log|·|` (as the field sample `logF b = ofFun (b·log‖·‖)`) along a pushed
folded circle `(f_t)_* fc(c, r)`, `f_t = fwdMapInv W t`, for every continuous driver `W` with
`W 0 = 0` and every `t ≥ 0`:

* `avgReg_logF`: `avgReg (logF b) k w = b·log max(2^{-k}, |w|)` at every `w` (Jensen's formula for
  folded circles, `CoordReg.integral_log_norm_foldedCircle`);
* `regShift_logF_fc_map`: `E1.RegShift (logF b) ((f_t)_* fc(c, r))`, with the limit
  `b ∫ log|f_t| dfc(c, r)` (dominated convergence: on `ℍ`, `Im u ≤ |f_t(u)| ≤ C`, and
  `log Im u` is integrable over folded circles);
* `continuous_integral_log_fwdMapInv`: `c ↦ ∫ log|f_t| dfc(c, r)` is continuous (the first half
  of the proof of `RegUnif.detContStmt_holds`, at a fixed time).

Own elementary arguments (bounded/dominated convergence), following the estimates of
`JointModDetCont.lean`.
-/

noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology Real

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint UnzipInvariance CircleFubini

variable {W : ℝ → ℝ}

/-- The deterministic field `b·log|·|`. -/
def logF (b : ℝ) : FieldSample := ofFun fun z => b * Real.log ‖z‖

theorem logF_fc (b : ℝ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    logF b (foldedCircle c r) = b * Real.log (max r ‖c‖) := by
  show ∫ z, b * Real.log ‖z‖ ∂foldedCircle c r = _
  rw [integral_const_mul, CoordReg.integral_log_norm_foldedCircle c hr]

theorem tendsto_raw_logF (b : ℝ) (k : ℕ) (z : ℂ) :
    Tendsto (fun n => logF b (foldedCircle (dyadicRoundC n z) (radius k))) atTop
      (𝓝 (b * Real.log (max (radius k) ‖z‖))) := by
  have h := (((CoordReg.continuous_log_max_norm (radius_pos k)).tendsto z).comp
    (RegClosure.tendsto_dyadicRoundC z)).const_mul b
  refine h.congr fun n => ?_
  rw [logF_fc b _ (radius_pos k)]
  rfl

theorem avgReg_logF (b : ℝ) (k : ℕ) (z : ℂ) :
    avgReg (logF b) k z = b * Real.log (max (radius k) ‖z‖) :=
  (tendsto_raw_logF b k z).limUnder_eq

theorem abs_log_le_of_bounds {a x B : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxB : x ≤ B)
    (hB : 1 ≤ B) : |Real.log x| ≤ Real.log B + |Real.log a| := by
  have a1 := Real.log_le_log ha hax
  have a2 := Real.log_le_log (ha.trans_le hax) hxB
  have a3 := Real.log_nonneg hB
  rcases le_total 0 (Real.log x) with h | h
  · rw [abs_of_nonneg h]; linarith [abs_nonneg (Real.log a)]
  · rw [abs_of_nonpos h]; linarith [neg_abs_le (Real.log a)]

theorem im_le_norm_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {u : ℂ}
    (hu : u ∈ H) : u.im ≤ ‖fwdMapInv W t u‖ := by
  rw [fwdMapInv_eq_revMap_timeRev W hW hW0 ht hu]
  exact (im_le_im_revMap _ (continuous_vRev hW t) u hu ht).trans (Complex.im_le_norm _)

theorem radius_le_one (k : ℕ) : radius k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

/-- **`RegShift` of the log field along an unzipped circle**, with its limit. -/
theorem regShift_logF_fc_map (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (b : ℝ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    E1.RegShift (logF b) ((foldedCircle c r).map (fwdMapInv W t)) ∧
      Tendsto (fun k => ∫ w, avgReg (logF b) k w ∂(foldedCircle c r).map (fwdMapInv W t))
        atTop (𝓝 (b * ∫ u, Real.log ‖fwdMapInv W t u‖ ∂foldedCircle c r)) := by
  set φ := fwdMapInv W t with hφdef
  have hφ : AEMeasurable φ (foldedCircle c r) := aemeasurable_fwdMapInv hW hW0 ht c hr
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW t
  set Bd := max (revBound (2 * M) t (‖c‖ + r)) 1 with hBd
  have hB1 : 1 ≤ Bd := le_max_right _ _
  have hpt : ∀ᵐ u ∂foldedCircle c r, 0 < u.im ∧ u.im ≤ ‖φ u‖ ∧ ‖φ u‖ ≤ Bd := by
    filter_upwards [foldedCircle_ae_mem_H c hr, foldedCircle_ae_norm_le c hr.le] with u hu hun
    exact ⟨hu, im_le_norm_fwdMapInv hW hW0 ht hu,
      ((fwdMapInv_mem_H_bound hW hW0 hM ht le_rfl hu hun).2).trans (le_max_left _ _)⟩
  have hav : ∀ k, (fun w => avgReg (logF b) k w) =
      fun w => b * Real.log (max (radius k) ‖w‖) := fun k => funext fun w => avgReg_logF b k w
  have hmk : ∀ k, Measurable fun w : ℂ => b * Real.log (max (radius k) ‖w‖) := fun k =>
    measurable_const.mul (Real.measurable_log.comp (measurable_const.max measurable_norm))
  set D : ℂ → ℝ := fun u => |b| * (Real.log Bd + |Real.log u.im|) with hDdef
  have hD : Integrable D (foldedCircle c r) :=
    ((integrable_const _).add (integrable_log_im_foldedCircle c hr).abs).const_mul _
  have hbd : ∀ k, ∀ᵐ u ∂foldedCircle c r,
      ‖b * Real.log (max (radius k) ‖φ u‖)‖ ≤ D u := by
    intro k
    filter_upwards [hpt] with u hu
    obtain ⟨h0, h1, h2⟩ := hu
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_log_le_of_bounds h0 (h1.trans (le_max_right _ _))
      (max_le ((radius_le_one k).trans hB1) h2) hB1) (abs_nonneg b)
  have hmeas : ∀ k, AEStronglyMeasurable (fun u => b * Real.log (max (radius k) ‖φ u‖))
      (foldedCircle c r) := fun k => ((hmk k).comp_aemeasurable hφ).aestronglyMeasurable
  have hint : ∀ k, Integrable (fun u => b * Real.log (max (radius k) ‖φ u‖))
      (foldedCircle c r) := fun k => Integrable.mono' hD (hmeas k) (hbd k)
  have hlim : ∀ᵐ u ∂foldedCircle c r, Tendsto (fun k => b * Real.log (max (radius k) ‖φ u‖))
      atTop (𝓝 (b * Real.log ‖φ u‖)) := by
    filter_upwards [hpt] with u hu
    obtain ⟨h0, h1, -⟩ := hu
    have hpos : 0 < ‖φ u‖ := h0.trans_le h1
    have h := (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).max
      (tendsto_const_nhds (x := ‖φ u‖))
    rw [max_eq_right (norm_nonneg _)] at h
    exact ((Real.continuousAt_log hpos.ne').tendsto.comp h).const_mul b
  have hT := tendsto_integral_of_dominated_convergence D hmeas hD hbd hlim
  have heq : ∀ k, ∫ w, avgReg (logF b) k w ∂(foldedCircle c r).map φ =
      ∫ u, b * Real.log (max (radius k) ‖φ u‖) ∂foldedCircle c r := fun k => by
    rw [hav k, integral_map hφ (hmk k).aestronglyMeasurable]
  have hT' : Tendsto (fun k => ∫ w, avgReg (logF b) k w ∂(foldedCircle c r).map φ) atTop
      (𝓝 (b * ∫ u, Real.log ‖φ u‖ ∂foldedCircle c r)) := by
    rw [← integral_const_mul]
    exact hT.congr fun k => (heq k).symm
  refine ⟨⟨Eventually.of_forall fun z k => ⟨_, tendsto_raw_logF b k z⟩, fun k => ?_,
    _, hT'⟩, hT'⟩
  rw [hav k, integrable_map_measure (hmk k).aestronglyMeasurable hφ]
  exact hint k

/-- **Continuity in the centre of `∫ log|f_t| dfc(c, r)`** (from the proof of
`detContStmt_holds`). -/
theorem continuous_integral_log_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {r : ℝ} (hr : 0 < r) :
    Continuous fun c : ℂ => ∫ u, Real.log ‖fwdMapInv W t u‖ ∂foldedCircle c r := by
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW t
  have hVM : ∀ s ∈ Icc (0 : ℝ) t, ∀ q ∈ Icc (0 : ℝ) s, |vRev W s q| ≤ 2 * M := by
    intro s hs q hq
    have h1 := hM (s - q) ⟨by linarith [hq.2], by linarith [hq.1, hs.2]⟩
    have h2 := hM s hs
    calc |W (s - q) - W s| ≤ |W (s - q)| + |W s| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hc1 : ContinuousOn (fun p : ℝ × (ℂ × ℝ) =>
      ∫ u, Real.log ‖revMap (vRev W p.1) p.1 u‖ ∂foldedCircle p.2.1 p.2.2)
      (Icc 0 t ×ˢ {p : ℂ × ℝ | 0 < p.2}) := by
    refine continuousOn_integral_foldedCircle_param ht (fun s hs =>
      Real.measurable_log.comp (measurable_revMap (continuous_vRev hW s) hs.1).norm) ?_ ?_
    · refine ((continuousOn_fwdMapInv_joint hW hW0 t).norm.log fun p hp => ?_).congr
        fun p hp => ?_
      · have h0 : 0 < (fwdMapInv W p.1 p.2).im :=
          (fwdMapInv_mem_H_bound hW hW0 hM hp.1.1 hp.1.2 hp.2 le_rfl).1
        exact norm_ne_zero_iff.2 fun h => by
          rw [h, Complex.zero_im] at h0; exact lt_irrefl _ h0
      · show Real.log ‖revMap (vRev W p.1) p.1 p.2‖ = Real.log ‖fwdMapInv W p.1 p.2‖
        rw [fwdMapInv_eq_revMap_timeRev W hW hW0 hp.1.1 hp.2]
    · intro R
      set B := max (revBound (2 * M) t R) 1
      refine ⟨|Real.log B|, abs_nonneg _, fun s hs u hu huR => ?_⟩
      have hV := continuous_vRev hW s
      have h0 : 0 < u.im := hu
      have h1 : u.im ≤ ‖revMap (vRev W s) s u‖ :=
        (im_le_im_revMap _ hV u hu hs.1).trans (Complex.im_le_norm _)
      have h2 : ‖revMap (vRev W s) s u‖ ≤ B :=
        ((norm_revMap_le_revBound hV hs.1 (hVM s hs) R huR).trans (revBound_mono hs.2)).trans
          (le_max_left _ _)
      have hB1 : 1 ≤ B := le_max_right _ _
      rw [abs_of_nonneg (Real.log_nonneg hB1)]
      exact abs_log_le_of_bounds h0 h1 h2 hB1
  have hcc : Continuous fun c : ℂ =>
      ∫ u, Real.log ‖revMap (vRev W t) t u‖ ∂foldedCircle c r := by
    refine continuousOn_univ.1 (hc1.comp (f := fun c : ℂ => (t, (c, r)))
      (by fun_prop : Continuous fun c : ℂ => (t, (c, r))).continuousOn fun c _ => ?_)
    exact ⟨⟨ht, le_rfl⟩, hr⟩
  refine hcc.congr fun c => integral_congr_ae ?_
  filter_upwards [foldedCircle_ae_mem_H c hr] with u hu
  show Real.log ‖revMap (vRev W t) t u‖ = Real.log ‖fwdMapInv W t u‖
  rw [fwdMapInv_eq_revMap_timeRev W hW hW0 ht hu]

end RegUnif
end QuantumZipper
