import QuantumZipper.Proofs.Zipper.XFlowRC3UC
import QuantumZipper.Proofs.Zipper.RegShiftUnifF2
import QuantumZipper.Proofs.Zipper.JointModDetCont
import QuantumZipper.Proofs.Zipper.D3PlusN2Cutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-FLOW-RC3, `Φ_j` continuity: pathwise ingredients

* `avgReg_unzX_eq`: at a time `t` where the `Γ⁰` field `y = 𝔥₀ + x` is regular after unzipping
  (witness `F`) and has `RegShift` along the unzipped dyadic circles, the dyadic averages of the
  unzipped `x`-field `x + α₀(−log|·|) = y − √κ log|·|` are
  `avgReg x_t k w = F(w, 2^{-k}) − √κ ∫ log|f_t⁻¹| dfc(w, 2^{-k})` for `w ∈ ℍ̄` (the computation of
  `RegUnif.logSing_reg_path`, at every centre instead of real centres);
* `continuousOn_integral_log_fwdMapInv_joint`: `(t, c, r) ↦ ∫ log|f_t⁻¹| dfc(c, r)` is jointly
  continuous on `[0,T] × ℂ × (0,∞)` (the first half of `RegUnif.detContStmt_holds`).

Own elementary bookkeeping (Sheffield arXiv:1012.4797 §5.1 rule (5.1); the estimates are those of
`JointModDetCont.lean`, `RegShiftUnifLog.lean`).
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace QuantumZipper
namespace F1

open RegCont TwoPoint UnzipInvariance RegUnif

/-- **Dyadic averages of the unzipped `x`-field** through the `Γ⁰` witness and the log part. -/
theorem avgReg_unzX_eq (κ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {x : FieldSample}
    (hR : ∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (ofFun (h0rev κ) + x)
      ((foldedCircle d (radius k)).map (fwdMapInv W t)))
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) t) F)
    (k : ℕ) {w : ℂ} (hw : w ∈ Hbar) :
    avgReg (F2.unzX κ x W t) k w = F (w, radius k) +
      -Real.sqrt κ * ∫ u, Real.log ‖fwdMapInv W t u‖ ∂foldedCircle w (radius k) := by
  set b := -Real.sqrt κ with hb
  set J : ℂ → ℝ := fun c => ∫ u, Real.log ‖fwdMapInv W t u‖ ∂foldedCircle c (radius k)
    with hJ
  have hJc : Continuous J := continuous_integral_log_fwdMapInv hW hW0 ht (radius_pos k)
  have key : ∀ n : ℕ, unzippedField (Real.sqrt κ) (x + F2.logSingField κ, W) t
      (foldedCircle (dyadicRoundC n w) (radius k)) =
      unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) t
        (foldedCircle (dyadicRoundC n w) (radius k)) +
        b * J (foldH (dyadicRoundC n w)) := by
    intro n
    rw [← CoordReg.foldedCircle_foldH (dyadicRoundC n w) (radius k)]
    have hd := foldH_dyadicRoundC_mem_Dy n w
    have hL := regShift_logF_fc_map hW hW0 ht b (foldH (dyadicRoundC n w)) (radius_pos k)
    have he := (regShift_add (hR k _ hd) hL.1).2
    have hg : evalReg (logF b) ((foldedCircle (foldH (dyadicRoundC n w)) (radius k)).map
        (fwdMapInv W t)) = b * J (foldH (dyadicRoundC n w)) := hL.2.limUnder_eq
    show evalReg (x + F2.logSingField κ) _ + _ = (evalReg (ofFun (h0rev κ) + x) _ + _) + _
    rw [logSing_eq, he, hg]
    ring
  have hJt : Tendsto (fun n => J (foldH (dyadicRoundC n w))) atTop (𝓝 (J w)) := by
    have := (hJc.tendsto _).comp ((CircleFubini.continuous_foldH'.tendsto _).comp
      (RegClosure.tendsto_dyadicRoundC w))
    rwa [Function.comp_def, Function.comp_def, D3Plus.foldH_of_mem_Hbar hw] at this
  exact ((hF.2.1 k w hw).add (hJt.const_mul b)).congr (fun n => (key n).symm) |>.limUnder_eq

/-- **Joint continuity of `(t, c, r) ↦ ∫ log|f_t⁻¹| dfc(c, r)`** on `[0,T] × ℂ × (0,∞)`. -/
theorem continuousOn_integral_log_fwdMapInv_joint {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun p : ℝ × (ℂ × ℝ) =>
      ∫ u, Real.log ‖fwdMapInv W p.1 u‖ ∂foldedCircle p.2.1 p.2.2)
      (Icc 0 T ×ˢ {p : ℂ × ℝ | 0 < p.2}) := by
  set G1 : ℝ → ℂ → ℝ := fun t u => Real.log ‖revMap (vRev W t) t u‖ with hG1
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  have hVM : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) t, |vRev W t s| ≤ 2 * M := by
    intro t ht s hs
    have h1 := hM (t - s) ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
    have h2 := hM t ht
    calc |W (t - s) - W t| ≤ |W (t - s)| + |W t| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hc1 : ContinuousOn (fun p : ℝ × (ℂ × ℝ) => ∫ u, G1 p.1 u ∂foldedCircle p.2.1 p.2.2)
      (Icc 0 T ×ˢ {p : ℂ × ℝ | 0 < p.2}) := by
    refine continuousOn_integral_foldedCircle_param hT (fun t ht =>
      Real.measurable_log.comp (measurable_revMap (continuous_vRev hW t) ht.1).norm) ?_ ?_
    · refine ((continuousOn_fwdMapInv_joint hW hW0 T).norm.log fun p hp => ?_).congr
        fun p hp => ?_
      · have h0 : 0 < (fwdMapInv W p.1 p.2).im :=
          (fwdMapInv_mem_H_bound hW hW0 hM hp.1.1 hp.1.2 hp.2 le_rfl).1
        exact norm_ne_zero_iff.2 fun h => by
          rw [h, Complex.zero_im] at h0; exact lt_irrefl _ h0
      · show Real.log ‖revMap (vRev W p.1) p.1 p.2‖ = Real.log ‖fwdMapInv W p.1 p.2‖
        rw [fwdMapInv_eq_revMap_timeRev W hW hW0 hp.1.1 hp.2]
    · intro R
      set B := max (revBound (2 * M) T R) 1
      refine ⟨|Real.log B|, abs_nonneg _, fun t ht u hu huR => ?_⟩
      have hV := continuous_vRev hW t
      have h0 : 0 < u.im := hu
      have h1 : u.im ≤ ‖revMap (vRev W t) t u‖ :=
        (im_le_im_revMap _ hV u hu ht.1).trans (Complex.im_le_norm _)
      have h2 : ‖revMap (vRev W t) t u‖ ≤ B :=
        ((norm_revMap_le_revBound hV ht.1 (hVM t ht) R huR).trans (revBound_mono ht.2)).trans
          (le_max_left _ _)
      have hB1 : 1 ≤ B := le_max_right _ _
      have a1 := Real.log_le_log h0 h1
      have a2 := Real.log_le_log (h0.trans_le h1) h2
      have a3 := Real.log_nonneg hB1
      show |Real.log ‖revMap (vRev W t) t u‖| ≤ _
      rw [abs_of_nonneg a3]
      rcases le_total 0 (Real.log ‖revMap (vRev W t) t u‖) with h | h
      · rw [abs_of_nonneg h]; linarith [abs_nonneg (Real.log u.im)]
      · rw [abs_of_nonpos h]; linarith [neg_abs_le (Real.log u.im)]
  refine hc1.congr fun p hp => ?_
  have hr : 0 < p.2.2 := hp.2
  refine integral_congr_ae ?_
  filter_upwards [foldedCircle_ae_mem_H p.2.1 hr] with u hu
  show Real.log ‖fwdMapInv W p.1 u‖ = Real.log ‖revMap (vRev W p.1) p.1 u‖
  rw [fwdMapInv_eq_revMap_timeRev W hW hW0 hp.1.1 hu]

end F1
end QuantumZipper
