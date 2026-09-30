import QuantumZipper.Proofs.Thm18.G3Cv2Setup
import QuantumZipper.Proofs.Zipper.D3PlusN2H3WinPsi
import QuantumZipper.Proofs.Zipper.RegContDet
import QuantumZipper.Proofs.Zipper.WedgeUnzipAddFun
import QuantumZipper.Proofs.GFF.FrostmanReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-A, item (a), layer 1: regularized evaluation of `ofFun f + x` for a log-singular profile

For a profile `f` equal to `a (−log ‖· − p‖) + h` near a real point `p` (`h` continuous) and a
field sample `x` whose dyadic circle averages converge (`RegCont.RegAvgGood`), the regularized
evaluation at a probability measure `ν` carried by a small half-disc around `p`, not charging
`p`, and integrating `log ‖· − p‖`, is additive:

  `evalReg (ofFun f + x) ν = ∫ f dν + lim_k ∫ avgReg x k dν`   (`evalReg_ofFun_add_logSing`).

This covers measures through the singularity (e.g. circles through `p`), which
`FrostmanReg.ae_evalReg_ofFun_add_eq_frostman` and `ASep.evalReg_ofFun_add_of_tendsto` do not.
Proof: the circle average of `−log ‖· − p‖` over `fc(c, s)` is `−log max(s, ‖c − p‖)` (Jensen's
formula, `D3Plus.integral_log_norm_fc`), continuous in the centre, so
`avgReg (ofFun f + x) k = −a log max(2^{-k}, ‖· − p‖) + (h)_{2^{-k}} + avgReg x k` near `p`;
dominated convergence (bound `|log ‖· − p‖| + const`, integrable by hypothesis) in `k`.
Own elementary argument (the paper treats `h + φ` for such explicit `φ` without comment,
Sheffield arXiv:1012.4797 §1.6 and p. 70).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace G3Za

theorem measurable_log_norm_sub (p : ℝ) : Measurable fun u : ℂ => Real.log ‖u - p‖ :=
  Real.measurable_log.comp (measurable_norm.comp (measurable_id.sub measurable_const))

/-- Circle average of `log ‖· − p‖` for a real point `p` (Jensen). -/
theorem integral_log_norm_sub_fc (c : ℂ) {s : ℝ} (hs : 0 < s) (p : ℝ) :
    ∫ u : ℂ, Real.log ‖u - (p : ℂ)‖ ∂foldedCircle c s = Real.log (max s ‖c - p‖) := by
  have h := IndepParams.fc_map_add_real c s (-p)
  have e : ∫ u, Real.log ‖u - p‖ ∂foldedCircle c s =
      ∫ v, Real.log ‖v‖ ∂(foldedCircle c s).map (fun u => u + ((-p : ℝ) : ℂ)) := by
    have hm : Measurable fun v : ℂ => Real.log ‖v‖ := Real.measurable_log.comp measurable_norm
    rw [integral_map (by fun_prop) hm.aestronglyMeasurable]
    congr 1; funext u; congr 2; push_cast; ring
  rw [e, h, D3Plus.integral_log_norm_fc _ hs]
  congr 3; push_cast; ring

theorem integrable_log_norm_sub_fc (c : ℂ) (s p : ℝ) :
    Integrable (fun u : ℂ => Real.log ‖u - (p : ℂ)‖) (foldedCircle c s) := by
  have h := CoordReg.integrable_log_norm_foldedCircle (c + ((-p : ℝ) : ℂ)) s
  have hm : Measurable fun v : ℂ => Real.log ‖v‖ := Real.measurable_log.comp measurable_norm
  rw [← IndepParams.fc_map_add_real c s (-p), integrable_map_measure
    hm.aestronglyMeasurable (by fun_prop)] at h
  refine h.congr (ae_of_all _ fun u => ?_)
  simp only [Function.comp, Complex.ofReal_neg, ← sub_eq_add_neg]

/-- Circle average of a log-singular profile, for circles inside the half-disc around `p`. -/
theorem integral_fc_logSing {a p ρ : ℝ} {f h : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (p : ℂ) ρ ∩ Hbar, f u = a * -Real.log ‖u - p‖ + h u)
    (hh : Continuous h) {c : ℂ} {s : ℝ} (hs : 0 < s) (hcs : ‖c - p‖ + s ≤ ρ) :
    ∫ u, f u ∂foldedCircle c s = a * -Real.log (max s ‖c - p‖) + ∫ u, h u ∂foldedCircle c s := by
  have hnull := G3Cv.foldedCircle_compl_null (b := p) hs hcs
  have hae := G3Cv.ae_mem_of_compl_null_g3cv hnull
  have hhi : Integrable h (foldedCircle c s) :=
    K3.integrable_of_continuousOn_closedBall_Hbar hh.continuousOn hnull
  have hli : Integrable (fun u : ℂ => a * -Real.log ‖u - (p : ℂ)‖) (foldedCircle c s) :=
    (integrable_log_norm_sub_fc c s p).neg.const_mul a
  rw [integral_congr_ae (hae.mono fun u hu => hf u hu), integral_add hli hhi, integral_const_mul,
    integral_neg, integral_log_norm_sub_fc c hs p]

theorem continuous_logMax (a p r : ℝ) (hr : 0 < r) :
    Continuous fun c : ℂ => a * -Real.log (max r ‖c - p‖) :=
  continuous_const.mul ((continuous_const.max
    (continuous_norm.comp (continuous_id.sub continuous_const))).log
      fun c => (lt_max_of_lt_left hr).ne').neg

/-- The dyadic circle average of `ofFun f + x` near the singularity. -/
theorem avgReg_ofFun_add_logSing {x : FieldSample} {a p ρ : ℝ} {f h : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (p : ℂ) ρ ∩ Hbar, f u = a * -Real.log ‖u - p‖ + h u)
    (hh : Continuous h) {k : ℕ} {w : ℂ} (hw : ‖w - p‖ + radius k < ρ) {L : ℝ}
    (hx : Tendsto (fun n => x (foldedCircle (dyadicRoundC n w) (radius k))) atTop (𝓝 L)) :
    avgReg (ofFun f + x) k w =
      a * -Real.log (max (radius k) ‖w - p‖) + GoodSample.smoothFun h w (radius k) + L := by
  unfold avgReg
  apply Tendsto.limUnder_eq
  have hd := RegClosure.tendsto_dyadicRoundC w
  have hev : ∀ᶠ n in atTop, ‖dyadicRoundC n w - p‖ + radius k ≤ ρ := by
    have : Tendsto (fun n => ‖dyadicRoundC n w - p‖ + radius k) atTop
        (𝓝 (‖w - p‖ + radius k)) := ((hd.sub_const _).norm).add_const _
    exact (this.eventually (gt_mem_nhds hw)).mono fun n hn => hn.le
  have hcont : Continuous fun c : ℂ =>
      a * -Real.log (max (radius k) ‖c - p‖) + GoodSample.smoothFun h c (radius k) :=
    (continuous_logMax a p _ (radius_pos k)).add
      (GoodSample.continuous_smoothFun hh.continuousOn _)
  refine (((hcont.tendsto w).comp hd).add hx).congr' ?_
  filter_upwards [hev] with n hn
  simp only [Function.comp, Pi.add_apply, ofFun]
  rw [integral_fc_logSing hf hh (radius_pos k) hn]
  rfl

theorem abs_log_max_le {r t B : ℝ} (hr : r ≤ 1) (ht : 0 < t) (htB : t ≤ B) :
    |Real.log (max r t)| ≤ |Real.log t| + |Real.log (max 1 B)| := by
  have h1 : Real.log t ≤ Real.log (max r t) := Real.log_le_log ht (le_max_right _ _)
  have h2 : Real.log (max r t) ≤ Real.log (max 1 B) :=
    Real.log_le_log (lt_max_of_lt_right ht) (max_le_max hr htB)
  have h3 : 0 ≤ Real.log (max 1 B) := Real.log_nonneg (le_max_left _ _)
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log t); linarith [abs_nonneg (Real.log (max 1 B))]
  · have := le_abs_self (Real.log (max 1 B)); linarith [abs_nonneg (Real.log t)]

/-- **Additivity of the regularized evaluation for a log-singular profile.** -/
theorem evalReg_ofFun_add_logSing {x : FieldSample} (hx : RegCont.RegAvgGood x)
    {a p ρ ρ₁ : ℝ} {f h : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (p : ℂ) ρ ∩ Hbar, f u = a * -Real.log ‖u - p‖ + h u)
    (hh : Continuous h) (hρ₁ : ρ₁ < ρ) {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ w ∂ν, w ∈ closedBall (p : ℂ) ρ₁ ∩ Hbar) (hνp : ∀ᵐ w ∂ν, w ≠ (p : ℂ))
    (hlog : Integrable (fun w : ℂ => Real.log ‖w - (p : ℂ)‖) ν) {A : ℝ}
    (hA : Tendsto (fun k => ∫ w, avgReg x k w ∂ν) atTop (𝓝 A)) :
    evalReg (ofFun f + x) ν = ∫ w, f w ∂ν + A := by
  unfold evalReg
  apply Tendsto.limUnder_eq
  have hnull : ν (closedBall (p : ℂ) ρ₁ ∩ Hbar)ᶜ = 0 := ae_iff.1 hν
  have hk : ∀ᶠ k in atTop, radius k < ρ - ρ₁ :=
    (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (by linarith))
  set T1 : ℕ → ℂ → ℝ := fun k w => a * -Real.log (max (radius k) ‖w - p‖) with hT1
  set T2 : ℕ → ℂ → ℝ := fun k w => GoodSample.smoothFun h w (radius k) with hT2
  have hT1c : ∀ k, Continuous (T1 k) := fun k => continuous_logMax a p _ (radius_pos k)
  have hT2c : ∀ k, Continuous (T2 k) := fun k =>
    GoodSample.continuous_smoothFun hh.continuousOn _
  have hT1i : ∀ k, Integrable (T1 k) ν := fun k =>
    K3.integrable_of_continuousOn_closedBall_Hbar (hT1c k).continuousOn hnull
  have hT2i : ∀ k, Integrable (T2 k) ν := fun k =>
    K3.integrable_of_continuousOn_closedBall_Hbar (hT2c k).continuousOn hnull
  have hXi : ∀ k, Integrable (avgReg x k) ν := fun k =>
    K3.integrable_of_continuousOn_closedBall_Hbar ((hx k).1.mono inter_subset_right) hnull
  -- the log part: dominated convergence
  have hlim1 : Tendsto (fun k => ∫ w, T1 k w ∂ν) atTop
      (𝓝 (∫ w, a * -Real.log ‖w - p‖ ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun w => |a| * (|Real.log ‖w - p‖| + |Real.log (max 1 ρ₁)|))
      (fun k => (hT1c k).aestronglyMeasurable)
      ((hlog.abs.add (integrable_const _)).const_mul _) (fun k => ?_) ?_
    · filter_upwards [hν, hνp] with w hw hwp
      have ht : 0 < ‖w - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hwp)
      have htB : ‖w - p‖ ≤ ρ₁ := by
        have := hw.1; rwa [mem_closedBall, dist_eq_norm] at this
      simp only [hT1, Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (abs_log_max_le (D3Plus.radius_le_one' k) ht htB)
        (abs_nonneg a)
    · filter_upwards [hνp] with w hwp
      have ht : 0 < ‖w - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hwp)
      have hev : ∀ᶠ k in atTop, radius k < ‖w - p‖ :=
        (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
          (gt_mem_nhds ht)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with k hk
      simp only [hT1, max_eq_right hk.le]
  -- the continuous part: dominated convergence
  have hlim2 : Tendsto (fun k => ∫ w, T2 k w ∂ν) atTop (𝓝 (∫ w, h w ∂ν)) := by
    obtain ⟨Mb, hMb⟩ := (isCompact_closedBall (0 : ℂ) (|p| + ρ₁ + 1)).exists_bound_of_continuousOn
      hh.continuousOn
    have hM' : ∀ z : ℂ, ‖z‖ ≤ |p| + ρ₁ + 1 → |h z| ≤ Mb := fun z hz => by
      have := hMb z (by rw [mem_closedBall, dist_zero_right]; exact hz)
      rwa [Real.norm_eq_abs] at this
    refine tendsto_integral_of_dominated_convergence (fun _ => Mb)
      (fun k => (hT2c k).aestronglyMeasurable) (integrable_const _) (fun k => ?_) ?_
    · filter_upwards [hν] with w hw
      have hwp : ‖w - p‖ ≤ ρ₁ := by
        have := hw.1; rwa [mem_closedBall, dist_eq_norm] at this
      have hwn : ‖w‖ ≤ |p| + ρ₁ := by
        have := norm_add_le (w - p) (p : ℂ)
        rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at this
        linarith
      rw [Real.norm_eq_abs]
      exact WedgeUnzip.abs_smoothFun_le hM' (radius_pos k).le
        (by linarith [D3Plus.radius_le_one' k])
    · filter_upwards [hν] with w hw
      exact D3Plus.tendsto_integral_fc_radius hh hw.2
  -- assemble
  have hsum := (hlim1.add hlim2).add hA
  have hfi : ∫ w, f w ∂ν = (∫ w, a * -Real.log ‖w - p‖ ∂ν) + ∫ w, h w ∂ν := by
    have hli : Integrable (fun w : ℂ => a * -Real.log ‖w - (p : ℂ)‖) ν := hlog.neg.const_mul a
    rw [← integral_add hli
      (K3.integrable_of_continuousOn_closedBall_Hbar hh.continuousOn hnull)]
    refine integral_congr_ae (hν.mono fun w hw => hf w ⟨?_, hw.2⟩)
    exact closedBall_subset_closedBall hρ₁.le hw.1
  rw [hfi]
  refine hsum.congr' ?_
  filter_upwards [hk] with k hk
  rw [← integral_add (hT1i k) (hT2i k)]
  rw [← integral_add (f := fun w => T1 k w + T2 k w) ((hT1i k).add (hT2i k)) (hXi k)]
  refine integral_congr_ae (hν.mono fun w hw => ?_)
  show T1 k w + T2 k w + avgReg x k w = avgReg (ofFun f + x) k w
  have hwp : ‖w - p‖ ≤ ρ₁ := by
    have := hw.1; rwa [mem_closedBall, dist_eq_norm] at this
  rw [avgReg_ofFun_add_logSing hf hh (by linarith) ((hx k).2 w hw.2)]

end G3Za
end QuantumZipper
