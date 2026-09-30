import QuantumZipper.Proofs.Zipper.Cor15RezipRegTame
import QuantumZipper.Proofs.Zipper.Cor15RezipRegHull
import QuantumZipper.Proofs.RS.HolderBox
import QuantumZipper.Proofs.RS.TipB
import QuantumZipper.Proofs.Thm11.CharFunRhs
import QuantumZipper.Proofs.Loewner.Algebra

/-!
# Corollary 1.5, input R: almost every driver is good

Task COR15-R. For `W = √κ B` (`0 < κ < 4`), `t > 0`, `V = vrev W t` and a folded circle
`σ = fc(w₀, r₀)`, almost surely `V` satisfies every hypothesis of the fixed-driver theorem
`ae_evalReg_coordChange_pushed_fc` (`ae_rezip_good`):

* `V` is continuous, `V 0 = 0` and bounded on `[0,t]`;
* `F = revMap V t` is Hölder on bounded parts of `ℍ` (Rohde–Schramm 2005, Thm 5.2, in the
  reverse-time form `RS.ae_revMap_holder`, applied to the reversed Brownian motion `B'` of
  `UnzipFull.exists_unzip_driver`, since `revMap V t = fwdMapInv W t = revMap (√κ B') t` on `ℍ`,
  `B2.fwdMapInv_eq_revMap_vrev`);
* the hull `ℍ \ F(ℍ) = revHull V t = fwdHull W t` (Sheffield's A1(c),
  `LoewnerAlgebra.revHull_eq_fwdHull_timeRev`) lies in the trace `η[0,∞)` (Rohde–Schramm 2005,
  Thm 6.1, `RS.ae_fwdHull_eq_sleTrace_image_of_le_four`);
* `σ{dist(·, η) ≤ ε} ≤ c ε^{1/8}` (`ae_measure_infDist_le_pow`), hence `σ(hull) = 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B2

/-- The reverse hull of the time-reversed driver is the forward hull (A1(c) plus the hull
depending only on the driver on `[0,t]`). Same argument as in `Cor15HullNull.lean`. -/
theorem rezip_revHull_vrev_eq_fwdHull {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 < t) : revHull (vrev W t) t = fwdHull W t := by
  have hVc : Continuous (vrev W t) := continuous_vrev hW t
  have hV0 : vrev W t 0 = 0 := by simp [vrev, ht.le]
  rw [LoewnerAlgebra.revHull_eq_fwdHull_timeRev _ hVc hV0 ht]
  refine CharFunRhs.fwdHull_eq_of_eqOn (by unfold vrev; fun_prop) hW ht.le ?_
  intro r hr
  have h1 : min (max (t - r) 0) t = t - r := by
    rw [max_eq_left (by linarith [hr.2]), min_eq_left (by linarith [hr.1])]
  simp only [vrev, h1, max_eq_left ht.le, min_self, sub_self, hW0]
  ring_nf

/-- Folded circles have a finite `(Im)^{-1/4}` moment. -/
theorem lintegral_im_rpow_fc_ne_top (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ z, ENNReal.ofReal (z.im ^ (-(1 / 4 : ℝ))) ∂foldedCircle w r ≠ ⊤ := by
  refine lintegral_im_rpow_neg_ne_top (TwoPoint.foldedCircle_ae_mem_H w hr)
    (A := 18 / Real.sqrt r) (a := 1 / 2) (by positivity) (by norm_num) (by norm_num)
    fun τ hτ => ?_
  refine (measure_mono_ae ?_).trans ((TwoPoint.foldedCircle_strip_le w hr hτ).trans
    (le_of_eq ?_))
  · filter_upwards [TwoPoint.foldedCircle_ae_mem_H w hr] with z hz hzτ
    have hz0 : 0 < z.im := hz
    change z.im < τ at hzτ
    show |z.im| < τ
    rw [abs_of_pos hz0]
    exact hzτ
  · congr 1
    rw [Real.sqrt_div' τ hr.le, Real.sqrt_eq_rpow]
    ring

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Almost every driver is good** for the fixed-driver regularity theorem. -/
theorem ae_rezip_good (hB : IsBrownianReal B P) (hind : IndepFun (pathOf B) X P) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {t : ℝ} (ht : 0 < t) (w₀ : ℂ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P,
      Continuous (vrev (drive κ B ω) t) ∧ vrev (drive κ B ω) t 0 = 0 ∧
      H \ revMap (vrev (drive κ B ω) t) t '' H ⊆ sleTrace κ B ω '' Ici 0 ∧
      foldedCircle w₀ r₀ (H \ revMap (vrev (drive κ B ω) t) t '' H) = 0 ∧
      (∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        foldedCircle w₀ r₀ {z | infDist z (sleTrace κ B ω '' Ici 0) ≤ ε} ≤
          ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ))) ∧
      ∃ M : ℝ, (∀ r ∈ Icc (0 : ℝ) t, |vrev (drive κ B ω) t r| ≤ M) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ‖w₀‖ + r₀ + (12 * M + 8 * Real.sqrt t) →
          ‖w‖ ≤ ‖w₀‖ + r₀ + (12 * M + 8 * Real.sqrt t) →
          ‖revMap (vrev (drive κ B ω) t) t z - revMap (vrev (drive κ B ω) t) t w‖ ≤
            C * ‖z - w‖ ^ β := by
  obtain ⟨B', hB', -, -, -, hEq⟩ := UnzipFull.exists_unzip_driver κ hB hind ht.le
  obtain ⟨β, hβ, hHol⟩ := RS.ae_revMap_holder hB' hκ hκ4 ht
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero, hEq, hHol,
    RS.ae_fwdHull_eq_sleTrace_image_of_le_four hB hκ hκ4.le,
    ae_measure_infDist_le_pow hB hκ hκ4 (TwoPoint.foldedCircle_ae_mem_H w₀ hr₀)
      (lintegral_im_rpow_fc_ne_top w₀ hr₀)] with ω hc h0 hEqω hHolω hHull hmass
  have hWc : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hVc : Continuous (vrev (drive κ B ω) t) := continuous_vrev hWc t
  have hV0 : vrev (drive κ B ω) t 0 = 0 := by simp [vrev, ht.le]
  -- the hull lies in the trace
  have hS : H \ revMap (vrev (drive κ B ω) t) t '' H ⊆ sleTrace κ B ω '' Ici 0 := by
    change revHull (vrev (drive κ B ω) t) t ⊆ _
    rw [rezip_revHull_vrev_eq_fwdHull hWc hW0 ht, hHull t ht.le]
    exact image_mono fun x hx => mem_Ici.2 (le_of_lt hx.1)
  obtain ⟨c₀, hc₀⟩ := hmass
  set c := max c₀ 0 with hcdef
  have hc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      foldedCircle w₀ r₀ {z | infDist z (sleTrace κ B ω '' Ici 0) ≤ ε} ≤
        ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ)) := fun ε hε hε1 =>
    (hc₀ ε hε hε1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  -- the hull is null
  have hK : foldedCircle w₀ r₀ (H \ revMap (vrev (drive κ B ω) t) t '' H) = 0 := by
    have hle : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        foldedCircle w₀ r₀ (H \ revMap (vrev (drive κ B ω) t) t '' H) ≤
          ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ)) := by
      intro ε hε hε1
      refine (measure_mono fun z hz => ?_).trans (hc ε hε hε1)
      show infDist z (sleTrace κ B ω '' Ici 0) ≤ ε
      rw [infDist_zero_of_mem (hS hz)]
      exact hε.le
    have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (c * (0 : ℝ) ^ (1 / 8 : ℝ)))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        (((continuous_const.mul (Real.continuous_rpow_const (by norm_num))).tendsto 0).mono_left
          nhdsWithin_le_nhds)
    rw [Real.zero_rpow (by norm_num), mul_zero, ENNReal.ofReal_zero] at hlim
    refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact hle ε hε.1 hε.2.le
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hVc.continuousOn
  obtain ⟨C₀, hC₀⟩ := hHolω (‖w₀‖ + r₀ + (12 * M + 8 * Real.sqrt t))
  refine ⟨hVc, hV0, hS, hK, ⟨c, le_max_right _ _, hc⟩, M,
    fun r hr => by simpa [Real.norm_eq_abs] using hM r hr, max C₀ 1,
    lt_max_of_lt_right one_pos, ?_⟩
  intro z hz w hw hzρ hwρ
  rw [← fwdMapInv_eq_revMap_vrev hWc hW0 ht.le hz, ← fwdMapInv_eq_revMap_vrev hWc hW0 ht.le hw,
    hEqω hz, hEqω hw]
  exact (hC₀ z hz w hw hzρ hwρ).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-! ## Changing the conformal map off `ℍ` -/

section Congr

variable {F F' : ℂ → ℂ}

theorem coordChange_congr_H (x : FieldSample) (hFF : EqOn F F' H) (Q : ℝ) {μ : Measure ℂ}
    (hμ : ∀ᵐ z ∂μ, z ∈ H) : coordChange x F Q μ = coordChange x F' Q μ := by
  unfold coordChange
  have h1 : μ.map F = μ.map F' := Measure.map_congr (hμ.mono fun z hz => hFF hz)
  have h2 : ∫ z, Real.log ‖deriv F z‖ ∂μ = ∫ z, Real.log ‖deriv F' z‖ ∂μ :=
    integral_congr_ae (hμ.mono fun z hz => by
      show Real.log ‖deriv F z‖ = Real.log ‖deriv F' z‖
      rw [Filter.EventuallyEq.deriv_eq (eventuallyEq_of_mem (isOpen_H.mem_nhds hz) hFF)])
  rw [h1, h2]

theorem avgReg_coordChange_congr_H (x : FieldSample) (hFF : EqOn F F' H) (Q : ℝ) :
    avgReg (coordChange x F Q) = avgReg (coordChange x F' Q) := by
  funext k z
  unfold avgReg
  congr 1
  funext n
  exact coordChange_congr_H x hFF Q (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k))

/-- Regularity of the unzipped field at `ν` (carried by `ℍ`) reduces to regularity of
`coordChange x (revMap (vrev W t) t) Q`, the map of the fixed-driver theorem. -/
theorem evalReg_unzip_eq_of {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (x : FieldSample) (Q : ℝ) {ν : Measure ℂ} (hνH : ∀ᵐ z ∂ν, z ∈ H)
    (h : evalReg (coordChange x (revMap (vrev W t) t) Q) ν =
      coordChange x (revMap (vrev W t) t) Q ν) :
    evalReg (coordChange x (fwdMapInv W t) Q) ν = coordChange x (fwdMapInv W t) Q ν := by
  have hFF : EqOn (fwdMapInv W t) (revMap (vrev W t) t) H := fun z hz =>
    fwdMapInv_eq_revMap_vrev hW hW0 ht hz
  rw [Factorization.evalReg_congr (avgReg_coordChange_congr_H x hFF Q),
    coordChange_congr_H x hFF Q hνH]
  exact h

end Congr

end Cor15Group
end QuantumZipper
