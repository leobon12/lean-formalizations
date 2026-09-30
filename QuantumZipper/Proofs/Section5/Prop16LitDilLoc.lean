import QuantumZipper.Proofs.Section5.Prop16LitDilDet3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: locality of the dilation event and of the scale (D98)

The dilation event `DilGood`, the cutoff mass `massB` and the rational scale `scaleQ` only read
the field on the dyadic circles in `B(0, r) ∩ ℍ` (`dilGood_congr`, `massB_congr`, `scaleQ_congr`)
and only through its circle averages (`dilGood_congr_avgReg`, …). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open ExA GoodSample

/-- Rescaled fields agree locally when the fields do. -/
theorem circAgree_rescale {Z Z' : FieldSample} {r s : ℝ} (hs : 0 < s)
    (h : Prop16Area.G.CircAgree (ball 0 r ∩ H) Z Z') (Q : ℝ) :
    Prop16Area.G.CircAgree (ball 0 (r / s) ∩ H) (rescale Z Q s) (rescale Z' Q s) := by
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  intro n k z hz hsub
  set d := dyadicRoundC n z
  have hd : d ∈ Hbar := CircleCont.dyadicRoundC_mem_Hbar hz n
  rw [Thm18Asm.G1.rescale_fc_apply Z Q hs, Thm18Asm.G1.rescale_fc_apply Z' Q hs,
    RegClosure.foldH_mul_pos _ hs, CircleFubini.foldH_of_mem' hd]
  congr 1
  have hsd : (s : ℂ) * d ∈ Hbar := by
    have h0 : (0 : ℝ) ≤ d.im := hd
    show (0 : ℝ) ≤ ((s : ℂ) * d).im
    rw [Complex.im_ofReal_mul]; exact mul_nonneg hs.le h0
  have hKU : closedBall ((s : ℂ) * d) (s * radius k) ∩ Hbar ⊆ ball 0 r ∩ H := by
    rintro w ⟨hw1, hw2⟩
    have hw' : w / s ∈ closedBall d (radius k) ∩ Hbar := by
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_eq_norm] at hw1 ⊢
        have e : w / s - d = (w - s * d) / s := by field_simp
        rw [e, norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, div_le_iff₀ hs]
        linarith
      · have h0 : (0 : ℝ) ≤ w.im := hw2
        show (0 : ℝ) ≤ (w / s).im
        rw [Complex.div_ofReal_im]; exact div_nonneg h0 hs.le
    have := hsub hw'
    rw [← preimage_mul_ball_inter_H hs] at this
    simpa [mul_div_cancel₀ _ hsc] using this
  refine Prop16Area.G.evalReg_eq_of_circAgree (isOpen_ball.inter isOpen_H) h
    (Prop16Area.G.isCompact_closedBall_inter_Hbar _ _) hKU ?_
  filter_upwards [G1Side.ae_fc_mem_closedBall hsd (mul_pos hs (radius_pos k)).le,
    RegClosure.fc_ae_mem_Hbar _ _] with u h1 h2 using ⟨⟨h1, h2⟩, h2⟩

/-- **Locality of the dilation event.** -/
theorem dilGood_congr {γ : ℝ} {Z Z' : FieldSample} {r s : ℝ} (hs : 0 < s)
    (h : Prop16Area.G.CircAgree (ball 0 r ∩ H) Z Z') (hD : DilGood γ Z r s) :
    DilGood γ Z' r s := by
  have hUo : IsOpen (ball (0 : ℂ) r ∩ H) := isOpen_ball.inter isOpen_H
  have hR := circAgree_rescale hs h (Qc γ)
  obtain ⟨hA, hC⟩ := hD
  refine ⟨goodA_congr hR hA, fun n g hg => ?_⟩
  obtain ⟨l, h1, h2⟩ := hC n g hg
  obtain ⟨hgc, hgs, -⟩ := famF_dense.1 g hg
  have hFc : Continuous fun z => hbCut (r / s) n z * g z := (continuous_hbCut _ n).mul hgc
  have hFs : HasCompactSupport fun z => hbCut (r / s) n z * g z := hgs.mul_left
  have hFU : tsupport (fun z => hbCut (r / s) n z * g z) ⊆ ball 0 (r / s) ∩ H :=
    (tsupport_mul_subset_left).trans (tsupport_hbCut _ n)
  obtain ⟨-, hGs, hGU⟩ := test_div hs hFc hFs hFU
  refine ⟨l, h1.congr' ?_, h2.congr' ?_⟩
  · exact eventually_integral_eq_of_circAgree (isOpen_ball.inter isOpen_H) inter_subset_right hR
      hFs hFU
  · exact eventually_integral_eq_of_circAgree hUo inter_subset_right h hGs hGU

theorem massB_congr {γ : ℝ} {Z Z' : FieldSample} {r : ℝ}
    (h : Prop16Area.G.CircAgree (ball 0 r ∩ H) Z Z') (a : ℝ) :
    massB γ Z r a = massB γ Z' r a := by
  unfold massB
  congr 1
  funext n
  congr 1
  have hs : HasCompactSupport (hbCut (min a r) n) :=
    (isCompact_closedBall (0 : ℂ) (min a r)).of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_hbCut _ n).trans (inter_subset_left.trans ball_subset_closedBall))
  have hsub : tsupport (hbCut (min a r) n) ⊆ ball 0 r ∩ H :=
    (tsupport_hbCut _ n).trans (inter_subset_inter_left _ (ball_subset_ball (min_le_right _ _)))
  have hev := eventually_integral_eq_of_circAgree (γ := γ) (isOpen_ball.inter isOpen_H)
    inter_subset_right h hs hsub
  unfold limUnder
  rw [Filter.map_congr hev]

theorem scaleQ_congr {γ : ℝ} {Z Z' : FieldSample} {r : ℝ}
    (h : Prop16Area.G.CircAgree (ball 0 r ∩ H) Z Z') : scaleQ γ Z r = scaleQ γ Z' r := by
  unfold scaleQ
  simp_rw [massB_congr h]

/-- Rescaling only sees the circle averages. -/
theorem rescale_congr_avgReg {x x' : FieldSample} (h : avgReg x = avgReg x') (Q s : ℝ) :
    rescale x Q s = rescale x' Q s := by
  funext μ
  simp only [rescale, coordChange, Factorization.evalReg_congr h]

theorem areaApprox_congr_avgReg' {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x') :
    areaApprox γ x = areaApprox γ x' := by
  funext k; simp only [areaApprox, h]

theorem dilGood_congr_avgReg {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x') (r s : ℝ) :
    DilGood γ x r s ↔ DilGood γ x' r s := by
  unfold DilGood GoodA
  rw [rescale_congr_avgReg h, areaApprox_congr_avgReg' h]

theorem scaleQ_congr_avgReg {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x') (r : ℝ) :
    scaleQ γ x r = scaleQ γ x' r := by
  unfold scaleQ massB
  rw [areaApprox_congr_avgReg' h]

end Prop16Lit
end QuantumZipper
