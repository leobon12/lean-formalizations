import QuantumZipper.Proofs.Zipper.JointModDet
import QuantumZipper.Proofs.Zipper.JointModAssembly

/-!
# JOINTMOD: the deterministic part is jointly continuous (`DetContStmt` proved)

`detContStmt_holds κ γ T : DetContStmt κ γ T`: for every continuous driver `W` with `W 0 = 0`,

`(t, c, r) ↦ (2/√κ) ∫ log ‖z‖ dν_t(c,r) + Q ∫ log ‖(ψ_t)'‖ dfc(c,r)`

is continuous on `[0,T] × Hbar × (0,∞)`. Both terms are folded-circle means of integrands
`G(t,u)` (`log ‖ψ_t(u)‖` and `log ‖ψ_t'(u)‖`) that are jointly continuous on `[0,T] × ℍ`
(`JointModDet`) and bounded by `A + |log Im u|` uniformly in `t` (reverse-map bounds
`RegCont.norm_revMap_le_revBound`, `TwoPoint.abs_log_norm_deriv_revMap_le`), so
`continuousOn_integral_foldedCircle_param` applies. **Own elementary argument** (the fixed-time
version is `TwoPoint.continuousOn_integral_foldedCircle` / `CoordReg.continuousOn_Dfun`).
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint UnzipInvariance

/-- **`DetContStmt` holds.** -/
theorem detContStmt_holds (κ γ T : ℝ) : DetContStmt κ γ T := by
  intro W hW hW0
  rcases lt_or_ge T 0 with hT | hT
  · intro p hp
    exact absurd (hp.1.1.trans hp.1.2) (not_le.2 hT)
  set G1 : ℝ → ℂ → ℝ := fun t u => Real.log ‖revMap (vRev W t) t u‖ with hG1
  set G2 : ℝ → ℂ → ℝ := fun t u => Real.log ‖deriv (revMap (vRev W t) t) u‖ with hG2
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
  have hc2 : ContinuousOn (fun p : ℝ × (ℂ × ℝ) => ∫ u, G2 p.1 u ∂foldedCircle p.2.1 p.2.2)
      (Icc 0 T ×ˢ {p : ℂ × ℝ | 0 < p.2}) := by
    refine continuousOn_integral_foldedCircle_param hT (fun t _ =>
      Real.measurable_log.comp (measurable_deriv _).norm) ?_ ?_
    · refine (continuousOn_log_deriv_fwdMapInv_joint hW hW0 T).congr fun p hp => ?_
      show Real.log ‖deriv (revMap (vRev W p.1) p.1) p.2‖ =
        Real.log ‖deriv (fwdMapInv W p.1) p.2‖
      rw [deriv_fwdMapInv_eq hW hW0 hp.1.1 hp.2]
    · intro R
      set R' := max R 1
      refine ⟨|Real.log (Real.sqrt (R' ^ 2 + 4 * T))|, abs_nonneg _, fun t ht u hu huR => ?_⟩
      have hV := continuous_vRev hW t
      have hb := abs_log_norm_deriv_revMap_le hV ht.1 hu (R := R')
        ((Complex.im_le_norm u).trans (huR.trans (le_max_left _ _)))
      have hR'1 : 1 ≤ R' := le_max_right _ _
      have hlo : 1 ≤ Real.sqrt (R' ^ 2 + 4 * t) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by nlinarith [ht.1])
      have hhi : Real.sqrt (R' ^ 2 + 4 * t) ≤ Real.sqrt (R' ^ 2 + 4 * T) :=
        Real.sqrt_le_sqrt (by linarith [ht.2])
      have hm := abs_log_le_of_mem one_pos hlo hhi
      rw [Real.log_one, abs_zero, zero_add] at hm
      show |Real.log ‖deriv (revMap (vRev W t) t) u‖| ≤ _
      linarith
  have hsub : parSet T ⊆ Icc 0 T ×ˢ {p : ℂ × ℝ | 0 < p.2} := fun p hp => ⟨hp.1, hp.2.2⟩
  have hcont : ContinuousOn (fun p : ℝ × (ℂ × ℝ) =>
      2 / Real.sqrt κ * (∫ u, G1 p.1 u ∂foldedCircle p.2.1 p.2.2) +
        Qc γ * ∫ u, G2 p.1 u ∂foldedCircle p.2.1 p.2.2) (parSet T) :=
    (continuousOn_const.mul (hc1.mono hsub)).add (continuousOn_const.mul (hc2.mono hsub))
  refine hcont.congr fun p hp => ?_
  have hr : 0 < p.2.2 := hp.2.2
  simp only [Ddet]
  congr 2
  · show ∫ z, Real.log ‖z‖ ∂(foldedCircle p.2.1 p.2.2).map (fwdMapInv W p.1) = _
    rw [integral_map (aemeasurable_fwdMapInv hW hW0 hp.1.1 p.2.1 hr)
      measurable_norm.log.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [foldedCircle_ae_mem_H p.2.1 hr] with u hu
    show Real.log ‖fwdMapInv W p.1 u‖ = Real.log ‖revMap (vRev W p.1) p.1 u‖
    rw [fwdMapInv_eq_revMap_timeRev W hW hW0 hp.1.1 hu]
  · refine integral_congr_ae ?_
    filter_upwards [foldedCircle_ae_mem_H p.2.1 hr] with u hu
    show Real.log ‖deriv (fwdMapInv W p.1) u‖ = Real.log ‖deriv (revMap (vRev W p.1) p.1) u‖
    rw [deriv_fwdMapInv_eq hW hW0 hp.1.1 hu]

end RegUnif
end QuantumZipper
