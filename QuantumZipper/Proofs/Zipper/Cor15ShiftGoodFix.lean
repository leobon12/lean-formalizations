import QuantumZipper.Proofs.Zipper.Cor15TdensFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-SHIFTGOOD (1): convergence form of RC3 at pushed folded circles, fixed driver

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18)
and §5.1 (rule (5.1)). Convergence-form companion (`E1.RegShift`: integrability of every
`avgReg · j` and convergence of the regularized integrals) of
`ae_evalReg_coordChange_pushed_fc` (`Cor15RezipRegTame`, which only records the value
`evalReg = raw`). Same hypotheses and the same tameness bookkeeping; the final analytic input is
the convergence form `CoordReg.ae_regShift_coordChange_revMap_gen` of RC3 for general measures
(Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1), exactly as in `ae_regShift_evalReg_pushed_tdens` (`Cor15TdensFixed`).

**Own elementary argument** (the proof of `ae_evalReg_coordChange_pushed_fc` with the final
call replaced).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

variable {V : ℝ → ℝ} {t : ℝ}

section Fix

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Convergence form of (R) for a fixed good driver**: a.s. in the free field `X`, the
pulled-back field `coordChange (𝔥₀ + X) (revMap V t) Q` satisfies `E1.RegShift` at the pushed
folded circle `σ.map (revMapInv V t)`. -/
theorem ae_regShift_coordChange_pushed_fc (hX : IsFreeGFFModConstH X P)
    [IsProbabilityMeasure P]
    (κ Q : ℝ) (hV : Continuous V) (hV0 : V 0 = 0) (ht : 0 < t) {w₀ : ℂ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hK : foldedCircle w₀ r₀ (H \ revMap V t '' H) = 0) {S : Set ℂ}
    (hS : H \ revMap V t '' H ⊆ S) {M : ℝ} (hM : ∀ r ∈ Icc (0 : ℝ) t, |V r| ≤ M) {C β : ℝ}
    (hC : 0 < C) (hβ : 0 < β)
    (hHol : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ‖w₀‖ + r₀ + (12 * M + 8 * Real.sqrt t) →
      ‖w‖ ≤ ‖w₀‖ + r₀ + (12 * M + 8 * Real.sqrt t) →
      ‖revMap V t z - revMap V t w‖ ≤ C * ‖z - w‖ ^ β)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      foldedCircle w₀ r₀ {z | infDist z S ≤ ε} ≤ ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ))) :
    ∀ᵐ ω ∂P,
      E1.RegShift (coordChange (ofFun (h0rev κ) + X ω) (revMap V t) Q)
        ((foldedCircle w₀ r₀).map (revMapInv V t)) := by
  set ρ := ‖w₀‖ + r₀ + (12 * M + 8 * Real.sqrt t) with hρ
  set σ := foldedCircle w₀ r₀ with hσ
  have hσD := ae_mem_revMap_image_fc hr₀ hK
  have hσρ : ∀ᵐ z ∂σ, ‖revMapInv V t z‖ ≤ ρ := by
    filter_upwards [hσD, TwoPoint.foldedCircle_ae_norm_le w₀ hr₀.le] with z hz hzn
    exact (norm_revMapInv_le hV hV0 ht hM hz).trans (by rw [hρ]; linarith)
  set ν := σ.map (revMapInv V t) with hν
  have hνP : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (measurable_revMapInv hV ht.le).aemeasurable).2
      inferInstance
  have hsupp := map_revMapInv_compl_closedBall_Hbar hV ht.le hσD hσρ
  have hνH := ae_mem_H_map_revMapInv hV ht.le hσD
  have hF := isFrostman_map_revMapInv_fc hV ht.le hr₀ hC.le hβ hHol hσD hσρ
  have hpow := map_revMapInv_fc_im_lt_le hV ht.le hr₀ hS hC hβ hHol hσD hσρ hc0 hc
  have hA0 : 0 ≤ (18 * Real.sqrt (2 / r₀) + c + 1) * C ^ (1 / 8 : ℝ) := by positivity
  have hβ8 : 0 < β / 8 := by positivity
  have hSt := stripBound_of_pow hνH hA0 hβ8 hpow
  have hR : ∀ᵐ z ∂ν, z.im ≤ ρ := by
    filter_upwards [(mem_ae_iff.2 hsupp : ∀ᵐ z ∂ν, z ∈ closedBall (0 : ℂ) ρ ∩ Hbar)] with z hz
    have h1 := hz.1
    rw [mem_closedBall, dist_zero_right] at h1
    exact (Complex.im_le_norm z).trans h1
  have hlν := integrable_abs_log_im_of_pow hνH hR hA0 hβ8 hpow
  have hFf : IsFrostman (ν.map (revMap V t)) 1 (6 / r₀) := by
    rw [hν, map_revMap_map_revMapInv hV ht.le hσD]
    exact isFrostman_fc w₀ hr₀
  have hA := CoordReg.ae_regShift_coordChange_revMap_gen hV ht.le hX (P := P)
    (2 / Real.sqrt κ) (g₁ := fun _ => 0) continuous_const Q hsupp hνH hF hβ hlν hSt
    (by positivity) hFf one_pos
  rw [← CoordReg.h0rev_eq_logAdd κ] at hA
  filter_upwards [hA] with ω hA
  obtain ⟨hreg, hint, L, hL⟩ := hA
  refine ⟨hνH.mono fun z hz k => ?_, hint, L, hL⟩
  obtain ⟨F, -, hF2, -⟩ := hreg
  exact ⟨_, hF2 k z (H_subset_Hbar hz)⟩

end Fix

end Cor15Group
end QuantumZipper
