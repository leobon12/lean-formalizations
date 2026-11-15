/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BHMean
import InteractingSLE.Spec.Sec5.CrossRestartKernelObst
import InteractingSLE.WangWu.ReverseContactBdryLimit
import InteractingSLE.WangWu.SideValues

/-!
# The relative transition: the hull image of a Loewner chain is the interval `[a_L, a_R]`

Packet PROVE-RELTRANS. For a continuous Loewner trace (curves allowed to hit `ℝ`), the **hull image**
`I_u = {x ∈ ℝ | F̄_u(x) ∈ cl K_u}` (the real points at which the boundary extension `F̄_u` of the inverse map lands
on the closed hull) is the closed interval `[a_L, a_R]` of the images of `0∓` (`WangWu.chartAL`, `WangWu.chartAR`),
as soon as `a_L < a_R`:

* right of `a_R` (left of `a_L`) the inverse map lands at an alive positive (negative) real point, off the closed hull:
  every value above `g_u(0⁺)` is the image `g_u(r)` of an alive positive point `r`
  (`Restart.RetAux79.exists_alive_gImg_eq`), and `F̄_u(f_u(r)) = r`
  (`Sec5.CrossRestart.extendFrom_eq_of_isForwardSol_real`);
* conversely a real point `x` at which `F̄_u` lands off the closed hull is the image `f_u(y)` of the alive real point
  `y = F̄_u(x) ≠ 0`, hence `x ≥ a_R` (`y > 0`) or `x ≤ a_L` (`y < 0`) (`WangWu.rightImg_sub_le_re_fwdMap`,
  `WangWu.re_fwdMap_le_neg_rightImg`);
* `I_u` is closed (`F̄_u` is continuous on `ℍ̄`).

This is the missing interval property of PROVE-BHMEAN §4.1 step 5, for a general (boundary-hitting) curve-generated
hull; the landed versions (`Sec5.CrossRestart.re_extendFrom_pos_of_chartAR_lt_of_mem_H`) assume the trace stays in `ℍ`.

* `notMem_closure_fwdHull_of_isForwardSol`;
* `extendFrom_notMem_closure_of_chartAR_lt`, `extendFrom_notMem_closure_of_lt_chartAL`;
* `chartAR_le_or_le_chartAL_of_notMem_closure`;
* `isClosed_hullImage`, **`hullImage_subset_Icc`**, **`Icc_subset_hullImage`**.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.Supp8.RelTrans

open MartChar.RealFlow
open WangWu (chartAL chartAR)

section HullImage

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {u : ℝ}

/-- **A starting point with a forward solution is off the closed hull.** -/
theorem notMem_closure_fwdHull_of_isForwardSol (hW : Continuous W) {p : ℂ} {T : ℝ} {v : ℝ → ℂ} (hT : 0 ≤ T)
    (hv : IsForwardSol W p T v) : p ∉ closure (fwdHull W T) := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hT hv
  set E := Real.exp (2 / δ ^ 2 * T) with hE
  have hEpos : 0 < E := Real.exp_pos _
  intro hmem
  obtain ⟨z, hzK, hzd⟩ := Metric.mem_closure_iff.1 hmem (δ / E) (div_pos hδ hEpos)
  refine not_mem_fwdHull_of_isForwardSol hW hv hδ hlow hzK.1 ?_ hzK
  rw [dist_comm, dist_eq_norm] at hzd
  calc ‖z - p‖ * E < δ / E * E := mul_lt_mul_of_pos_right hzd hEpos
    _ = δ := div_mul_cancel₀ δ hEpos.ne'

/-- **Right of `a_R` the inverse map lands off the closed hull** (at an alive positive real point). -/
theorem extendFrom_notMem_closure_of_chartAR_lt (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hu : 0 ≤ u) {x : ℝ} (hx : chartAR W u < x) :
    extendFrom H (fwdMapInv W u) (x : ℂ) ∉ closure (fwdHull W u) := by
  have hM : rightImg W 0 u < x + W u := by rw [WangWu.chartAR] at hx; linarith
  obtain ⟨r, -, hal, hg⟩ := Restart.RetAux79.exists_alive_gImg_eq hW hu hM
  have hv := WangWu.isForwardSol_of_alive hW hal
  have hc : cflow W r u = x := by simp only [gImg] at hg; linarith
  have h := Sec5.CrossRestart.extendFrom_eq_of_isForwardSol_real hη hW hW0 hu hv
  simp only [hc] at h
  rw [h]
  exact notMem_closure_fwdHull_of_isForwardSol hW hu hv

/-- **Left of `a_L` the inverse map lands off the closed hull** (at an alive negative real point). -/
theorem extendFrom_notMem_closure_of_lt_chartAL (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hu : 0 ≤ u) {x : ℝ} (hx : x < chartAL W u) :
    extendFrom H (fwdMapInv W u) (x : ℂ) ∉ closure (fwdHull W u) := by
  have hM : rightImg (fun s => -W s) 0 u < -x - W u := by rw [WangWu.chartAL] at hx; linarith
  obtain ⟨y, -, hal, hg⟩ := Restart.RetAux79.exists_alive_gImg_eq hW.neg hu hM
  have hv := WangWu.isForwardSol_neg_of_alive hW hal
  have hv' : IsForwardSol W ((-y : ℝ) : ℂ) u (fun s => -(cflow (fun s => -W s) y s : ℂ)) := by
    rw [Complex.ofReal_neg]; exact hv
  have hg' : -W u + cflow (fun s => -W s) y u = -x - W u := hg
  have hc : cflow (fun s => -W s) y u = -x := by linarith
  have h := Sec5.CrossRestart.extendFrom_eq_of_isForwardSol_real hη hW hW0 hu hv'
  simp only [hc, Complex.ofReal_neg, neg_neg] at h
  rw [h]
  have := notMem_closure_fwdHull_of_isForwardSol hW hu hv'
  rwa [Complex.ofReal_neg] at this

/-- **A real point at which the inverse map lands off the closed hull lies outside `(a_L, a_R)`** (for `u > 0`). -/
theorem chartAR_le_or_le_chartAL_of_notMem_closure (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hu : 0 < u) {x : ℝ} (hx : extendFrom H (fwdMapInv W u) (x : ℂ) ∉ closure (fwdHull W u)) :
    chartAR W u ≤ x ∨ x ≤ chartAL W u := by
  set y : ℂ := extendFrom H (fwdMapInv W u) (x : ℂ) with hydef
  have hyim : y.im = 0 := BHMean.im_extendFrom_eq_zero_of_notMem_closure hη hW hW0 hu.le hx
  have hyr : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [hyim])
  have hy0 : y.re ≠ 0 := by
    intro h0
    apply hx
    have h0' : y = 0 := by rw [hyr, h0]; simp
    rw [h0']
    exact ConformalImageFull.zero_mem_closure_fwdHull hW hW0 hu
  have hxeq := BHMean.eq_fwdMap_of_extendFrom_notMem_closure hη hW hW0 hu.le hx hy0
  have hyK : ((y.re : ℝ) : ℂ) ∉ closure (fwdHull W u) := by rw [← hyr]; exact hx
  obtain ⟨v, hv⟩ := BHMean.exists_isForwardSol_of_notMem_closure hW hW0 hu.le hyK hy0
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · right
    have h := WangWu.re_fwdMap_le_neg_rightImg hW hW0 hu.le hneg hv
    rw [WangWu.chartAL]
    linarith
  · left
    have h := WangWu.rightImg_sub_le_re_fwdMap hW hW0 hu.le hpos hv
    rw [WangWu.chartAR]
    linarith

/-- The real points at which the inverse map lands on the closed hull form a closed set. -/
theorem isClosed_hullImage (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 ≤ u) :
    IsClosed {x : ℝ | extendFrom H (fwdMapInv W u) (x : ℂ) ∈ closure (fwdHull W u)} := by
  have hc : ContinuousOn (extendFrom H (fwdMapInv W u)) Hbar := (hη.hasBdryLimits hW hW0 hu).continuousOn
  have hc' : Continuous fun x : ℝ => extendFrom H (fwdMapInv W u) (x : ℂ) :=
    hc.comp_continuous Complex.continuous_ofReal fun x => show (0 : ℝ) ≤ (x : ℂ).im by simp
  exact isClosed_closure.preimage hc'

/-- **The hull image lies in `[a_L, a_R]`.** -/
theorem hullImage_subset_Icc (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 ≤ u) {x : ℝ}
    (hx : extendFrom H (fwdMapInv W u) (x : ℂ) ∈ closure (fwdHull W u)) : x ∈ Icc (chartAL W u) (chartAR W u) := by
  by_contra h
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact extendFrom_notMem_closure_of_lt_chartAL hη hW hW0 hu h hx
  · exact extendFrom_notMem_closure_of_chartAR_lt hη hW hW0 hu h hx

/-- **`[a_L, a_R]` lies in the hull image** (for `u > 0` and `a_L < a_R`). -/
theorem Icc_subset_hullImage (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 < u)
    (hlt : chartAL W u < chartAR W u) :
    Icc (chartAL W u) (chartAR W u) ⊆ {x : ℝ | extendFrom H (fwdMapInv W u) (x : ℂ) ∈ closure (fwdHull W u)} := by
  have hIoo : Ioo (chartAL W u) (chartAR W u) ⊆
      {x : ℝ | extendFrom H (fwdMapInv W u) (x : ℂ) ∈ closure (fwdHull W u)} := fun x hx => by
    by_contra hxI
    rcases chartAR_le_or_le_chartAL_of_notMem_closure hη hW hW0 hu hxI with h | h
    · exact absurd hx.2 (not_lt.2 h)
    · exact absurd hx.1 (not_lt.2 h)
  rw [← closure_Ioo hlt.ne]
  exact (isClosed_hullImage hη hW hW0 hu.le).closure_subset_iff.2 hIoo

end HullImage

end InteractingSLE.Supp8.RelTrans
