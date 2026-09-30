import QuantumZipper.Proofs.Loewner.TwoPoint
import QuantumZipper.Proofs.Zipper.UnzipInvariance

/-!
# REG-CONT, deterministic part: the unzip maps in time

Blueprint `E_BRANCH_BLUEPRINT.md` §3, node REG-CONT. The unzip map at time `s` is
`ψ_s = fwdMapInv W s`. This file proves the deterministic inputs of the time-continuity
argument:

* `fwdMapInv_add`: the flow property `ψ_{s+h} = ψ_s ∘ ψ̃`, with `ψ̃ = revMap Ṽ h` the reverse map
  of the time-reversed increment `Ṽ r = W(s+h−r) − W(s+h)` on `[0,h]`
  (from `fwdMapInv_eq_revMap_timeRev` and `revMap_concat_eq`);
* `norm_revMap_sub_self_le`: `ψ̃` is close to the identity,
  `‖revMap V h z − z‖ ≤ sup_{[0,h]}|V| + 2h/Im z` (directly from the integral equation
  `u_h = z − V_h − ∫₀ʰ 2/u` and `Im u ≥ Im z`);
* `isFrostman_fwdMapInv_foldedCircle`: `(fc(w,r)).map ψ_s` is `IsFrostman` with exponent `1/3`
  and a constant uniform in `s ∈ [0,T]` (from `TwoPoint.isFrostman_revMap_foldedCircle`).

These are the standard facts behind the Kolmogorov argument for continuity of circle averages
of a GFF in their parameters (Hu, Miller, Peres, *Thick points of the Gaussian free field*,
Ann. Probab. 38 (2010), Prop. 2.1), transported through the Loewner flow; the flow property and
the near-identity bound are elementary (no source needed).
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace QuantumZipper
namespace RegCont

open TwoPoint UnzipInvariance

variable {W : ℝ → ℝ}

/-- **Flow property of the unzip maps.** `ψ_{s+h} = ψ_s ∘ revMap Ṽ h` on `ℍ`, where
`Ṽ r = W(s+h−r) − W(s+h)`. -/
theorem fwdMapInv_add (hW : Continuous W) (hW0 : W 0 = 0) {s h : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h)
    {w : ℂ} (hw : w ∈ H) :
    fwdMapInv W (s + h) w =
      fwdMapInv W s (revMap (fun r => W (s + h - r) - W (s + h)) h w) := by
  have hVc : Continuous fun r => W (s + h - r) - W (s + h) := by fun_prop
  have hwm : revMap (fun r => W (s + h - r) - W (s + h)) h w ∈ H :=
    im_revMap_pos hVc hw hh
  rw [fwdMapInv_eq_revMap_timeRev W hW hW0 (by linarith) hw,
    fwdMapInv_eq_revMap_timeRev W hW hW0 hs hwm]
  have key := revMap_concat_eq (W := fun r => W (s + h - r) - W (s + h)) hVc
    (W1 := fun r => W (s + h - r) - W (s + h)) (W2 := fun r => W (s - r) - W s) hh hs
    (fun _ _ => rfl) (fun r _ => by
      rw [show s + h - (h + r) = s - r by ring, show s + h - h = s by ring]
      ring) hw
  rw [show h + s = s + h by ring] at key
  exact key

/-- **Near-identity bound.** `‖revMap V h z − z‖ ≤ M + 2h/Im z` if `|V| ≤ M` on `[0,h]`. -/
theorem norm_revMap_sub_self_le {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ} (hz : z ∈ H) {h : ℝ}
    (hh : 0 ≤ h) {M : ℝ} (hM : ∀ r ∈ Icc (0 : ℝ) h, |V r| ≤ M) :
    ‖revMap V h z - z‖ ≤ M + 2 * h / z.im := by
  have hz0 : 0 < z.im := hz
  obtain ⟨u, hu⟩ := exists_isReverseSol V hV z hz0 h hh
  rw [revMap_eq V hV z hh le_rfl hu, (hu.2 h ⟨hh, le_rfl⟩).2]
  have hI : ‖∫ s in (0 : ℝ)..h, 2 / u s‖ ≤ 2 / z.im * |h - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
    rw [uIoc_of_le hh] at hr
    have hr' : r ∈ Icc (0 : ℝ) h := ⟨hr.1.le, hr.2⟩
    have hge : z.im ≤ (u r).im := ReverseFlow.isReverseSol_im_ge hu hr'
    have hnorm : z.im ≤ ‖u r‖ := hge.trans (Complex.im_le_norm _)
    rw [norm_div, Complex.norm_two]
    exact div_le_div_of_nonneg_left (by norm_num) hz0 hnorm
  rw [sub_zero, abs_of_nonneg hh] at hI
  have hVh : ‖((V h : ℝ) : ℂ)‖ ≤ M := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hM h ⟨hh, le_rfl⟩
  calc ‖(z - ↑(V h) - ∫ s in (0 : ℝ)..h, 2 / u s) - z‖
      = ‖-(((V h : ℝ) : ℂ)) - ∫ s in (0 : ℝ)..h, 2 / u s‖ := by congr 1; ring
    _ ≤ ‖((V h : ℝ) : ℂ)‖ + ‖∫ s in (0 : ℝ)..h, 2 / u s‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_neg]
    _ ≤ M + 2 * h / z.im := by
        have : 2 / z.im * h = 2 * h / z.im := by ring
        linarith

/-- **Uniform Frostman bound in time.** For `s ∈ [0,T]`, `r₀ ≤ r` and `‖w‖ + r ≤ R`,
`(fc(w,r)).map ψ_s` is `IsFrostman` with exponent `1/3` and constant
`18/√r₀ + 12√(R²+4T)/r₀`, independent of `s` and of the driver. -/
theorem isFrostman_fwdMapInv_foldedCircle (hW : Continuous W) (hW0 : W 0 = 0) {s T : ℝ}
    (hs : 0 ≤ s) (hsT : s ≤ T) {w : ℂ} {r r₀ R : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (hwR : ‖w‖ + r ≤ R) :
    TwoPoint.IsFrostman ((foldedCircle w r).map (fwdMapInv W s)) (1 / 3)
      (18 / Real.sqrt r₀ + 12 * Real.sqrt (R ^ 2 + 4 * T) / r₀) := by
  have hVc : Continuous fun r => W (s - r) - W s := by fun_prop
  have hmap : (foldedCircle w r).map (fwdMapInv W s) =
      (foldedCircle w r).map (revMap (fun r => W (s - r) - W s) s) := by
    refine Measure.map_congr ?_
    filter_upwards [foldedCircle_ae_mem_H w (hr₀.trans_le hr)] with x hx
    exact fwdMapInv_eq_revMap_timeRev W hW hW0 hs hx
  rw [hmap]
  have hF := isFrostman_revMap_foldedCircle hVc hs hr₀ hr hwR
  intro p ρ hρ
  refine (hF p ρ hρ).trans ?_
  have hsq : Real.sqrt (R ^ 2 + 4 * s) ≤ Real.sqrt (R ^ 2 + 4 * T) :=
    Real.sqrt_le_sqrt (by linarith)
  have hpow : 0 ≤ ρ ^ (1 / 3 : ℝ) := Real.rpow_nonneg hρ.le _
  gcongr

end RegCont
end QuantumZipper
