import QuantumZipper.Proofs.Thm18.A1RS3Scale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (3): the rescaling identity for the smeared-loop pairings (pathwise)

`y` has the regularized averages of `rescale Z Q b` (the canonical wedge field and its unscaled
field `Z = X + α₀(−log|·|) + G`), the driver of `y` is `W = V(b² ·)/b`, `ψ_W = b⁻¹ ψ_V(μ⁻¹ ·)`
(`sideMap_scale`). With `T p = (b² t, μ⁻¹ d, μ⁻¹ s)`:

* `evalReg_smear_rescale_pos` (`ρ > 0`): `evalReg y ν^W_{p,ρ} = evalReg Z ν^V_{Tp, bρ} + Q log b`
  (the smeared pairings are integrals of the per-loop pairings, `A1RF.integral_evalReg_fc_eq_nu`;
  per-loop rescaling `evalReg_loop_rescale`; scaling of the pushed side circles `a1rMu_scale`);
* `evalReg_sidePush_rescale` (`ρ = 0`): the same for `ν_{p,0} = ψ_* fc(d, s)`, given the
  continuum limit of the continuous-radius pairings of `y` against `ψ_W* fc(d, s)`
  (`F1.ContData`; `evalReg_eq_of_contData_rescale`).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm F1 B3d.ZipLen

variable {κ : ℝ} {X Z : FieldSample} {FX : ℂ × ℝ → ℝ} {G : ℂ → ℝ} {V : ℝ → ℝ}

/-- The circle pairings of the rescaled field. -/
theorem evalReg_fc_rescale {y Z : FieldSample} (hZ : IsRegularSample Z) {Q b : ℝ} (hb : 0 < b)
    (hy : avgReg y = avgReg (rescale Z Q b)) {u : ℂ} (hu : u ∈ Hbar) {ρ : ℝ} (hρ : 0 < ρ) :
    evalReg y (foldedCircle u ρ) =
      evalReg Z (foldedCircle ((b : ℂ) * u) (b * ρ)) + Q * Real.log b := by
  obtain ⟨FZ, hFZ⟩ := hZ
  have hres := hFZ.congr_evalReg.rescale' Q hb
  have e : evalReg y (foldedCircle u ρ) = evalReg (rescale Z Q b) (foldedCircle u ρ) := by
    unfold evalReg; rw [hy]
  rw [e, hres.evalReg_fc_of_mem hu hρ]

/-- **The identity at `ρ = 0`.** -/
theorem evalReg_sidePush_rescale {y : FieldSample} (hZ : IsRegularSample Z) {Q b : ℝ}
    (hb : 0 < b) (hy : avgReg y = avgReg (rescale Z Q b)) (hGV : G1zDrvGood V)
    (hGW : G1zDrvGood fun r => V (b ^ 2 * r) / b) {left : Bool} {μ : ℝ} (hμ : 0 < μ)
    (hψ : ∀ w ∈ H, g1zSideMap left (fun r => V (b ^ 2 * r) / b) w =
      ((b⁻¹ : ℝ) : ℂ) * g1zSideMap left V (((μ : ℂ))⁻¹ * w)) (d : ℂ) {s : ℝ} (hs : 0 < s)
    (hC : ContData y ((foldedCircle d s).map (g1zSideMap left fun r => V (b ^ 2 * r) / b))) :
    evalReg y ((foldedCircle d s).map (g1zSideMap left fun r => V (b ^ 2 * r) / b)) =
      evalReg Z ((foldedCircle (((μ⁻¹ : ℝ) : ℂ) * d) (μ⁻¹ * s)).map (g1zSideMap left V)) +
        Q * Real.log b := by
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  set W : ℝ → ℝ := fun r => V (b ^ 2 * r) / b with hWdef
  set ν := (foldedCircle d s).map (g1zSideMap left W) with hν
  have hψm := measurable_g1zSideMap hGW left
  have hνP : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hψm.aemeasurable).2 inferInstance
  have hνH : ∀ᵐ u ∂ν, u ∈ Hbar := by
    refine (ae_map_iff hψm.aemeasurable isClosed_Hbar.measurableSet).2
      ((TwoPoint.foldedCircle_ae_mem_H d hs).mono fun w hw => ?_)
    rw [hψ w hw]
    have h1 : g1zSideMap left V (((μ : ℂ))⁻¹ * w) ∈ H := by
      have hw' : ((μ : ℂ))⁻¹ * w ∈ H := by
        show 0 < (((μ : ℂ))⁻¹ * w).im
        rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]
        exact mul_pos (inv_pos.2 hμ) hw
      exact (sideMap_mem_compl_fwdHull hGV le_rfl left hw').1
    show 0 ≤ (((b⁻¹ : ℝ) : ℂ) * g1zSideMap left V (((μ : ℂ))⁻¹ * w)).im
    rw [Complex.im_ofReal_mul]
    exact mul_nonneg (inv_pos.2 hb).le (le_of_lt h1)
  have hsc := sidePush_scale hGV hb hGW hμ hψ d hs
  -- `ContData` for `Z` by dilating back
  have hCZ : ContData Z (ν.map fun z => (b : ℂ) * z) := by
    have hbi : 0 < b⁻¹ := inv_pos.2 hb
    refine contData_of_dilate (x := Z) (Z := y) hbi (C := -(Q * Real.log b)) ?_ ?_ ?_
    · exact (ae_map_iff (measurable_const_mul _).aemeasurable isClosed_Hbar.measurableSet).2
        (hνH.mono fun u hu => by
          show 0 ≤ ((b : ℂ) * u).im
          rw [Complex.im_ofReal_mul]; exact mul_nonneg hb.le hu)
    · intro u hu ρ hρ
      have hu' : ((b⁻¹ : ℝ) : ℂ) * u ∈ Hbar := by
        show 0 ≤ (((b⁻¹ : ℝ) : ℂ) * u).im
        rw [Complex.im_ofReal_mul]; exact mul_nonneg hbi.le hu
      rw [evalReg_fc_rescale hZ hb hy hu' (mul_pos hbi hρ)]
      have e1 : (b : ℂ) * (((b⁻¹ : ℝ) : ℂ) * u) = u := by
        push_cast; field_simp
      have e2 : b * (b⁻¹ * ρ) = ρ := by field_simp
      rw [e1, e2]; ring
    · rw [Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
      have e : ((fun z : ℂ => ((b⁻¹ : ℝ) : ℂ) * z) ∘ fun z : ℂ => (b : ℂ) * z) = id := by
        funext z; simp only [Function.comp_apply, id]; push_cast; field_simp
      rw [e, Measure.map_id]
      exact hC
  have h := evalReg_eq_of_contData_rescale hZ hb hy hνH hCZ
  rw [h, hsc]

end A1RS
end R18
end QuantumZipper
