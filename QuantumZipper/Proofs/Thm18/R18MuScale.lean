import QuantumZipper.Proofs.Thm18.R18MuBasic
import QuantumZipper.Proofs.Zipper.B3dDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8 (D76): Brownian scaling of the carried area, and the area part of `Z_{−ℓ} ∘ Z_ℓ`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, p. 26 (the rescaling (1.8)
and Brownian scaling of the driver); Lawler, *Conformally Invariant Processes in the Plane*,
Prop. 4.10 (scaling of the Loewner chain: driver `W(a² ·)/a` gives the maps `f_{a²t}(a ·)/a`),
formalized as `LoewnerAlgebra.mem_fwdHull_scale_iff` and `B3d.fwdMap_scale_of`.
Own elementary bookkeeping (the paper uses these identities implicitly).

* `zipCapDownA_canonAConfig_area`: unzipping the rescaled configuration by `T/b²` pushes the area
  as unzipping the original by `T`, followed by `z ↦ z/b` (`b = areaScale μ`);
* `zipLenDownA_zipLenUpA_area`: the carried area after `Z_{−ℓ} ∘ Z_ℓ` is the original one, given
  the unzipping time `T/b²` (as in `Thm18Asm.roundDown_tail_of_rezip`).
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- **Brownian scaling of the carried area under unzipping.** With `b = areaScale c.area > 0`,
unzipping `canonAConfig γ c` by capacity `T / b²` gives the area of unzipping `c` by `T`, pushed
forward by `z ↦ z / b`. -/
theorem zipCapDownA_canonAConfig_area {γ T : ℝ} (hT : 0 ≤ T) {c : AreaConfig}
    (hc : Continuous c.drv) (hb : 0 < areaScale c.area) :
    (zipCapDownA γ (T / areaScale c.area ^ 2) (canonAConfig γ c)).area =
      (zipCapDownA γ T c).area.map fun z => ((areaScale c.area : ℂ))⁻¹ * z := by
  set b := areaScale c.area with hbdef
  set D := (canonAConfig γ c).drv with hDdef
  set W₁ : ℝ → ℝ := fun r => c.drv (max r 0) with hW₁def
  have hW₁ : Continuous W₁ := hc.comp (continuous_id.max continuous_const)
  have hW₁eq : EqOn W₁ c.drv (Icc 0 T) := fun r hr => by simp only [hW₁def, max_eq_left hr.1]
  have hD : D = fun s => W₁ (b ^ 2 * s) / b := by
    funext s
    simp only [hDdef, canonAConfig, hW₁def, ← hbdef]
    rw [mul_max_of_nonneg _ _ (sq_nonneg b), mul_zero]
  have hDc : Continuous D := by
    rw [hD]; exact (hW₁.comp (continuous_const.mul continuous_id)).div_const b
  have hb2 : 0 < b ^ 2 := by positivity
  set t := T / b ^ 2 with htdef
  have ht : 0 ≤ t := div_nonneg hT hb2.le
  have hbt : b ^ 2 * t = T := by rw [htdef]; field_simp
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hFmap : ∀ z, fwdMap D t z = fwdMap c.drv T ((b : ℂ) * z) / b := by
    intro z
    rw [hD, B3d.fwdMap_scale_of W₁ hb ht z, hbt,
      CharFunRhs.fwdMap_eq_of_eqOn fun r hr => hW₁eq hr]
  have hHull : ∀ z, z ∈ fwdHull D t ↔ (b : ℂ) * z ∈ fwdHull c.drv T := by
    intro z
    rw [hD, LoewnerAlgebra.mem_fwdHull_scale_iff W₁ hb ht z, hbt,
      Thm14FromThm13.fwdHull_eq_of_eqOn hW₁ hc hT hW₁eq]
  set s : ℂ → ℂ := fun z => ((b : ℂ))⁻¹ * z with hsdef
  have hsm : Measurable s := measurable_id.const_mul _
  set U := H \ fwdHull c.drv T with hUdef
  set UD := H \ fwdHull D t with hUDdef
  have hU : MeasurableSet U := (FwdHolo.isOpen_compl_fwdHull hc hT).measurableSet
  have hUD : MeasurableSet UD := (FwdHolo.isOpen_compl_fwdHull hDc ht).measurableSet
  have hpre : s ⁻¹' UD = U := by
    ext z
    simp only [hsdef, hUDdef, hUdef, Set.mem_preimage, Set.mem_sdiff, hHull,
      mul_inv_cancel_left₀ hbC]
    refine and_congr ?_ Iff.rfl
    show 0 < (((b : ℂ))⁻¹ * z).im ↔ 0 < z.im
    rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]
    exact mul_pos_iff_of_pos_left (inv_pos.2 hb)
  have hG : AEMeasurable (fwdMap D t) ((c.area.map s).restrict UD) :=
    (FwdHolo.differentiableOn_fwdMap hDc ht).continuousOn.aemeasurable hUD
  rw [Measure.restrict_map hsm hUD, hpre] at hG
  have hF : AEMeasurable (fwdMap c.drv T) (c.area.restrict U) :=
    (FwdHolo.differentiableOn_fwdMap hc hT).continuousOn.aemeasurable hU
  show ((c.area.map s).restrict UD).map (fwdMap D t) =
    ((c.area.restrict U).map (fwdMap c.drv T)).map s
  rw [Measure.restrict_map hsm hUD, hpre, AEMeasurable.map_map_of_aemeasurable hG hsm.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable hsm.aemeasurable hF]
  congr 1
  funext z
  simp only [Function.comp_apply, hsdef, hFmap, mul_inv_cancel_left₀ hbC, div_eq_inv_mul]

/-- **Brownian scaling of the carried area under zipping up.** With `a = areaScale c.area > 0`,
zipping up `canonAConfig γ c` along a driver equal on `[0, t/a²]` to `u ↦ W(a² u)/a` gives the
area of zipping up `c` along `(t, W)`, pushed forward by `z ↦ z / a`. -/
theorem zipWeldUpA_canonAConfig_area {γ t : ℝ} (ht : 0 ≤ t) {W W₃ : ℝ → ℝ} (hW : Continuous W)
    {c : AreaConfig} (ha : 0 < areaScale c.area)
    (hW₃ : EqOn W₃ (fun u => W (areaScale c.area ^ 2 * u) / areaScale c.area)
      (Icc 0 (t / areaScale c.area ^ 2))) :
    (zipWeldUpA γ (t / areaScale c.area ^ 2) W₃ (canonAConfig γ c)).area =
      (zipWeldUpA γ t W c).area.map fun z => ((areaScale c.area : ℂ))⁻¹ * z := by
  set a := areaScale c.area with hadef
  have ha2 : 0 < a ^ 2 := by positivity
  have ht' : 0 ≤ t / a ^ 2 := div_nonneg ht ha2.le
  have hat : a ^ 2 * (t / a ^ 2) = t := by field_simp
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hWa : Continuous fun u => W (a ^ 2 * u) / a :=
    (hW.comp (continuous_const.mul continuous_id)).div_const a
  have hR3 : revMap W₃ (t / a ^ 2) = revMap (fun u => W (a ^ 2 * u) / a) (t / a ^ 2) :=
    revMap_congr_lenZip hW₃
  set s : ℂ → ℂ := fun z => ((a : ℂ))⁻¹ * z with hsdef
  have hsm : Measurable s := measurable_id.const_mul _
  have hpre : s ⁻¹' H = H := by
    ext z
    show 0 < (((a : ℂ))⁻¹ * z).im ↔ 0 < z.im
    rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]
    exact mul_pos_iff_of_pos_left (inv_pos.2 ha)
  have hG : AEMeasurable (revMap W₃ (t / a ^ 2)) ((c.area.map s).restrict H) := by
    rw [hR3]
    exact (differentiableOn_revMap _ hWa ht').continuousOn.aemeasurable measurableSet_H_mu
  rw [Measure.restrict_map hsm measurableSet_H_mu, hpre] at hG
  have hF : AEMeasurable (revMap W t) (c.area.restrict H) :=
    (differentiableOn_revMap W hW ht).continuousOn.aemeasurable measurableSet_H_mu
  show ((c.area.map s).restrict H).map (revMap W₃ (t / a ^ 2)) =
    ((c.area.restrict H).map (revMap W t)).map s
  rw [Measure.restrict_map hsm measurableSet_H_mu, hpre,
    AEMeasurable.map_map_of_aemeasurable hG hsm.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable hsm.aemeasurable hF]
  refine Measure.map_congr ((ae_restrict_mem measurableSet_H_mu).mono fun z hz => ?_)
  have hz' : 0 < (s z).im := by
    have h' : z ∈ s ⁻¹' H := by rw [hpre]; exact hz
    exact h'
  simp only [Function.comp_apply, hR3]
  rw [LoewnerAlgebra.revMap_scale W hW ha ht' hz', hat, hsdef]
  simp only [mul_inv_cancel_left₀ haC, div_eq_inv_mul]

end R18
end QuantumZipper
