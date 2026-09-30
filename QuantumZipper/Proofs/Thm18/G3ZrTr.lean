import QuantumZipper.Proofs.Thm18.G3ZrWire
import QuantumZipper.Proofs.Thm18.G1Z2MeasScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-REG (6): area-only choice regularity at a boundary point, from the side field

For a regular field `y`, a measurable map `Ψ : ℍ → ℍ` whose side field `Z = y ∘ Ψ + Q log|Ψ'|`
satisfies `G1.ChoiceRegularCore` (regular, RC3, continuum limits at dilated test measures) and has
an area limit `μ` that is finite near every real point and infinite in total, and for which `y` has
continuum limits along all pushed circles `Ψ_* fc`, the translated field `y(x + ·) + C` pulled back
by the local map `g = Ψ(· + β) − x` satisfies `G1.ChoiceRegularA` (`choiceRegularA_translate`),
for **every** `x`, `β`, `C`.

Proof: `V = coordChange (addConst (translate y x) C) g Q` has the same raw folded-circle values as
`W = addConst (translate Z β) C` (`raw_eq_translate_side`; the composition rule of `coordChange`
for a translation, as in `G1ZZ1.regEq_side_translate_zoom`, and `F2.coordChange_addConst_fc` with
the `RegShift` of `G3ZrShift`). Regularity, RC3 and the area limit pass from `Z` to `W` by
translation and constants (`IsRegularWith.translate'`, `hasAreaLimit_translate`,
`hasAreaLimit_add_ofFun`); positivity of the scale parameter from the local finiteness at the real
point `β` and the infinite total mass (`g1z2_translate_mass`, `g1z2_scaleParam_pos`); scale
consistency from the continuum limits of `Z` at translated test functions
(`g1za1b_scaleConsistent_of_core`; test functions are closed under real translations and
Lebesgue measure is translation invariant).

Sheffield, arXiv:1012.4797, pp. 69–71 (zoom at a boundary point through the local map). Own
bookkeeping (as `shiftRegA_of_det`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zr

open G3Z2b2 RegClosure

/-- The composition rule of `coordChange` for a real translation, at one folded circle. -/
theorem coordChange_translate_shift_fc {y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hy : IsRegularWith y F) (Q : ℝ) {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψH : MapsTo ψ H H)
    (b x : ℝ) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    coordChange (translate y (x : ℂ)) (fun w => ψ (w + (b : ℂ)) - (x : ℂ)) Q
      (foldedCircle d r) = coordChange y ψ Q (foldedCircle (d + b) r) := by
  have hT := hy.translate' x
  unfold coordChange
  have hderiv : ∀ z : ℂ, deriv (fun w : ℂ => ψ (w + (b : ℂ)) - (x : ℂ)) z =
      deriv ψ (z + (b : ℂ)) := fun z => by
    rw [deriv_sub_const]; exact deriv_comp_add_const _ _ _
  have h2 : ∫ z, Real.log ‖deriv (fun w : ℂ => ψ (w + (b : ℂ)) - (x : ℂ)) z‖ ∂foldedCircle d r =
      ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle (d + b) r := by
    simp_rw [hderiv]
    exact G1ZZ1.integral_fc_add_real (fun u => Real.log ‖deriv ψ u‖) d r b
  have h1 : evalReg (translate y (x : ℂ))
      ((foldedCircle d r).map fun w : ℂ => ψ (w + (b : ℂ)) - (x : ℂ)) =
      evalReg y ((foldedCircle (d + b) r).map ψ) := by
    unfold evalReg
    congr 1
    funext k
    rw [integral_map (G1ZZ1.measurable_shift_map hψm b x).aemeasurable
        (measurable_avgReg_slice _ k).aestronglyMeasurable,
      integral_map hψm.aemeasurable (measurable_avgReg_slice _ k).aestronglyMeasurable]
    have e1 : ∫ w, avgReg (translate y (x : ℂ)) k (ψ (w + (b : ℂ)) - (x : ℂ)) ∂foldedCircle d r =
        ∫ w, F (ψ (w + (b : ℂ)), radius k) ∂foldedCircle d r := by
      refine integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => ?_)
      show avgReg (translate y (x : ℂ)) k (ψ (w + (b : ℂ)) - (x : ℂ)) = _
      rw [hT.avgReg_eq k (shift_mem_Hbar hψH hw b x)]
      simp
    have e2 : ∫ u, avgReg y k (ψ u) ∂foldedCircle (d + b) r =
        ∫ u, F (ψ u, radius k) ∂foldedCircle (d + b) r := by
      refine integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H (d + b) hr).mono fun u hu => ?_)
      exact hy.avgReg_eq k (show 0 ≤ (ψ u).im from le_of_lt (hψH hu))
    rw [e1, e2]
    exact G1ZZ1.integral_fc_add_real (fun u => F (ψ u, radius k)) d r b
  rw [h1, h2]

/-- **Raw folded-circle values of the pulled-back translated field.** -/
theorem raw_eq_translate_side {γ : ℝ} {y : FieldSample} (hy : IsRegularSample y) {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) (hψH : MapsTo ψ H H)
    (hex : ∀ d ∈ Hbar, ∀ r > 0, evalReg (coordChange y ψ (Qc γ)) (foldedCircle d r) =
      coordChange y ψ (Qc γ) (foldedCircle d r))
    (hN : ∀ (d : ℂ) (r : ℝ), 0 < r → F1.ContData y ((foldedCircle d r).map ψ))
    (b x C : ℝ) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    coordChange (addConst (translate y (x : ℂ)) C) (fun w => ψ (w + (b : ℂ)) - (x : ℂ)) (Qc γ)
        (foldedCircle d r) =
      addConst (translate (coordChange y ψ (Qc γ)) (b : ℂ)) C (foldedCircle d r) := by
  obtain ⟨F, hF⟩ := hy
  rw [← WedgeTK.fc_foldH_eq d r]
  have hd : foldH d ∈ Hbar := CircleFubini.foldH_mem_Hbar' d
  have hRS := regShift_translate_shift ⟨F, hF⟩ hψm hψH b x (foldH d) hr (hN _ r hr)
  rw [F2.coordChange_addConst_fc C hRS, coordChange_translate_shift_fc hF (Qc γ) hψm hψH b x _ hr]
  have hdb : foldH d + (b : ℂ) ∈ Hbar := mapsTo_add_real b hd
  simp only [addConst, measure_univ, ENNReal.toReal_one, mul_one]
  unfold translate
  rw [IndepParams.fc_map_add_real, hex _ hdb r hr]

end G3Zr
end Thm18Asm
end QuantumZipper
