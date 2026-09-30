import QuantumZipper.Proofs.Thm18.G1ZSplitDefs
import QuantumZipper.Proofs.LQG.IndepParams

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-Z1 (1): the field identity of the change of variables (Theorem 1.8, G1 zoom)

Deterministic half of `G1PalmToWedgeStmt` (handoff/G1-ZSPLIT.md item 7). For a regular wedge
sample `Y`, a measurable map `ψ` of `ℍ` into itself such that the side field `Z = Y ∘ ψ + Q log|ψ'|`
has folded-circle values equal to its regularized ones (RC3 of `G1.ChoiceRegularCore`), and real
`b`, `x`:

  `translate Z b + C  ≈  (translate Y x)(ψ(· + b) − x) + Q log|ψ'(· + b)| + C`   up to `RegEq`.

Both sides have raw value `coordChange Y ψ Q (fc (d + b) r) + C` on the folded circle `fc d r`
(a real translation of the circle, `IndepParams.fc_map_add_real`, and `avgReg` of `translate`
computed through the regularity witness). This is the "composition rule of `coordChange` for a
translation" of Sheffield, arXiv:1012.4797, pp. 69–71 (`h ∘ ψ`, restricted near `ψ⁻¹(x)`, is
`h(x + ·)` composed with the local map); own elementary proof.

Main results: `G1ZZ1.integral_fc_add_real`, `G1ZZ1.regEq_side_translate_zoom`,
`G1ZZ1.regEq_side_zoomVia`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZZ1

open RegClosure

/-- Real translation of a folded circle, at the level of integrals of arbitrary functions. -/
theorem integral_fc_add_real (f : ℂ → ℝ) (d : ℂ) (r b : ℝ) :
    ∫ u, f (u + (b : ℂ)) ∂foldedCircle d r = ∫ u, f u ∂foldedCircle (d + b) r := by
  have e := (Homeomorph.addRight (b : ℂ)).measurableEmbedding.integral_map
    (μ := foldedCircle d r) f
  have hm : Measure.map (Homeomorph.addRight (b : ℂ)) (foldedCircle d r) =
      foldedCircle (d + b) r := IndepParams.fc_map_add_real d r b
  rw [hm] at e
  exact e.symm

theorem measurable_shift_map {ψ : ℂ → ℂ} (hψm : Measurable ψ) (b x : ℝ) :
    Measurable (fun w : ℂ => ψ (w + (b : ℂ)) - (x : ℂ)) :=
  (hψm.comp (measurable_id.add_const _)).sub_const _

theorem regEq_side_translate_zoom {Y : FieldSample} {F : ℂ × ℝ → ℝ} (hY : IsRegularWith Y F)
    (Q : ℝ) {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψH : MapsTo ψ H H)
    (hexact : ∀ d ∈ Hbar, ∀ r > 0, evalReg (coordChange Y ψ Q) (foldedCircle d r) =
      coordChange Y ψ Q (foldedCircle d r)) (b x C : ℝ) :
    RegEq (addConst (translate (coordChange Y ψ Q) (b : ℂ)) C)
      (addConst (coordChange (translate Y (x : ℂ)) (fun w => ψ (w + (b : ℂ)) - (x : ℂ)) Q) C) := by
  refine S5.FieldShift.regEq_of_fc fun d hd r hr => ?_
  have hd' : d + (b : ℂ) ∈ Hbar := mapsTo_add_real b hd
  have hu : ((foldedCircle d r) Set.univ).toReal = 1 := by simp
  have hL : translate (coordChange Y ψ Q) (b : ℂ) (foldedCircle d r) =
      coordChange Y ψ Q (foldedCircle (d + b) r) := by
    unfold translate
    rw [IndepParams.fc_map_add_real, hexact _ hd' r hr]
  have hT := hY.translate' x
  have hmH : ∀ w : ℂ, w ∈ H → ψ (w + (b : ℂ)) ∈ H := fun w hw =>
    hψH (show 0 < (w + (b : ℂ)).im by have : 0 < w.im := hw; simpa using this)
  have hR : coordChange (translate Y (x : ℂ)) (fun w => ψ (w + (b : ℂ)) - (x : ℂ)) Q
      (foldedCircle d r) = coordChange Y ψ Q (foldedCircle (d + b) r) := by
    unfold coordChange
    have hderiv : ∀ z : ℂ, deriv (fun w : ℂ => ψ (w + (b : ℂ)) - (x : ℂ)) z =
        deriv ψ (z + (b : ℂ)) := fun z => by
      rw [deriv_sub_const]; exact deriv_comp_add_const _ _ _
    have h2 : ∫ z, Real.log ‖deriv (fun w : ℂ => ψ (w + (b : ℂ)) - (x : ℂ)) z‖ ∂foldedCircle d r =
        ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle (d + b) r := by
      simp_rw [hderiv]
      exact integral_fc_add_real (fun u => Real.log ‖deriv ψ u‖) d r b
    have h1 : evalReg (translate Y (x : ℂ))
        ((foldedCircle d r).map fun w : ℂ => ψ (w + (b : ℂ)) - (x : ℂ)) =
        evalReg Y ((foldedCircle (d + b) r).map ψ) := by
      unfold evalReg
      congr 1
      funext k
      rw [integral_map (measurable_shift_map hψm b x).aemeasurable
          (measurable_avgReg_slice _ k).aestronglyMeasurable,
        integral_map hψm.aemeasurable (measurable_avgReg_slice _ k).aestronglyMeasurable]
      have e1 : ∫ w, avgReg (translate Y (x : ℂ)) k (ψ (w + (b : ℂ)) - (x : ℂ)) ∂foldedCircle d r =
          ∫ w, F (ψ (w + (b : ℂ)), radius k) ∂foldedCircle d r := by
        refine integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => ?_)
        have hmem : ψ (w + (b : ℂ)) - (x : ℂ) ∈ Hbar := by
          have := hmH w hw
          show 0 ≤ (ψ (w + (b : ℂ)) - (x : ℂ)).im
          simpa using this.le
        show avgReg (translate Y (x : ℂ)) k (ψ (w + (b : ℂ)) - (x : ℂ)) = _
        rw [hT.avgReg_eq k hmem]
        simp
      have e2 : ∫ u, avgReg Y k (ψ u) ∂foldedCircle (d + b) r =
          ∫ u, F (ψ u, radius k) ∂foldedCircle (d + b) r := by
        refine integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H (d + b) hr).mono fun u hu => ?_)
        exact hY.avgReg_eq k (show 0 ≤ (ψ u).im from le_of_lt (hψH hu))
      rw [e1, e2]
      exact integral_fc_add_real (fun u => F (ψ u, radius k)) d r b
    rw [h1, h2]
  simp only [addConst, hu, hL, hR]

/-- **The field identity of Z1**: `translate Z b + C` is `RegEq` to the zoom of `Y` at `x` through
the local map `w ↦ ψ(w + b) − x` at level `γ C` (for `γ ≠ 0`). -/
theorem regEq_side_zoomVia {γ : ℝ} (hγ : γ ≠ 0) {Y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hY : IsRegularWith Y F) {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψH : MapsTo ψ H H)
    (hexact : ∀ d ∈ Hbar, ∀ r > 0, evalReg (coordChange Y ψ (Qc γ)) (foldedCircle d r) =
      coordChange Y ψ (Qc γ) (foldedCircle d r)) (b x C : ℝ) :
    RegEq (addConst (translate (coordChange Y ψ (Qc γ)) (b : ℂ)) C)
      (zoomFieldVia γ (γ * C) Y x (fun w => ψ (w + (b : ℂ)) - (x : ℂ))) := by
  have e : γ * C / γ = C := by field_simp
  unfold zoomFieldVia
  rw [e]
  exact regEq_side_translate_zoom hY (Qc γ) hψm hψH hexact b x C

end G1ZZ1
end Thm18Asm
end QuantumZipper
