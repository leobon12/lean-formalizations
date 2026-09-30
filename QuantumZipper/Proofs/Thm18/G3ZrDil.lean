import QuantumZipper.Proofs.Thm18.G3ZrShift
import QuantumZipper.Proofs.Thm18.G1A1bCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-REG (2): `DilRegCore` for the curve maps from the continuum limit at the dilated side map

`G3Z2b2.DilRegCore γ y b x f σ` consists of three "regularized evaluation = raw evaluation"
identities at pushed folded circles `σ.map f`, for the curve map `f = ψ(· + B) − x/b`:

1. for the real translate of the regular field `rescale y Q b`: deterministic
   (`evalReg_translate_eq`: `avgReg` of a real translate is the translated `avgReg`, on `ℍ̄`);
2. for `rescale y Q b` itself: from the continuum limit `F1.ContData y` at the pushed measure
   dilated by `b`, i.e. at `(fc(d + B, r)).map (b ψ)` (`evalReg_rescale_eq_of_contData`, from
   `G1A1b.evalReg_rescale_eq_of_tendsto`);
3. for the real translate of `y`: deterministic again.

`dilRegCore_of_contData`: all three at every `x`, `d`, `k`, given the continuum limit of `y` along
every pushed circle of `b ψ`. `contData_dilate_of_rescale`: that continuum limit follows from the
continuum limit of the rescaled field `rescale y Q b` along the pushed circles of `ψ` (the
canonical wedge, where `G1SidePushUCRepStmt` supplies it).

Sheffield, arXiv:1012.4797, p. 70 (the curve is independent of the field; regularity at a fixed
map). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zr

open G3Z2b2

/-- **Real translates are exact at measures carried by `ℍ̄`.** -/
theorem evalReg_translate_eq {z : FieldSample} (hz : IsRegularSample z) (t : ℝ)
    {m : Measure ℂ} (hm : ∀ᵐ u ∂m, u ∈ Hbar) :
    evalReg (translate z (t : ℂ)) m = translate z (t : ℂ) m := by
  obtain ⟨F, hF⟩ := hz
  have hT := hF.translate' t
  show evalReg (translate z (t : ℂ)) m = evalReg z (m.map fun u => u + (t : ℂ))
  unfold evalReg
  congr 1
  funext k
  rw [integral_map (show Measurable fun u : ℂ => u + (t : ℂ) from measurable_id.add_const _).aemeasurable
    (RegClosure.measurable_avgReg_slice z k).aestronglyMeasurable]
  refine integral_congr_ae (hm.mono fun u hu => ?_)
  exact (hT.avgReg_eq k hu).trans (hF.avgReg_eq k (RegClosure.mapsTo_add_real t hu)).symm

/-- **The dilated field is exact at a measure where the field has a continuum limit after the
dilation.** -/
theorem evalReg_rescale_eq_of_contData {y : FieldSample} (hy : IsRegularSample y) (Q : ℝ)
    {b : ℝ} (hb : 0 < b) {m : Measure ℂ} [IsProbabilityMeasure m] (hm : ∀ᵐ u ∂m, u ∈ Hbar)
    (hc : F1.ContData y (m.map fun u => (b : ℂ) * u)) :
    evalReg (rescale y Q b) m = rescale y Q b m := by
  obtain ⟨F, hF⟩ := hy
  have hF' := hF.congr_evalReg
  obtain ⟨hint, L, hL⟩ := hc
  have hmb : Measurable fun u : ℂ => (b : ℂ) * u := measurable_const_mul _
  have hmH : ∀ᵐ v ∂(m.map fun u => (b : ℂ) * u), v ∈ Hbar :=
    (ae_map_iff hmb.aemeasurable R18.G1A1b.measurableSet_Hbar').2
      (hm.mono fun u hu => RegClosure.mapsTo_mul_pos hb hu)
  rw [R18.G1A1b.evalReg_rescale_eq_of_tendsto hF' Q hb hm hint hL]
  show _ = evalReg y (m.map fun u => (b : ℂ) * u) +
    Q * ∫ z, Real.log ‖deriv (fun z : ℂ => (b : ℂ) * z) z‖ ∂m
  rw [RegClosure.integral_log_deriv_mul hb m, R18.G1A1b.evalReg_eq_of_tendsto_radius hF' hmH hL]

theorem ae_map_mem_Hbar {m : Measure ℂ} {g : ℂ → ℂ} (hg : Measurable g)
    (h : ∀ᵐ w ∂m, g w ∈ Hbar) : ∀ᵐ u ∂(m.map g), u ∈ Hbar :=
  (ae_map_iff hg.aemeasurable R18.G1A1b.measurableSet_Hbar').2 h

/-- **`DilRegCore` for a shifted local map, from the continuum limit at the dilated map.** -/
theorem dilRegCore_of_contData (γ : ℝ) {y : FieldSample} (hy : IsRegularSample y) {b : ℝ}
    (hb : 0 < b) {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψH : MapsTo ψ H H)
    (hc : ∀ (d : ℂ) (r : ℝ), 0 < r →
      F1.ContData y ((foldedCircle d r).map fun w => (b : ℂ) * ψ w))
    (x B : ℝ) (d : ℂ) (k : ℕ) :
    DilRegCore γ y b x (fun w => ψ (w + (B : ℂ)) - ((x / b : ℝ) : ℂ))
      (foldedCircle d (radius k)) := by
  have hr := radius_pos k
  set f : ℂ → ℂ := fun w => ψ (w + (B : ℂ)) - ((x / b : ℝ) : ℂ) with hfdef
  have hfm : Measurable f := G1ZZ1.measurable_shift_map hψm B (x / b)
  have hfH : ∀ᵐ w ∂(foldedCircle d (radius k)), f w ∈ Hbar :=
    (TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => shift_mem_Hbar hψH hw B (x / b)
  have hm1 : ∀ᵐ u ∂((foldedCircle d (radius k)).map f), u ∈ Hbar := ae_map_mem_Hbar hfm hfH
  have hyR : IsRegularSample (rescale y (Qc γ) b) := by
    obtain ⟨F, hF⟩ := hy; exact ⟨_, hF.rescale' (Qc γ) hb⟩
  refine ⟨evalReg_translate_eq hyR (x / b) hm1, ?_, ?_⟩
  · -- the dilated field at the translated pushed circle
    have htm : Measurable fun u : ℂ => u + ((x / b : ℝ) : ℂ) := measurable_id.add_const _
    refine evalReg_rescale_eq_of_contData hy (Qc γ) hb
      (ae_map_mem_Hbar htm (hm1.mono fun u hu => RegClosure.mapsTo_add_real _ hu)) ?_
    have e : ((((foldedCircle d (radius k)).map f).map fun u => u + ((x / b : ℝ) : ℂ)).map
        fun u => (b : ℂ) * u) = (foldedCircle (d + B) (radius k)).map fun w => (b : ℂ) * ψ w := by
      rw [Measure.map_map (measurable_const_mul _) htm,
        Measure.map_map ((measurable_const_mul _).comp htm) hfm,
        ← IndepParams.fc_map_add_real d (radius k) B,
        Measure.map_map (hψm.const_mul (b : ℂ))
          (show Measurable fun u : ℂ => u + (B : ℂ) from measurable_id.add_const _)]
      congr 1
      funext w
      simp [hfdef]
    rw [e]
    exact hc _ _ hr
  · refine evalReg_translate_eq hy x (ae_map_mem_Hbar ((measurable_const_mul _).comp hfm) ?_)
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr] with w hw
    have h' : 0 < (ψ (w + (B : ℂ))).im := hψH (add_real_mem_H hw B)
    show 0 ≤ ((b : ℂ) * (ψ (w + (B : ℂ)) - ((x / b : ℝ) : ℂ))).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.sub_re, zero_mul, add_zero, sub_zero]
    exact mul_nonneg hb.le h'.le

end G3Zr
end Thm18Asm
end QuantumZipper
