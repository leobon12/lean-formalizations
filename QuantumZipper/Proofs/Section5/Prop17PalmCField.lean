import QuantumZipper.Proofs.Section5.Prop17PalmCMain
import QuantumZipper.Proofs.Zipper.E5Model2
import QuantumZipper.Proofs.GFF.CoordRegLog

/-!
# Proposition 1.7, Palm-zoom node C: the deterministic field identity (PALM-C)

For `ϖ = foldedCircle 0 3`, `s = shiftFun γ 0 ϖ x` and a folded circle `ν` (radius `> 0`):
if the Palm-shifted field `h = N_ϖ(s + X ω)` is *regular* at the translated circle `ν(· − x)`
(`evalReg h (ν(· − x)) = h (ν(· − x))`), then the zoomed field `zoomField γ C h x` and the D3⁺
model field `zoomModel γ γ C (palmCRho ϖ x) (palmCField X x ω) (palmCCorr γ ϖ x)` take the same
value at `ν` (`zoomField_palm_eq_zoomModel`), and so does the split field
`(X' + γ(−log‖·‖)) + (g + const)` used for goodness (`zoomField_palm_eq_split`).

Ingredients: the closed form `kPot ϖ u = −2 (log 3 + log⁺(‖u‖/3))` (Jensen's formula, mathlib
`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`), hence `g` is continuous; the
pointwise identity `s(z + x) = γ(−log‖z‖) + g z + ∫ s dϖ` (since `neumannH x (z + x) =
−2 log‖z‖` for real `x`); integrability of `log‖·‖` on folded circles
(`CoordReg.integrable_log_norm_foldedCircle`). Own elementary computation (AGENT_GUIDE cost
rule), the computation behind Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull TV PalmShift FieldShift PalmNorm

/-- Closed form of the potential of the folded circle of radius `3`. -/
theorem kPot_foldedCircle_three_eq (u : ℂ) :
    kPot (foldedCircle 0 3) u = -2 * (Real.log 3 + Real.posLog (3⁻¹ * ‖u‖)) := by
  unfold kPot foldedCircle
  rw [integral_map measurable_foldH.aemeasurable
    (palmC_measurable_neumannH u).aestronglyMeasurable]
  simp_rw [palmC_neumannH_foldH]
  rw [CoordReg.integral_circleUnif_eq_circleAverage (palmC_measurable_neumannH u)]
  have e : neumannH u = fun w => (-1 : ℝ) • (Real.log ‖w - u‖ + Real.log ‖w - conj u‖) := by
    funext w
    simp only [neumannH]
    rw [norm_sub_rev u w, show u - conj w = conj (conj u - w) by simp, Complex.norm_conj,
      norm_sub_rev (conj u) w, smul_eq_mul]
    ring
  have hav : ∀ a : ℂ, Real.circleAverage (fun w => Real.log ‖w - a‖) 0 3 =
      Real.log 3 + Real.posLog (3⁻¹ * ‖a‖) := by
    intro a
    rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (by norm_num), zero_sub,
      norm_neg]
  rw [e, Real.circleAverage_fun_smul, Real.circleAverage_fun_add
    (circleIntegrable_log_norm_sub_const _) (circleIntegrable_log_norm_sub_const _), hav, hav,
    Complex.norm_conj, smul_eq_mul]
  ring

theorem continuous_palmCCorr (γ x : ℝ) : Continuous (palmCCorr γ (foldedCircle 0 3) x) := by
  have e : palmCCorr γ (foldedCircle 0 3) x = fun z => -(γ / 2) *
      (-2 * (Real.log 3 + Real.posLog (3⁻¹ * ‖z + (x : ℂ)‖))) -
        ∫ u, shiftFun γ (0 : ℂ → ℝ) (foldedCircle 0 3) x u ∂(foldedCircle 0 3) := by
    funext z; rw [palmCCorr, kPot_foldedCircle_three_eq]
  rw [e]
  fun_prop

/-- The pointwise identity `s(z + x) = γ(−log‖z‖) + g z + ∫ s dϖ`. -/
theorem shiftFun_add_eq (γ : ℝ) (ϖ : Measure ℂ) (x : ℝ) (z : ℂ) :
    shiftFun γ (0 : ℂ → ℝ) ϖ x (z + x) =
      γ * -Real.log ‖z‖ + palmCCorr γ ϖ x z + ∫ u, shiftFun γ (0 : ℂ → ℝ) ϖ x u ∂ϖ := by
  have h1 : (x : ℂ) - (z + x) = -z := by ring
  have h2 : (x : ℂ) - conj (z + (x : ℂ)) = -conj z := by
    rw [map_add, Complex.conj_ofReal]; ring
  simp only [shiftFun, palmCCorr, neumannH, Pi.zero_apply, h1, h2, norm_neg, Complex.norm_conj]
  ring

theorem integral_map_add_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Measure ℂ) (t : ℝ) (f : ℂ → E) :
    ∫ u, f u ∂(ν.map (· + (t : ℂ))) = ∫ z, f (z + t) ∂ν := by
  have e : (fun z : ℂ => z + (t : ℂ)) = ⇑(Homeomorph.addRight (t : ℂ)).toMeasurableEquiv := rfl
  rw [e, integral_map_equiv]
  rfl

theorem palmCField_rho (X : Ω → FieldSample) (ϖ : Measure ℂ) (x : ℝ) (ω : Ω) :
    palmCField X x ω (palmCRho ϖ x) = X ω ϖ := by
  simp only [palmCField, palmCRho]
  rw [Measure.map_map (measurable_add_const _) (measurable_add_const _)]
  congr 1
  convert Measure.map_id (μ := ϖ)
  funext z
  simp

variable {Ω : Type*}

/-- Integrability of the model integrand on a folded circle of positive radius. -/
theorem integrable_palmC_parts (γ x : ℝ) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun z => γ * -Real.log ‖z‖) (foldedCircle c ρ) ∧
      Integrable (palmCCorr γ (foldedCircle 0 3) x) (foldedCircle c ρ) :=
  ⟨(CoordReg.integrable_log_norm_foldedCircle c ρ).neg.const_mul γ,
    E5.integrable_foldedCircle_of_continuousOn (continuous_palmCCorr γ x).continuousOn c ρ hρ
      (lt_add_one _)⟩

/-- Value of the zoomed Palm field at a folded circle where the Palm field is regular. -/
theorem zoomField_palm_apply {γ C x : ℝ} {X : Ω → FieldSample} {ω : Ω} {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hreg : evalReg (palmFreeField γ (foldedCircle 0 3) X x ω)
      ((foldedCircle c ρ).map (· + (x : ℂ))) =
        palmFreeField γ (foldedCircle 0 3) X x ω ((foldedCircle c ρ).map (· + (x : ℂ)))) :
    zoomField γ C (palmFreeField γ (foldedCircle 0 3) X x ω) x (foldedCircle c ρ) =
      palmCField X x ω (foldedCircle c ρ) +
        ((∫ z, γ * -Real.log ‖z‖ ∂(foldedCircle c ρ)) +
          ∫ z, palmCCorr γ (foldedCircle 0 3) x z ∂(foldedCircle c ρ)) + C / γ -
        X ω (foldedCircle 0 3) := by
  obtain ⟨h1, h2⟩ := integrable_palmC_parts γ x c hρ
  have h12 : Integrable (fun z => γ * -Real.log ‖z‖ + palmCCorr γ (foldedCircle 0 3) x z)
      (foldedCircle c ρ) := h1.add h2
  have hmass : ((foldedCircle c ρ).map (· + (x : ℂ)) univ).toReal = 1 := by
    rw [map_add_real_univ, measure_univ, ENNReal.toReal_one]
  have hs : ∫ u, shiftFun γ (0 : ℂ → ℝ) (foldedCircle 0 3) x u
      ∂((foldedCircle c ρ).map (· + (x : ℂ))) =
      (∫ z, γ * -Real.log ‖z‖ ∂(foldedCircle c ρ)) +
        (∫ z, palmCCorr γ (foldedCircle 0 3) x z ∂(foldedCircle c ρ)) +
        ∫ u, shiftFun γ (0 : ℂ → ℝ) (foldedCircle 0 3) x u ∂(foldedCircle 0 3) := by
    rw [integral_map_add_real]
    simp_rw [shiftFun_add_eq]
    rw [integral_add h12 (integrable_const _), integral_add h1 h2, integral_const,
      Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  simp only [zoomField, addConst, translate]
  rw [hreg, measure_univ, ENNReal.toReal_one]
  simp only [palmFreeField, normAt, addConst, Pi.add_apply, ofFun, hmass, palmCField]
  rw [hs]
  ring

/-- **Field identity (model).** -/
theorem zoomField_palm_eq_zoomModel {γ C x : ℝ} {X : Ω → FieldSample} {ω : Ω} {c : ℂ}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hreg : evalReg (palmFreeField γ (foldedCircle 0 3) X x ω)
      ((foldedCircle c ρ).map (· + (x : ℂ))) =
        palmFreeField γ (foldedCircle 0 3) X x ω ((foldedCircle c ρ).map (· + (x : ℂ)))) :
    zoomField γ C (palmFreeField γ (foldedCircle 0 3) X x ω) x (foldedCircle c ρ) =
      D3Plus.zoomModel γ γ C (palmCRho (foldedCircle 0 3) x) (palmCField X x ω)
        (palmCCorr γ (foldedCircle 0 3) x) (foldedCircle c ρ) := by
  obtain ⟨h1, h2⟩ := integrable_palmC_parts γ x c hρ
  have h12 : Integrable (fun z => γ * -Real.log ‖z‖ + palmCCorr γ (foldedCircle 0 3) x z)
      (foldedCircle c ρ) := h1.add h2
  rw [zoomField_palm_apply hρ hreg]
  simp only [D3Plus.zoomModel, Pi.add_apply, ofFun, palmCField_rho]
  rw [integral_add h12 (integrable_const _), integral_add h1 h2, integral_const,
    Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  ring

/-- The split field `(X' + γ(−log‖·‖)) + (g + (C/γ − X' ρ₀))` (for goodness). -/
def palmCSplit (γ C x : ℝ) (X : Ω → FieldSample) (ω : Ω) : FieldSample :=
  (palmCField X x ω + ofFun fun z => γ * -Real.log ‖z‖) +
    ofFun fun z => palmCCorr γ (foldedCircle 0 3) x z + (C / γ - X ω (foldedCircle 0 3))

/-- **Field identity (split field).** -/
theorem zoomField_palm_eq_split {γ C x : ℝ} {X : Ω → FieldSample} {ω : Ω} {c : ℂ}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hreg : evalReg (palmFreeField γ (foldedCircle 0 3) X x ω)
      ((foldedCircle c ρ).map (· + (x : ℂ))) =
        palmFreeField γ (foldedCircle 0 3) X x ω ((foldedCircle c ρ).map (· + (x : ℂ)))) :
    zoomField γ C (palmFreeField γ (foldedCircle 0 3) X x ω) x (foldedCircle c ρ) =
      palmCSplit γ C x X ω (foldedCircle c ρ) := by
  obtain ⟨-, h2⟩ := integrable_palmC_parts γ x c hρ
  rw [zoomField_palm_apply hρ hreg]
  simp only [palmCSplit, Pi.add_apply, ofFun]
  rw [integral_add h2 (integrable_const _), integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul]
  ring

/-- Agreement at all dyadic folded circles gives equal area approximations. -/
theorem areaApprox_eq_of_agree {γ : ℝ} {y y' : FieldSample}
    (h : ∀ (n k : ℕ) (z : ℂ), y (foldedCircle (dyadicRoundC n z) (radius k)) =
      y' (foldedCircle (dyadicRoundC n z) (radius k))) :
    areaApprox γ y = areaApprox γ y' := by
  have hag : ∀ r : ℝ, D3Plus.AgreeNear y y' r := fun r n k z _ => h n k z
  funext k
  unfold areaApprox
  congr 1
  funext z
  rw [D3Plus.avgReg_congr (hag (‖z‖ + radius k + 1)) (lt_add_one _)]

end Raw
end FieldLaw
end S5
end QuantumZipper
