import QuantumZipper.Proofs.Thm18.G3FidMass

/-!
# G2 (full field, mixing form): the Palm law as a Lebesgue mixture in the Palm length

The Palm law of the concrete G3 scheme is `g3PalmLaw = (P₀ ⊗ Exp 1).withDensity g3W`, with
`g3W = Z⁻¹ e^ℓ 1{0 < ℓ ≤ M(ω)}` and `M = g3Mass = (ν₁ + ν₀)[−δ, 0]`. The factor `e^ℓ` cancels the
density of `Exp 1`, so (for `0 < Z < ∞`)

  `P_Palm(S) = Z⁻¹ ∫ Leb{ℓ ∈ (0, M(ω)] : (ω, ℓ) ∈ S} dP₀(ω)`   (`g3PalmLaw_apply_eq_lebesgue`):

given the field, the Palm length `ℓ = ν_h[x, 0]` is uniform on `(0, ν_h[−δ, 0]]`, and the field
is size-biased by `ν_h[−δ, 0]`. This is the form of the rooted measure used in Sheffield's
proof of Proposition 5.5 (arXiv:1012.4797, p. 65–66: conditioning on the lengths
`L₁ = ν_h[a, x]` is a reweighting by the smooth density of the length), and the starting point
for the fixed-region mixing statement `G2FixMixStmt` (`G2FullMixGeo.lean`): events of
`outsideSigmaPalm` are events in `(outside field, ℓ)`, and `ℓ` has a Lebesgue density given the
field.

Own elementary computation (AGENT_GUIDE cost rule), as `lintegral_expMeasure_palmKernel`
(`G3FidMass.lean`) with an indicator.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- `∫⁻ 1_T(ℓ) e^ℓ 1{0 < ℓ ≤ M} dExp(1)(ℓ) = Leb(T ∩ (0, M])` for finite `M`. -/
theorem lintegral_expMeasure_palmKernel_indicator {T : Set ℝ} (hT : MeasurableSet T)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) :
    ∫⁻ ℓ : ℝ, T.indicator (fun ℓ => if 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ M then
      ENNReal.ofReal (Real.exp ℓ) else 0) ℓ ∂(expMeasure 1) = volume (T ∩ Ioc 0 M.toReal) := by
  have hg : Measurable fun ℓ : ℝ =>
      (if 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ M then ENNReal.ofReal (Real.exp ℓ) else 0) :=
    Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_id) measurable_const))
      (ENNReal.measurable_ofReal.comp Real.measurable_exp) measurable_const
  have hset : ∀ ℓ : ℝ, (0 < ℓ ∧ ENNReal.ofReal ℓ ≤ M) ↔ ℓ ∈ Ioc 0 M.toReal := by
    intro ℓ
    rw [Set.mem_Ioc]
    refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
    · refine (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 ?_
      simpa [ENNReal.ofReal_toReal hM] using h.2
    · exact (ENNReal.ofReal_le_ofReal h.2).trans_eq (ENNReal.ofReal_toReal hM)
  rw [show expMeasure 1 = volume.withDensity (gammaPDF 1 1) from rfl,
    lintegral_withDensity_eq_lintegral_mul (f := gammaPDF 1 1) volume
      (ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 1)) (hg.indicator hT)]
  have hpt : ∀ ℓ : ℝ, gammaPDF 1 1 ℓ * T.indicator (fun ℓ => if 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ M
      then ENNReal.ofReal (Real.exp ℓ) else 0) ℓ = (T ∩ Ioc 0 M.toReal).indicator 1 ℓ := by
    intro ℓ
    by_cases hℓT : ℓ ∈ T
    · rw [indicator_of_mem hℓT]
      by_cases h : 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ M
      · rw [if_pos h, indicator_of_mem (show ℓ ∈ T ∩ Ioc 0 M.toReal from ⟨hℓT, (hset ℓ).1 h⟩)]
        have hℓ : (0 : ℝ) ≤ ℓ := h.1.le
        have hpdf : gammaPDF 1 1 ℓ = ENNReal.ofReal (Real.exp (-ℓ)) := by
          have h1 : gammaPDFReal 1 1 ℓ = Real.exp (-ℓ) := by
            simp only [gammaPDFReal, hℓ, if_true, Real.one_rpow, Real.Gamma_one, div_one,
              sub_self, Real.rpow_zero, one_mul, mul_one]
          show ENNReal.ofReal (gammaPDFReal 1 1 ℓ) = ENNReal.ofReal (Real.exp (-ℓ))
          rw [h1]
        rw [hpdf, ← ENNReal.ofReal_mul (Real.exp_nonneg (-ℓ)), ← Real.exp_add, neg_add_cancel,
          Real.exp_zero, ENNReal.ofReal_one, Pi.one_apply]
      · rw [if_neg h, mul_zero, indicator_of_notMem fun hc => h ((hset ℓ).2 hc.2)]
    · rw [indicator_of_notMem hℓT, mul_zero, indicator_of_notMem fun hc => hℓT hc.1]
  simp only [Pi.mul_apply]
  rw [lintegral_congr hpt, lintegral_indicator_one (hT.inter measurableSet_Ioc)]

variable (γ : ℝ) (i : G3Idx)

/-- **The Palm law as a Lebesgue mixture in the Palm length.** For `0 < Z < ∞`,
`P_Palm(S) = Z⁻¹ ∫ Leb{ℓ ∈ (0, M(ω)] : (ω, ℓ) ∈ S} dP₀(ω)`, `M = g3Mass`. -/
theorem g3PalmLaw_apply_eq_lebesgue (hZ : 0 < g3Z γ i ∧ g3Z γ i < ⊤) {S : Set (Ω₀ × ℝ)}
    (hS : MeasurableSet S) :
    g3PalmLaw γ i S = (g3Z γ i)⁻¹ * ∫⁻ ω, volume ({ℓ | (ω, ℓ) ∈ S} ∩
      Ioc 0 (g3Mass γ i ω).toReal) ∂gffBase.P := by
  have hW0 : Measurable (g3W0 γ i) := (measurable_g3W0 γ i).mono (sig_le_g3 i _ _) le_rfl
  have hcoe : ∀ p, ((g3W γ i p : ℝ≥0) : ℝ≥0∞) = (g3Z γ i)⁻¹ * g3W0 γ i p := by
    intro p
    unfold g3W; rw [if_pos hZ]
    exact ENNReal.coe_toNNReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ.1.ne')
      (g3W0_ne_top γ i p))
  rw [g3PalmLaw, withDensity_apply _ hS, ← lintegral_indicator hS]
  have e1 : (S.indicator fun p => ((g3W γ i p : ℝ≥0) : ℝ≥0∞)) =
      fun p => (g3Z γ i)⁻¹ * S.indicator (g3W0 γ i) p := by
    funext p
    by_cases hp : p ∈ S
    · rw [indicator_of_mem hp, indicator_of_mem hp, hcoe]
    · rw [indicator_of_notMem hp, indicator_of_notMem hp, mul_zero]
  rw [e1, lintegral_const_mul _ (hW0.indicator hS), lintegral_prod _ (hW0.indicator hS).aemeasurable]
  congr 1
  refine lintegral_congr fun ω => ?_
  have hsec : MeasurableSet {ℓ : ℝ | (ω, ℓ) ∈ S} := measurable_prodMk_left hS
  rw [← lintegral_expMeasure_palmKernel_indicator hsec (g3Mass_lt_top γ i ω).ne]
  refine lintegral_congr fun ℓ => ?_
  by_cases hp : (ω, ℓ) ∈ S
  · rw [indicator_of_mem hp, indicator_of_mem (show ℓ ∈ {ℓ : ℝ | (ω, ℓ) ∈ S} from hp)]
    rfl
  · rw [indicator_of_notMem hp, indicator_of_notMem (show ℓ ∉ {ℓ : ℝ | (ω, ℓ) ∈ S} from hp)]

end Thm18Asm
end QuantumZipper
