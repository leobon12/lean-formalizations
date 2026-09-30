import QuantumZipper.Proofs.Thm18.G3ZqO4PalmT
import QuantumZipper.Proofs.Zipper.UnzipFullSplit
import QuantumZipper.Proofs.Loewner.TwoPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-G1 (5): the expected boundary mass of the core is finite

`lintegral_bdryM_core_lt_top`: for the unscaled wedge `h = wedgeU`,
`E ν_h(coreSet left η) < ∞`. By the Palm identity on the core (`wedge_palm_core` with `φ = 1`),
`E ν_h(T) = ∫_T ρ(x) dx`, and the Palm density
`ρ(x) = exp(γ Lf(x)/2 − (γ/2)∫Lf dS − (γ²/4) k_S(x) + (γ²/8) kk_S)` is bounded on `T`:
`|log |x|| ≤ |log η| + |log 4|` there, and `k_S(x) ≥ −2 log(5/4)` because every point of the unit
semicircle `S` is within distance `5/4` of `x` (`rhoNorm_le_core`).

Needed for dominated convergence in the window-shift step (G3ZqO6Shift). Duplantier–Sheffield,
arXiv:0808.1560, §3.3 (the rooted measure has density `ρ`). Own elementary proof (AGENT_GUIDE
cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqO

open G1Zm

/-- A lower bound of the Neumann potential of the unit semicircle near the root. -/
theorem kPot_g3zS_ge {x : ℝ} (hx : |x| ≤ 1 / 4) :
    -(2 * Real.log (5 / 4)) ≤ PalmNorm.kPot R18.g3zS (x : ℂ) := by
  have hl : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have hlog : ∀ t : ℝ, 0 ≤ t → t ≤ 5 / 4 → Real.log t ≤ Real.log (5 / 4) := by
    intro t ht0 ht
    rcases ht0.lt_or_eq with htp | hte
    · exact Real.log_le_log htp ht
    · rw [← hte, Real.log_zero]; exact hl.le
  have hbd : ∀ᵐ v ∂R18.g3zS, -(2 * Real.log (5 / 4)) ≤ neumannH (x : ℂ) v := by
    filter_upwards [UnzipFull.fc_ae_norm_le 0 zero_le_one] with v hv
    simp only [norm_zero, zero_add] at hv
    have hxn : ‖(x : ℂ)‖ ≤ 1 / 4 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hx
    have h1 : ‖(x : ℂ) - v‖ ≤ 5 / 4 := (norm_sub_le _ _).trans (by linarith)
    have h2 : ‖(x : ℂ) - conj v‖ ≤ 5 / 4 :=
      (norm_sub_le _ _).trans (by rw [Complex.norm_conj]; linarith)
    have e1 := hlog _ (norm_nonneg _) h1
    have e2 := hlog _ (norm_nonneg _) h2
    rw [neumannH]
    linarith
  unfold PalmNorm.kPot
  by_cases hi : Integrable (fun v => neumannH (x : ℂ) v) R18.g3zS
  · have h := integral_mono_ae (integrable_const (-(2 * Real.log (5 / 4)))) hi hbd
    rwa [integral_const, probReal_univ, one_smul] at h
  · rw [integral_undef hi]; linarith

/-- **The Palm density is bounded on the core.** -/
theorem rhoNorm_le_core (γ : ℝ) (hγ : 0 < γ) (left : Bool) {η : ℝ} (hη : 0 < η)
    (hη4 : η < 1 / 4) :
    ∃ K : ℝ, ∀ x ∈ coreSet left η,
      PalmNorm.rhoNorm γ (LogSingGood.Lf (γ - 2 / γ)) R18.g3zS x ≤ K := by
  set α := γ - 2 / γ with hα
  set B := |Real.log η| + |Real.log (1 / 4)| with hB
  set C := -(γ / 2 * ∫ u, LogSingGood.Lf α u ∂R18.g3zS) + γ ^ 2 / 8 * PalmNorm.kkPot R18.g3zS
    with hC
  refine ⟨Real.exp (γ * (|α| * B) / 2 + C + γ ^ 2 / 4 * (2 * Real.log (5 / 4))), ?_⟩
  intro x hx
  have hxa : η ≤ |x| ∧ |x| ≤ 1 / 4 := by
    cases left
    · simp only [coreSet, Bool.false_eq_true, ite_false, mem_Icc] at hx
      rw [abs_of_pos (by linarith [hx.1])]; exact hx
    · simp only [coreSet, ite_true, mem_Icc] at hx
      rw [abs_of_neg (by linarith [hx.2])]; constructor <;> linarith [hx.1, hx.2]
  have hlogx : |Real.log (abs x)| ≤ B := TwoPoint.abs_log_le_of_mem hη hxa.1 hxa.2
  have hLf : γ * LogSingGood.Lf α (x : ℂ) / 2 ≤ γ * (|α| * B) / 2 := by
    have : LogSingGood.Lf α (x : ℂ) ≤ |α| * B := by
      unfold LogSingGood.Lf
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc α * -Real.log (abs x) ≤ |α * -Real.log (abs x)| := le_abs_self _
        _ = |α| * |Real.log (abs x)| := by rw [abs_mul, abs_neg]
        _ ≤ |α| * B := mul_le_mul_of_nonneg_left hlogx (abs_nonneg _)
    have hγ2 : 0 ≤ γ / 2 := by positivity
    nlinarith
  have hk := kPot_g3zS_ge hxa.2
  have hk' : -(γ ^ 2 / 4 * PalmNorm.kPot R18.g3zS (x : ℂ)) ≤
      γ ^ 2 / 4 * (2 * Real.log (5 / 4)) := by
    have h4 : 0 ≤ γ ^ 2 / 4 := by positivity
    nlinarith
  unfold PalmNorm.rhoNorm
  refine Real.exp_le_exp.2 ?_
  rw [hC]
  linarith

/-- **The expected boundary mass of the core is finite.** -/
theorem lintegral_bdryM_core_lt_top {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type}
    [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ) (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P') (hXA : IndepFun X (fun ω t => A t ω) P')
    (left : Bool) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ∫⁻ ω', bdryM γ (wedgeU γ X A ω') (coreSet left η) ∂P' < ⊤ := by
  obtain ⟨V, -, hI⟩ := wedge_palm_core hγ hγ2 P' X A hX hA hXA
  have h := hI left η hη hη4 (fun _ => 0) (fun _ => 1 / 2) (fun _ => by simp [Hbar])
    (fun _ => by norm_num) (fun _ => by
      intro z hz
      have : ‖z‖ ≤ 1 / 2 := by simpa using hz.1
      simp only [Metric.mem_ball, dist_zero_right]; linarith)
    (fun _ _ => 1) measurable_const
  obtain ⟨K, hK⟩ := rhoNorm_le_core γ hγ left hη hη4
  have hT := measurableSet_coreSet left η
  calc ∫⁻ ω', bdryM γ (wedgeU γ X A ω') (coreSet left η) ∂P'
      ≤ ∫⁻ ω', qBoundaryMeasure γ (F2.zU γ X A ω') (coreSet left η) ∂P' :=
        lintegral_mono fun ω' => bdryM_le_qBoundaryMeasure γ _ _
    _ = ∫⁻ ω', ∫⁻ x, (coreSet left η).indicator (fun _ => (1 : ℝ≥0∞)) x
          ∂(qBoundaryMeasure γ (F2.zU γ X A ω')) ∂P' := by
        refine lintegral_congr fun ω' => ?_
        rw [lintegral_indicator_const hT, one_mul]
    _ = _ := h
    _ ≤ ∫⁻ x, (coreSet left η).indicator (fun _ => ENNReal.ofReal K) x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ coreSet left η
        · simp only [indicator_of_mem hx, lintegral_const, measure_univ, mul_one]
          exact ENNReal.ofReal_le_ofReal (hK x hx)
        · simp only [indicator_of_notMem hx, le_refl]
    _ = ENNReal.ofReal K * volume (coreSet left η) := lintegral_indicator_const hT _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        cases left
        · simp [coreSet]
        · simp [coreSet]

end G3ZqO
end Thm18Asm
end QuantumZipper
