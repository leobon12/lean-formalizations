import QuantumZipper.Proofs.Thm18.G3ZqO2Trunc
import QuantumZipper.Proofs.Thm18.G3Z2bPalm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-G1 (4): the Palm identity of the wedge on the core of the window

`R18.G3WedgePalmIdStmt` (proved, `R18.g3WedgePalmIdStmt_holds`) is stated with a continuous
weight `w` supported in a window `[a, b] ⊆ [−1/2, 1/2]` avoiding the root. For the core
`T = Icc u v` of the truncated Palm window (G3ZqO2Trunc) we take the trapezoid weight equal to
`1` on `T` and supported in `[u − m, v + m]`, and the functional `1_T(x) φ(·, x)`; the weight then
disappears:

  `E ∫ 1_T(x) φ((h(fc_j))_j, x) ν_h(dx) = ∫ 1_T(x) ρ(x) E φ((h^x(fc_j))_j, x) dx`

(`wedge_palm_Icc`), and in particular on the core `coreSet left η` (`wedge_palm_core`, margin
`η/2`, window `[η/2, 1/2]` or `[−1/2, −η/2]`).

Duplantier–Sheffield, arXiv:0808.1560, §3.3 (rooted measure), through `G3WedgePalmIdStmt`.
Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqO

/-- The trapezoid weight: `1` on `[u, v]`, `0` off `(u − m, v + m)`. -/
def trapW (u v m : ℝ) (x : ℝ) : ℝ := max 0 (min 1 (min ((x - (u - m)) / m) (((v + m) - x) / m)))

theorem continuous_trapW (u v m : ℝ) : Continuous (trapW u v m) := by
  unfold trapW
  fun_prop

theorem trapW_nonneg (u v m x : ℝ) : 0 ≤ trapW u v m x := le_max_left _ _

theorem trapW_eq_one {u v m x : ℝ} (hm : 0 < m) (hx : x ∈ Icc u v) : trapW u v m x = 1 := by
  unfold trapW
  have h1 : 1 ≤ (x - (u - m)) / m := by rw [le_div_iff₀ hm]; linarith [hx.1]
  have h2 : 1 ≤ ((v + m) - x) / m := by rw [le_div_iff₀ hm]; linarith [hx.2]
  rw [min_eq_left (le_min h1 h2)]
  exact max_eq_right zero_le_one

theorem trapW_eq_zero {u v m x : ℝ} (hm : 0 < m) (hx : x ∉ Icc (u - m) (v + m)) :
    trapW u v m x = 0 := by
  unfold trapW
  simp only [mem_Icc, not_and_or, not_le] at hx
  refine max_eq_left ?_
  rcases hx with h | h
  · have : (x - (u - m)) / m < 0 := div_neg_of_neg_of_pos (by linarith) hm
    exact (min_le_right _ _).trans ((min_le_left _ _).trans this.le)
  · have : ((v + m) - x) / m < 0 := div_neg_of_neg_of_pos (by linarith) hm
    exact (min_le_right _ _).trans ((min_le_right _ _).trans this.le)

/-- **The wedge Palm identity with the weight `1_{[u,v]}`.** -/
theorem wedge_palm_Icc {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ)
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') :
    ∃ V : Ω' → FieldSample, IsFreeGFFModConstH V P' ∧
      ∀ u v m : ℝ, 0 < m → Icc (u - m) (v + m) ⊆ Icc (-(1 / 2)) (1 / 2) →
      (0 : ℝ) ∉ Icc (u - m) (v + m) →
      ∀ (c : ℕ → ℂ) (r : ℕ → ℝ), (∀ j, c j ∈ Hbar) → (∀ j, 0 < r j) →
        (∀ j, Metric.closedBall (c j) (r j) ∩ Hbar ⊆ Metric.ball (0 : ℂ) 1) →
      ∀ φ : (ℕ → ℝ) → ℝ → ℝ≥0∞, Measurable (Function.uncurry φ) →
        ∫⁻ ω, ∫⁻ x, (Icc u v).indicator
            (fun x => φ (fun j => F2.zU γ X A ω (foldedCircle (c j) (r j))) x) x
            ∂(qBoundaryMeasure γ (F2.zU γ X A ω)) ∂P' =
          ∫⁻ x, (Icc u v).indicator (fun x =>
            ENNReal.ofReal (PalmNorm.rhoNorm γ (LogSingGood.Lf (γ - 2 / γ)) R18.g3zS x) *
            ∫⁻ ω, φ (fun j => PalmNorm.normAt R18.g3zS
              (ofFun (PalmNorm.shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) R18.g3zS x) + V ω)
              (foldedCircle (c j) (r j))) x ∂P') x := by
  obtain ⟨V, hV, hPI⟩ := R18.g3WedgePalmIdStmt_holds γ hγ hγ2 P' X A hX hA hXA
  refine ⟨V, hV, ?_⟩
  intro u v m hm hsub h0 c r hc hr hin φ hφ
  set φ' : (ℕ → ℝ) → ℝ → ℝ≥0∞ := fun d x => (Icc u v).indicator (fun x => φ d x) x with hφ'
  have hφ'm : Measurable (Function.uncurry φ') := by
    have : Function.uncurry φ' = (Prod.snd ⁻¹' Icc u v).indicator (Function.uncurry φ) := by
      funext q
      simp only [Function.uncurry, hφ', indicator, mem_preimage]
    rw [this]
    exact hφ.indicator (measurable_snd measurableSet_Icc)
  have h := hPI (u - m) (v + m) hsub h0 c r hc hr hin (trapW u v m) (continuous_trapW u v m)
    (trapW_nonneg u v m) (fun x hx => trapW_eq_zero hm hx) φ' hφ'm
  convert h using 1
  · refine lintegral_congr fun ω => lintegral_congr fun x => ?_
    by_cases hx : x ∈ Icc u v
    · simp only [hφ', indicator_of_mem hx, trapW_eq_one hm hx, ENNReal.ofReal_one, one_mul]
    · simp only [hφ', indicator_of_notMem hx, mul_zero]
  · refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Icc u v
    · simp only [hφ', indicator_of_mem hx, trapW_eq_one hm hx, one_mul]
    · simp only [hφ', indicator_of_notMem hx, lintegral_zero, mul_zero]

/-- The core with its margin lies in the Palm range. -/
theorem coreSet_margin (left : Bool) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ∃ u v : ℝ, coreSet left η = Icc u v ∧ Icc (u - η / 2) (v + η / 2) ⊆ Icc (-(1 / 2)) (1 / 2) ∧
      (0 : ℝ) ∉ Icc (u - η / 2) (v + η / 2) := by
  cases left
  · refine ⟨η, 1 / 4, by simp [coreSet], ?_, ?_⟩
    · exact Icc_subset_Icc (by linarith) (by linarith)
    · intro h; linarith [h.1]
  · refine ⟨-(1 / 4), -η, by simp [coreSet], ?_, ?_⟩
    · exact Icc_subset_Icc (by linarith) (by linarith)
    · intro h; linarith [h.2]

/-- **The wedge Palm identity on the core of the window.** -/
theorem wedge_palm_core {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ)
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') :
    ∃ V : Ω' → FieldSample, IsFreeGFFModConstH V P' ∧
      ∀ (left : Bool) (η : ℝ), 0 < η → η < 1 / 4 →
      ∀ (c : ℕ → ℂ) (r : ℕ → ℝ), (∀ j, c j ∈ Hbar) → (∀ j, 0 < r j) →
        (∀ j, Metric.closedBall (c j) (r j) ∩ Hbar ⊆ Metric.ball (0 : ℂ) 1) →
      ∀ φ : (ℕ → ℝ) → ℝ → ℝ≥0∞, Measurable (Function.uncurry φ) →
        ∫⁻ ω, ∫⁻ x, (coreSet left η).indicator
            (fun x => φ (fun j => F2.zU γ X A ω (foldedCircle (c j) (r j))) x) x
            ∂(qBoundaryMeasure γ (F2.zU γ X A ω)) ∂P' =
          ∫⁻ x, (coreSet left η).indicator (fun x =>
            ENNReal.ofReal (PalmNorm.rhoNorm γ (LogSingGood.Lf (γ - 2 / γ)) R18.g3zS x) *
            ∫⁻ ω, φ (fun j => PalmNorm.normAt R18.g3zS
              (ofFun (PalmNorm.shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) R18.g3zS x) + V ω)
              (foldedCircle (c j) (r j))) x ∂P') x := by
  obtain ⟨V, hV, hI⟩ := wedge_palm_Icc hγ hγ2 P' X A hX hA hXA
  refine ⟨V, hV, ?_⟩
  intro left η hη hη4 c r hc hr hin φ hφ
  obtain ⟨u, v, e, hsub, h0⟩ := coreSet_margin left hη hη4
  rw [e]
  exact hI u v (η / 2) (by positivity) hsub h0 c r hc hr hin φ hφ

end G3ZqO
end Thm18Asm
end QuantumZipper
