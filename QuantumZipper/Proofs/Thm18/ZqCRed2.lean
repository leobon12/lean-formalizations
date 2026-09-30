import QuantumZipper.Proofs.Thm18.ZqCRed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (9): the reduction `ZqCLocSandwichStmt → ZqCZoomTransferStmt → G3ZqO6CoreDStmt`

See `ZqCRed` for the statement of the sandwich node and the strategy. Own bookkeeping
(AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL G3ZqO Factorization G2PalmLoc

theorem measurable_rhoP (γ : ℝ) : Measurable (rhoP γ) :=
  (E1.measurable_rhoNorm (((Real.measurable_log.comp measurable_norm).neg).const_mul _ :
      Measurable (LogSingGood.Lf (γ - 2 / γ))) R18.g3zS).ennreal_ofReal

/-- The Palm-side expectation of a circle functional at `x`. -/
def palmE (F : (ℕ → ℝ) → ℝ → ℝ≥0∞) (γ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (V : Ω' → FieldSample) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, F (vOf (G1Zm.palmFieldAt γ x (V ω))) x ∂P'

/-- Its weighted integral over the core. -/
def palmM (F : (ℕ → ℝ) → ℝ → ℝ≥0∞) (γ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (V : Ω' → FieldSample) (left : Bool) (η : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (coreSet left η).indicator (fun x => rhoP γ x * palmE F γ P' V x) x

theorem measurable_palmE_omega {F : (ℕ → ℝ) → ℝ → ℝ≥0∞} (hF : Measurable (uncurry F)) (γ : ℝ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {V : Ω' → FieldSample}
    (hV : IsFreeGFFModConstH V P') (x : ℝ) :
    Measurable fun ω => F (vOf (G1Zm.palmFieldAt γ x (V ω))) x := by
  have h1 : Measurable fun ω : Ω' => ((x, ω) : ℝ × Ω') := measurable_const.prodMk measurable_id
  have h := hF.comp (((measurable_vOf_palmField hV γ).comp h1).prodMk
    (measurable_const (a := x)))
  simp only [Function.comp_def] at h
  exact h

theorem measurable_palmE {F : (ℕ → ℝ) → ℝ → ℝ≥0∞} (hF : Measurable (uncurry F)) (γ : ℝ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [SFinite P'] {V : Ω' → FieldSample}
    (hV : IsFreeGFFModConstH V P') : Measurable (palmE F γ P' V) := by
  have h : Measurable fun p : ℝ × Ω' => F (vOf (G1Zm.palmFieldAt γ p.1 (V p.2))) p.1 := by
    have h := hF.comp ((measurable_vOf_palmField hV γ).prodMk measurable_fst)
    simp only [Function.comp_def] at h
    exact h
  exact h.lintegral_prod_right'

theorem measurable_palmW {F : (ℕ → ℝ) → ℝ → ℝ≥0∞} (hF : Measurable (uncurry F)) (γ : ℝ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [SFinite P'] {V : Ω' → FieldSample}
    (hV : IsFreeGFFModConstH V P') (left : Bool) (η : ℝ) :
    Measurable fun x => (coreSet left η).indicator (fun x => rhoP γ x * palmE F γ P' V x) x :=
  ((measurable_rhoP γ).mul (measurable_palmE hF γ hV)).indicator (measurableSet_coreSet left η)

/-- The Palm identity for a circle functional on the core. -/
theorem palm_vOf {γ : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} {V : Ω' → FieldSample}
    (hPI : ZqCPalmFor γ P' X A V) (left : Bool) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4)
    {F : (ℕ → ℝ) → ℝ → ℝ≥0∞} (hF : Measurable (uncurry F)) :
    ∫⁻ ω, ∫⁻ x, (coreSet left η).indicator (fun x => F (vOf (F2.zU γ X A ω)) x) x
        ∂(qBoundaryMeasure γ (F2.zU γ X A ω)) ∂P' = palmM F γ P' V left η :=
  palmFor_core hPI left hη hη4 cJ rJ cJ_mem rJ_pos cJ_ball F hF

/-- **The weighted Palm mass of a vanishing functional vanishes.** -/
theorem tendsto_palmM_zero {γ : ℝ} (hγ : 0 < γ) {β : ℝ → (ℕ → ℝ) → ℝ → ℝ≥0∞}
    (hβm : ∀ L, Measurable (uncurry (β L))) (hβ1 : ∀ L v x, β L v x ≤ 1)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {V : Ω' → FieldSample} (hV : IsFreeGFFModConstH V P') (left : Bool) {η : ℝ} (hη : 0 < η)
    (hη4 : η < 1 / 4)
    (hlim : ∀ x ∈ coreSet left η, Tendsto (fun L => palmE (β L) γ P' V x) atTop (𝓝 0)) :
    Tendsto (fun L => palmM (β L) γ P' V left η) atTop (𝓝 0) := by
  have hT := measurableSet_coreSet left η
  obtain ⟨K, hK⟩ := rhoNorm_le_core γ hγ left hη hη4
  have h0 : (0 : ℝ≥0∞) = ∫⁻ x, (coreSet left η).indicator (fun _ => (0 : ℝ≥0∞)) x := by simp
  rw [h0]
  refine tendsto_lintegral_filter_of_dominated_convergence'
    ((coreSet left η).indicator fun _ => ENNReal.ofReal K)
    (Eventually.of_forall fun L => (measurable_palmW (hβm L) γ hV left η).aemeasurable)
    (Eventually.of_forall fun L => ae_of_all _ fun x => ?_) ?_ (ae_of_all _ fun x => ?_)
  · by_cases hx : x ∈ coreSet left η
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      have hE : palmE (β L) γ P' V x ≤ 1 := by
        unfold palmE
        exact (lintegral_mono fun ω => hβ1 L _ _).trans (le_of_eq (by simp))
      calc rhoP γ x * palmE (β L) γ P' V x ≤ ENNReal.ofReal K * 1 :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (hK x hx)) hE
        _ = ENNReal.ofReal K := mul_one _
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  · rw [lintegral_indicator_const hT]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    cases left
    · simp [coreSet]
    · simp [coreSet]
  · by_cases hx : x ∈ coreSet left η
    · simp only [indicator_of_mem hx]
      have := ENNReal.Tendsto.const_mul (a := rhoP γ x) (hlim x hx) (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_zero] at this
      exact this
    · simp only [indicator_of_notMem hx]
      exact tendsto_const_nhds

end ZqC
end Thm18Asm
end QuantumZipper
