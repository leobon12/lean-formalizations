import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# G2 for the concrete scheme, first step: absorbing error events

The handoff (`handoff/G3.md`, G3-SCH) routes the error events of the concrete G3 scheme (Palm
point too close to a region edge, localization of the region field, length partner vs welding
partner) into G2 and G3-Transfer. For G2 (`G2TwoPointStmt`, per-set `L¹` form) this is the
following stability: if the events `A i` and `B i` differ only on events of vanishing
probability, and the conditional probabilities of `B i` converge in `L¹` to a constant, so do
those of `A i` (`tendsto_integral_abs_condExp_sub_of_symmDiff`). The proof is the
`L¹`-contraction of conditional expectation (`integral_abs_condExp_le`):
`∫ |P[1_A | 𝒢] − P[1_B | 𝒢]| ≤ ∫ |1_A − 1_B| = P(A ∆ B)`. Own elementary argument (AGENT_GUIDE
cost rule).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm

variable {α : Type*} [mα : MeasurableSpace α]

theorem integral_abs_condExp_indicator_sub_le (P : Measure α) [IsFiniteMeasure P]
    (𝒢 : MeasurableSpace α) {A B : Set α} (hA : MeasurableSet[mα] A) (hB : MeasurableSet[mα] B) :
    ∫ x, |P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] x - P[B.indicator (fun _ => (1 : ℝ)) | 𝒢] x| ∂P
      ≤ P.real (symmDiff A B) := by
  have iA : Integrable (A.indicator fun _ => (1 : ℝ)) P := (integrable_const 1).indicator hA
  have iB : Integrable (B.indicator fun _ => (1 : ℝ)) P := (integrable_const 1).indicator hB
  calc ∫ x, |P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] x - P[B.indicator (fun _ => (1 : ℝ)) | 𝒢] x| ∂P
        = ∫ x, |P[A.indicator (fun _ => (1 : ℝ)) - B.indicator (fun _ => (1 : ℝ)) | 𝒢] x| ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [condExp_sub iA iB 𝒢] with x hx
          rw [hx, Pi.sub_apply]
    _ ≤ ∫ x, |(A.indicator (fun _ => (1 : ℝ)) - B.indicator (fun _ => (1 : ℝ))) x| ∂P :=
          integral_abs_condExp_le _
    _ = ∫ x, (symmDiff A B).indicator (fun _ => (1 : ℝ)) x ∂P := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [Pi.sub_apply, indicator, mem_symmDiff]
          by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha, hb, Set.mem_symmDiff]
    _ = P.real (symmDiff A B) := integral_indicator_one (hA.symmDiff hB)

/-- **Error absorption for G2.** -/
theorem tendsto_integral_abs_condExp_sub_of_symmDiff {ι : Type*} {l : Filter ι}
    {𝒢 : ι → MeasurableSpace α} {P : ι → Measure α} [∀ i, IsProbabilityMeasure (P i)]
    {A B : ι → Set α} (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) {c : ℝ}
    (hE : Tendsto (fun i => (P i).real (symmDiff (A i) (B i))) l (𝓝 0))
    (hBc : Tendsto (fun i => ∫ x, |(P i)[(B i).indicator (fun _ => (1 : ℝ)) | 𝒢 i] x - c|
      ∂(P i)) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, |(P i)[(A i).indicator (fun _ => (1 : ℝ)) | 𝒢 i] x - c| ∂(P i))
      l (𝓝 0) := by
  refine squeeze_zero (fun i => integral_nonneg fun _ => abs_nonneg _) (fun i => ?_)
    (by simpa using hBc.add hE)
  set a := (P i)[(A i).indicator (fun _ => (1 : ℝ)) | 𝒢 i]
  set b := (P i)[(B i).indicator (fun _ => (1 : ℝ)) | 𝒢 i]
  have ia : Integrable a (P i) := integrable_condExp
  have ib : Integrable b (P i) := integrable_condExp
  calc ∫ x, |a x - c| ∂(P i) ≤ ∫ x, (|b x - c| + |a x - b x|) ∂(P i) := by
        refine integral_mono (ia.sub (integrable_const c)).abs
          ((ib.sub (integrable_const c)).abs.add (ia.sub ib).abs) fun x => ?_
        calc |a x - c| = |(b x - c) + (a x - b x)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
    _ = ∫ x, |b x - c| ∂(P i) + ∫ x, |a x - b x| ∂(P i) :=
        integral_add (ib.sub (integrable_const c)).abs (ia.sub ib).abs
    _ ≤ ∫ x, |b x - c| ∂(P i) + (P i).real (symmDiff (A i) (B i)) := by
        gcongr
        exact integral_abs_condExp_indicator_sub_le (P i) (𝒢 i) (hA i) (hB i)

end Thm18Asm
end QuantumZipper
