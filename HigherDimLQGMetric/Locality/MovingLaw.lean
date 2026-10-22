import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! A fixed marginal transfers convergence in measure to moving copies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

/-- A sequence of inputs may move on a coupling, while each input retains
the same law. Any scale-dependent error that vanishes in measure under the
fixed law still vanishes in measure along those moving inputs. -/
theorem l7a_tendstoInMeasure_moving_fixed_law
    {Ω T E : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    [EDist E] (P : Measure Ω) (X : Ω → T) (Xn : ℕ → Ω → T)
    (hXn : ∀ n, Measurable (Xn n))
    (hlaw : ∀ n, P.map (Xn n) = P.map X)
    (Y : ℕ → T → E) (c : E)
    (hbad : ∀ (n : ℕ) (ε : ℝ≥0∞),
      MeasurableSet {t : T | ε ≤ edist (Y n t) c})
    (hbase : TendstoInMeasure (P.map X) Y atTop (fun _ => c)) :
    TendstoInMeasure P (fun n ω => Y n (Xn n ω)) atTop (fun _ => c) := by
  intro ε hε
  have heq (n : ℕ) :
      P {ω | ε ≤ edist (Y n (Xn n ω)) c} =
        (P.map X) {t | ε ≤ edist (Y n t) c} := by
    rw [← hlaw n, Measure.map_apply (hXn n) (hbad n ε)]
    rfl
  simpa only [heq] using hbase ε hε

/-- The same fixed-law argument yields an almost surely convergent
subsequence of the moving errors. -/
theorem l7a_exists_moving_fixed_law_ae_subseq
    {Ω T E : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    [PseudoEMetricSpace E] (P : Measure Ω) (X : Ω → T) (Xn : ℕ → Ω → T)
    (hXn : ∀ n, Measurable (Xn n))
    (hlaw : ∀ n, P.map (Xn n) = P.map X)
    (Y : ℕ → T → E) (c : E)
    (hbad : ∀ (n : ℕ) (ε : ℝ≥0∞),
      MeasurableSet {t : T | ε ≤ edist (Y n t) c})
    (hbase : TendstoInMeasure (P.map X) Y atTop (fun _ => c)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂P, Tendsto (fun k => Y (ns k) (Xn (ns k) ω)) atTop (𝓝 c) := by
  exact (l7a_tendstoInMeasure_moving_fixed_law P X Xn hXn hlaw Y c hbad hbase).exists_seq_tendsto_ae

end HigherDimLQGMetric
