/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafInitHAssembly
import InteractingSLE.Stochastic.Martingale.Backward
import Mathlib.Topology.DenseEmbedding

/-!
# Reconstructing continuous paths from limits on dyadic times

The limit condition concerns only the restriction to the dense dyadic set.
Mathlib's dense extension constructs the continuous path. Upper dyadic limits
identify that extension with a countable, pointwise measurable construction.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique

/-- The dyadic observation times, as a subset of nonnegative real time. -/
def dyadicTimes : Set ℝ≥0 := range dyadicTime

/-- Existing upper dyadic approximations prove density of the observation times. -/
theorem dense_dyadicTimes : Dense dyadicTimes := by
  intro t
  exact mem_closure_of_tendsto (tendsto_dyadicTime_upperDyadic t)
    (Eventually.of_forall fun n => ⟨upperDyadic t n, rfl⟩)

/-- A path read by upper dyadic limits, defined at every nonnegative time. -/
def dyadicTimeLimit (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  limUnder atTop fun n => f (dyadicTime (upperDyadic t n))

/-- If the dyadic restriction has a limit at each time, its upper-dyadic reader
is exactly the existing dense extension. -/
theorem dyadicTimeLimit_eq_extend {f : ℝ≥0 → ℝ}
    (hlim : ∀ t : ℝ≥0, ∃ c : ℝ, Tendsto (fun d : dyadicTimes => f d)
      (comap (fun d : dyadicTimes => (d : ℝ≥0)) (𝓝 t)) (𝓝 c)) :
    dyadicTimeLimit f = dense_dyadicTimes.extend (fun d : dyadicTimes => f d) := by
  have hc := dense_dyadicTimes.continuous_extend hlim
  have he := dense_dyadicTimes.isDenseInducing_val.extend_eq' hlim
  funext t
  have ht := (hc.tendsto t).comp (tendsto_dyadicTime_upperDyadic t)
  have heq : (fun n => dense_dyadicTimes.extend (fun d : dyadicTimes => f d)
      (dyadicTime (upperDyadic t n))) = fun n => f (dyadicTime (upperDyadic t n)) := by
    funext n
    exact he ⟨dyadicTime (upperDyadic t n), upperDyadic t n, rfl⟩
  dsimp only [Function.comp_def] at ht
  rw [heq] at ht
  exact ht.limUnder_eq

/-- The pointwise upper-dyadic construction is continuous under the dyadic
limit condition. No regularity at nondyadic values of the original path is used. -/
theorem continuous_dyadicTimeLimit {f : ℝ≥0 → ℝ}
    (hlim : ∀ t : ℝ≥0, ∃ c : ℝ, Tendsto (fun d : dyadicTimes => f d)
      (comap (fun d : dyadicTimes => (d : ℝ≥0)) (𝓝 t)) (𝓝 c)) :
    Continuous (dyadicTimeLimit f) := by
  rw [dyadicTimeLimit_eq_extend hlim]
  exact dense_dyadicTimes.continuous_extend hlim

/-- At a dyadic time the reconstruction retains the original value. -/
theorem dyadicTimeLimit_eq_at {f : ℝ≥0 → ℝ}
    (hlim : ∀ t : ℝ≥0, ∃ c : ℝ, Tendsto (fun d : dyadicTimes => f d)
      (comap (fun d : dyadicTimes => (d : ℝ≥0)) (𝓝 t)) (𝓝 c))
    {t : ℝ≥0} (ht : t ∈ dyadicTimes) : dyadicTimeLimit f t = f t := by
  rw [dyadicTimeLimit_eq_extend hlim]
  exact dense_dyadicTimes.isDenseInducing_val.extend_eq' hlim ⟨t, ht⟩

end InteractingSLE.WFS
