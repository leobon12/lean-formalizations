import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Adj
import MatedCRTHarmonic.Frozen.Dart
import MatedCRTHarmonic.Frozen.Dsrc
import MatedCRTHarmonic.Frozen.Dtgt
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.StateVertex
import MatedCRTHarmonic.Frozen.IsPlaneData
import MatedCRTHarmonic.Frozen.OutDarts
import MatedCRTHarmonic.Frozen.StateMeasurableSpace
import MatedCRTHarmonic.Frozen.StepMeasure
import MatedCRTHarmonic.Frozen.StepMeasureIsProbability
import MatedCRTHarmonic.Frozen.WalkKernel
import MatedCRTHarmonic.Frozen.WalkKernelIsMarkov
import MatedCRTHarmonic.Frozen.WalkLaw
import MatedCRTHarmonic.Frozen.VertexPath
import MatedCRTHarmonic.Markov.Chain

/-!
# §4 preliminaries: chained edge-end paths and the embedded walk

An edge-end path `ω : ℕ → G.State` is *chained* with dart sequence `D` if step `k + 1` traverses the dart `D k`
and `D k` leaves the vertex occupied at time `k` (`IsDartChain ω D`). Simple random walk is chained almost surely
(`ae_isChained`; the state space is countable by properness). Along a chained path the embedded walk
`Y = Φ.embeddedWalk ω` (frozen definition, unit time per step) satisfies, the polar-template argument A7/A8 and the blueprint's
Lemma `b:lem-walkcurve`:

* on `[k, k+1]` it is the traversal of `D k`: `Y t = Φ.stepCurve (inr (D k)) (t - k)` (`embeddedWalk_eq_of_mem_Icc`);
* at integer times it sits at the walk's vertex: `Y k = Φ(X_k)` (`embeddedWalk_natCast`);
* it is continuous (`continuous_embeddedWalk`);
* `Y([k, k+1]) = Φ(e_k)` (`image_Icc_succ`) and `Y([m, n]) = ⋃_{m ≤ k < n} Φ(e_k)` (`image_Icc_natCast`);
* at non-integer times it lies on the open arc of the current edge (`embeddedWalk_mem_openArc`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal unitInterval

namespace MatedCRTHarmonic.WalkSteps

variable {V E : Type*} {G : LFMultigraph V E}

/-- `ω` is a chained edge-end path with dart sequence `D`: step `k + 1` traverses `D k`, which leaves the vertex
occupied at time `k`. -/
def IsDartChain (ω : ℕ → G.State) (D : ℕ → G.Dart) : Prop :=
  ∀ k, ω (k + 1) = Sum.inr (D k) ∧ G.dsrc (D k) = G.stateVertex (ω k)

section Chained

variable {ω : ℕ → G.State} {D : ℕ → G.Dart}

theorem IsDartChain.state_succ (h : IsDartChain ω D) (k : ℕ) : ω (k + 1) = Sum.inr (D k) := (h k).1

theorem IsDartChain.dsrc_eq (h : IsDartChain ω D) (k : ℕ) : G.dsrc (D k) = G.vertexPath ω k := (h k).2

theorem IsDartChain.vertexPath_succ (h : IsDartChain ω D) (k : ℕ) :
    G.vertexPath ω (k + 1) = G.dtgt (D k) := by
  simp only [LFMultigraph.vertexPath, h.state_succ k]
  rfl

theorem IsDartChain.dsrc_succ (h : IsDartChain ω D) (k : ℕ) : G.dsrc (D (k + 1)) = G.dtgt (D k) := by
  rw [h.dsrc_eq, h.vertexPath_succ]

/-- The local time parameter on `[k, k+1]`. -/
def stepParam (k : ℕ) (t : ℝ≥0) : I := projIcc 0 1 zero_le_one ((t : ℝ) - k)

theorem continuous_stepParam (k : ℕ) : Continuous (stepParam k) :=
  continuous_projIcc.comp (NNReal.continuous_coe.sub continuous_const)

theorem coe_stepParam {k : ℕ} {t : ℝ≥0} (ht : t ∈ Icc (k : ℝ≥0) (k + 1)) :
    (stepParam k t : ℝ) = (t : ℝ) - k := by
  have h1 : (k : ℝ) ≤ t := by exact_mod_cast ht.1
  have h2 : (t : ℝ) ≤ k + 1 := by exact_mod_cast ht.2
  rw [stepParam, projIcc_of_mem _ ⟨by linarith, by linarith⟩]

theorem stepParam_natCast (k : ℕ) : stepParam k k = 0 := by
  apply Subtype.ext
  rw [coe_stepParam ⟨le_rfl, by simp⟩]
  simp

theorem stepParam_natCast_add_one (k : ℕ) : stepParam k ((k : ℝ≥0) + 1) = 1 := by
  apply Subtype.ext
  rw [coe_stepParam ⟨by simp, le_rfl⟩]
  simp

/-- The time `k + u` of `[k, k+1]`. -/
def stepTime (k : ℕ) (u : I) : ℝ≥0 := (k : ℝ≥0) + Real.toNNReal (u : ℝ)

theorem coe_stepTime (k : ℕ) (u : I) : (stepTime k u : ℝ) = k + u := by
  rw [stepTime, NNReal.coe_add, NNReal.coe_natCast, Real.coe_toNNReal _ u.2.1]

theorem stepTime_mem (k : ℕ) (u : I) : stepTime k u ∈ Icc (k : ℝ≥0) (k + 1) := by
  constructor
  · rw [← NNReal.coe_le_coe, coe_stepTime, NNReal.coe_natCast]
    linarith [u.2.1]
  · rw [← NNReal.coe_le_coe, coe_stepTime, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    linarith [u.2.2]

theorem stepParam_stepTime (k : ℕ) (u : I) : stepParam k (stepTime k u) = u := by
  apply Subtype.ext
  rw [coe_stepParam (stepTime_mem k u), coe_stepTime]
  ring

theorem locallyFinite_Icc_natCast : LocallyFinite fun k : ℕ => Icc (k : ℝ≥0) (k + 1) := by
  intro t
  refine ⟨Iio (t + 1), Iio_mem_nhds (lt_add_one t), (finite_Iio (⌊t⌋₊ + 2)).subset ?_⟩
  rintro k ⟨y, hy, hyt⟩
  have hkt : (k : ℝ≥0) < t + 1 := lt_of_le_of_lt hy.1 hyt
  have hfl : t < (⌊t⌋₊ : ℝ≥0) + 1 := Nat.lt_floor_add_one t
  have : (k : ℝ≥0) < ((⌊t⌋₊ + 2 : ℕ) : ℝ≥0) := by
    push_cast
    calc (k : ℝ≥0) < t + 1 := hkt
      _ < (⌊t⌋₊ : ℝ≥0) + 1 + 1 := by gcongr
      _ = (⌊t⌋₊ : ℝ≥0) + 2 := by ring
  exact_mod_cast this

theorem iUnion_Icc_natCast : ⋃ k : ℕ, Icc (k : ℝ≥0) (k + 1) = univ := by
  refine eq_univ_of_forall fun t => mem_iUnion.mpr ⟨⌊t⌋₊, Nat.floor_le zero_le, ?_⟩
  exact (Nat.lt_floor_add_one t).le

theorem monotone_stepParam (k : ℕ) : Monotone (stepParam k) := fun s t hst =>
  monotone_projIcc _ (sub_le_sub_right (by exact_mod_cast hst) _)

theorem Icc_zero_one_I : Icc (0 : I) 1 = univ := eq_univ_of_forall fun u => ⟨u.2.1, u.2.2⟩

theorem stepParam_mem_Ioo {k : ℕ} {t : ℝ≥0} (ht : t ∈ Ioo (k : ℝ≥0) (k + 1)) :
    stepParam k t ∈ Ioo (0 : I) 1 := by
  have h1 : (k : ℝ) < t := by exact_mod_cast ht.1
  have h2 : (t : ℝ) < k + 1 := by exact_mod_cast ht.2
  have hc := coe_stepParam (k := k) (t := t) ⟨ht.1.le, ht.2.le⟩
  constructor
  · show (0 : ℝ) < stepParam k t
    rw [hc]
    linarith
  · show (stepParam k t : ℝ) < 1
    rw [hc]
    linarith

end Chained

/-! ### Simple random walk is chained almost surely -/

/-- The state space carries the discrete σ-algebra, so singletons are measurable. -/
theorem measurableSingletonClass_state : MeasurableSingletonClass G.State :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- A step of the walk kernel from `x` never uses a dart that does not leave `x`. -/
theorem stepMeasure_singleton_eq_zero {x : V} {v : G.State}
    (hv : ∀ d : G.Dart, v = Sum.inr d → G.dsrc d ≠ x) : G.stepMeasure x {v} = 0 := by
  classical
  rw [LFMultigraph.stepMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  have h0 : ∀ d ∈ G.outDarts x, (Measure.dirac (show G.State from Sum.inr d)) {v} = 0 := by
    intro d hd
    rw [Measure.dirac_apply' _ MeasurableSpace.measurableSet_top, indicator_of_notMem]
    intro hdv
    rw [mem_singleton_iff] at hdv
    have hd' : G.dsrc d = x := by
      unfold LFMultigraph.outDarts at hd
      exact (Finset.mem_filter.mp hd).2
    exact hv d hdv.symm hd'
  rw [Finset.sum_congr rfl h0, Finset.sum_const_zero, smul_zero]

/-- Simple random walk starts at its starting vertex almost surely. -/
theorem ae_start (x : V) : ∀ᵐ ω ∂G.walkLaw x, ω 0 = Sum.inl x := by
  have := measurableSingletonClass_state (G := G)
  exact Markov.chainLaw_ae_start G.walkKernel _

end MatedCRTHarmonic.WalkSteps
