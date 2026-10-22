import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Uniform probabilistic bounds for almost surely continuous positive paths. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace HigherDimLQGMetric

theorem l9c_uniform_bounds_of_ae_continuousOn {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ → ℝ)
    (hm : ∀ r, Measurable fun ω => X ω r)
    {a b : ℝ} (hab : a ≤ b)
    (hae : ∀ᵐ ω ∂P, ContinuousOn (X ω) (Icc a b) ∧
      ∀ r ∈ Icc a b, 0 < X ω r) :
    ∃ m M : ℝ, 0 < m ∧ ∀ r ∈ Icc a b,
      (4⁻¹ : ℝ≥0∞) < P {ω | m ≤ X ω r ∧ X ω r ≤ M} := by
  obtain ⟨Q,hQc,hQs,hQd⟩ :=
    TopologicalSpace.exists_countable_dense_subset (Icc a b : Set ℝ)
  have hQclosure : closure Q = Icc a b := by
    exact Subset.antisymm (closure_minimal hQs isClosed_Icc) hQd
  let E : ℕ → Set Ω := fun n => {ω | ∀ q ∈ Q,
    1 / ((n : ℝ) + 1) ≤ X ω q ∧ X ω q ≤ (n : ℝ) + 1}
  have hEm (n : ℕ) : MeasurableSet (E n) := by
    have heq : E n = ⋂ q ∈ Q,
      {ω | 1 / ((n : ℝ) + 1) ≤ X ω q ∧ X ω q ≤ (n : ℝ) + 1} := by
      ext ω
      simp only [E, mem_ofPred_eq, mem_iInter]
    rw [heq]
    apply MeasurableSet.biInter hQc
    intro q hq
    exact (measurableSet_le measurable_const (hm q)).inter
      (measurableSet_le (hm q) measurable_const)
  have hEmono : Monotone E := by
    intro m n hmn ω hω q hq
    obtain ⟨hl,hu⟩ := hω q hq
    have hlow : 1 / ((n : ℝ)+1) ≤ 1 / ((m : ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
    have hupp : (m : ℝ)+1 ≤ (n : ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hmn
    exact ⟨hlow.trans hl,hu.trans hupp⟩
  have hfull : P (⋃ n, E n) = 1 := by
    apply le_antisymm (by simpa only [measure_univ] using
      (measure_mono (subset_univ (⋃ n, E n)) : P (⋃ n, E n) ≤ P univ))
    have hAE : ∀ᵐ ω ∂P, ω ∈ ⋃ n, E n := by
      filter_upwards [hae] with ω ⟨hcont,hpos⟩
      obtain ⟨u,hu,hu'⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hcont
      obtain ⟨v,hv,hv'⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hcont
      have hup : 0 < X ω u := hpos u hu
      obtain ⟨N, hN⟩ := exists_nat_gt (max (X ω v) (1 / X ω u))
      refine mem_iUnion.mpr ⟨N, ?_⟩
      intro q hq
      have hqI : q ∈ Icc a b := hQs hq
      have hmin : X ω u ≤ X ω q := hu' hqI
      have hmax : X ω q ≤ X ω v := hv' hqI
      have hNup : X ω v < (N : ℝ)+1 := by linarith [le_max_left (X ω v) (1 / X ω u)]
      have hNlo : 1 / ((N : ℝ)+1) ≤ X ω u := by
        have ht : 1 / X ω u < (N : ℝ)+1 := by
          linarith [le_max_right (X ω v) (1 / X ω u)]
        have hmul : 1 < ((N : ℝ)+1) * X ω u := (div_lt_iff₀ hup).mp ht
        apply (div_le_iff₀ (by positivity : (0:ℝ)<(N:ℝ)+1)).2
        nlinarith only [hmul]
      exact ⟨hNlo.trans hmin,hmax.trans hNup.le⟩
    have hset : (⋃ n, E n) =ᵐ[P] (univ : Set Ω) :=
      hAE.mono fun ω hω => by simp [hω]
    have heq := measure_congr hset
    simpa only [measure_univ] using heq.ge
  have hlim := tendsto_measure_iUnion_atTop (μ := P) hEmono
  rw [hfull] at hlim
  have hquarter : (4⁻¹ : ℝ≥0∞) < 1 := by norm_num
  obtain ⟨N,hN⟩ := (Filter.Eventually.exists
    (hlim.eventually (Ioi_mem_nhds hquarter)))
  refine ⟨1 / ((N : ℝ)+1), (N : ℝ)+1, by positivity, fun r hr => ?_⟩
  have hsubsetAE : ∀ᵐ ω ∂P, ω ∈ E N →
      ω ∈ {ω | 1 / ((N : ℝ)+1) ≤ X ω r ∧ X ω r ≤ (N : ℝ)+1} := by
    filter_upwards [hae] with ω hω hEN
    have hmap : Q.MapsTo (X ω) (Icc (1 / ((N : ℝ)+1)) ((N : ℝ)+1)) :=
      fun q hq => hEN q hq
    have hcont : ContinuousOn (X ω) (closure Q) := by
      rw [hQclosure]
      exact hω.1
    have hh := hmap.closure_of_continuousOn hcont
    simpa only [isClosed_Icc.closure_eq, mem_Icc] using
      hh (by simpa only [hQclosure] using hr)
  exact hN.trans_le (measure_mono_ae hsubsetAE)

end HigherDimLQGMetric
