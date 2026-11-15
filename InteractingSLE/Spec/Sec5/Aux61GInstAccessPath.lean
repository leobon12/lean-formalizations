/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstAccess

/-! # Continuity and measurability of the selected-access completion -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal Classical
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61FibData Restart

variable {X : Type*} [MeasurableSpace X] {E : Set X} {c : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E c ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E c ρ T V)

include hs hV hV0 hland

theorem continuousOn_accessExitPath {x : X} (hx : x ∈ exitEv E c ρ T V) :
    ContinuousOn (accessExitPath E c ρ T V x) (Iic (exitNN E c ρ T V x)) := by
  classical
  have heT : ((exitNN E c ρ T V x : ℝ≥0) : ℝ≥0∞) ≤ T x :=
    IsRestartSpec.coe_exitNN hx ▸ IsRestartSpec.exitTime_le x
  intro u hu
  rcases lt_or_eq_of_le (mem_Iic.1 hu) with hue | rfl
  · have hc : ContinuousAt (inPath E c ρ T x) u :=
      (hs.continuousOn_inPath hx.1.1).continuousAt
        ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds
          ((ENNReal.coe_lt_coe.2 hue).trans_le heT))
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [gt_mem_nhds hue] with r hr
    simp [accessExitPath, hx, hr]
  · change Tendsto (fun r => accessExitPath E c ρ T V x r) (𝓝[≤] _)
      (𝓝 (accessExitPath E c ρ T V x (exitNN E c ρ T V x)))
    simp only [accessExitPath, hx, ite_true, lt_irrefl, ite_false]
    have hsplit : 𝓝[≤] (exitNN E c ρ T V x) =
        𝓝[<] (exitNN E c ρ T V x) ⊔ pure (exitNN E c ρ T V x) := by
      rw [← Iio_union_right, nhdsWithin_union, nhdsWithin_singleton]
    rw [hsplit]
    refine Tendsto.sup ((accessExitPoint_spec hs hV hV0 hland hx).2.congr' ?_) ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_Iio] at hr
      simp [hr]
    · rw [tendsto_pure_left]
      intro s hs'
      simpa using mem_of_mem_nhds hs'

omit hland in
theorem accessExitPath_zero {x : X} (hx : x ∈ exitEv E c ρ T V) :
    accessExitPath E c ρ T V x 0 = 0 := by
  classical
  simp only [accessExitPath, hx, exitNN_pos hs hV hV0 hx, ite_true]
  exact hs.inPath_zero hx.1.1 hx.1.2

theorem measurable_accessExitPoint :
    Measurable (fun x => if x ∈ exitEv E c ρ T V then accessExitPoint E c ρ T V x else 0) := by
  classical
  have hm : Measurable (exitNN E c ρ T V) :=
    ENNReal.measurable_toNNReal.comp (hs.measurable_exitTime hV)
  refine measurable_of_tendsto_metrizable
    (f := fun n x => if x ∈ exitEv E c ρ T V then
      inPath E c ρ T x (beforeEnd (exitNN E c ρ T V x) n) else 0) ?_ ?_
  · intro n
    refine measurable_piecewise_eval (hs.measurableSet_exitEv hV) hs.measurable_inPath
      (hm.mul_const _) fun x hx => (hs.continuousOn_inPath hx.1.1).mono ?_
    intro r hr
    have heT : ((exitNN E c ρ T V x : ℝ≥0) : ℝ≥0∞) ≤ T x :=
      IsRestartSpec.coe_exitNN hx ▸ IsRestartSpec.exitTime_le x
    exact (ENNReal.coe_lt_coe.2
      (hr.trans_lt (beforeEnd_lt (exitNN_pos hs hV hV0 hx) n))).trans_le heT
  · rw [tendsto_pi_nhds]
    intro x
    by_cases hx : x ∈ exitEv E c ρ T V
    · simp only [hx, ite_true]
      exact (accessExitPoint_spec hs hV hV0 hland hx).2.comp
        (tendsto_beforeEnd_left (exitNN_pos hs hV hV0 hx))
    · simp only [hx, ite_false]
      exact tendsto_const_nhds

theorem measurable_accessExitPath (u : ℝ≥0) :
    Measurable (fun x => accessExitPath E c ρ T V x u) := by
  classical
  have he : Measurable (exitNN E c ρ T V) :=
    ENNReal.measurable_toNNReal.comp (hs.measurable_exitTime hV)
  have hset : MeasurableSet (exitEv E c ρ T V ∩ {x | u < exitNN E c ρ T V x}) :=
    (hs.measurableSet_exitEv hV).inter (measurableSet_lt measurable_const he)
  have hm : Measurable (fun x => if x ∈ exitEv E c ρ T V ∩ {x | u < exitNN E c ρ T V x}
      then inPath E c ρ T x u
      else if x ∈ exitEv E c ρ T V then accessExitPoint E c ρ T V x else 0) :=
    Measurable.ite hset (hs.measurable_inPath u) (measurable_accessExitPoint hs hV hV0 hland)
  convert hm using 1
  funext x
  by_cases hx : x ∈ exitEv E c ρ T V <;>
    simp [accessExitPath, hx]

theorem isPathSpec_accessExitPath :
    IsPathSpec (exitEv E c ρ T V) (accessExitPath E c ρ T V) (exitNN E c ρ T V) :=
  ⟨hs.measurableSet_exitEv hV,
    ENNReal.measurable_toNNReal.comp (hs.measurable_exitTime hV),
    measurable_accessExitPath hs hV hV0 hland,
    fun _ hx => continuousOn_accessExitPath hs hV hV0 hland hx,
    fun _ hx => accessExitPath_zero hs hV hV0 hx⟩

end InteractingSLE.Sec5.Aux61GInst
