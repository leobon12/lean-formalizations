/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvWTilt

/-! # Locality transfers under the exact chart comparison tilt -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H)
namespace CMIVSetting
variable {S : Type u} [MeasurableSpace S] (D : CMIVSetting S)

/-- Any local set of the original chart field remains local for the shifted
chart field under the explicit comparison measure. -/
theorem isLocalSet_chartField {A : S → Set ℂ} (hloc : IsLocalSet A D.h' D.Q₀) :
    IsLocalSet A D.chartField D.tilt := by
  let _ := D.Q₀_prob
  let c : ℝ := D.θ * QuantumZipper.chiC D.κ
  let I₀ : ℝ := ∫ z, D.F.src z
  let s' := fun n => chartTest D.y (D.s n)
  let Λ' := fun ω => D.Λ ω + c * I₀
  let k' := D.k * Real.exp (c * I₀)
  have hs : ∀ n z, |s' n z| ≤ |(D.F.shift D.y).src z| := fun n z => by
    change |chartTest D.y (D.s n) z| ≤ |(D.F.shift D.y).src z|
    rw [chartTest_apply, CMCut.src_shift]
    exact D.s_bound n (z + D.y)
  have hslim : ∀ z, Tendsto (fun n => s' n z) atTop (𝓝 ((D.F.shift D.y).src z)) := fun z => by
    simp only [s', chartTest_apply, CMCut.src_shift]
    exact D.s_limit _
  have hints : ∀ n, (∫ z, s' n z) = ∫ z, D.s n z := fun n => by
    simp only [s', chartTest_apply]
    exact integral_add_right_eq_self (fun z => D.s n z) (D.y : ℂ)
  have hI : Tendsto (fun n => ∫ z, D.s n z) atTop (𝓝 I₀) :=
    tendsto_integral_of_dominated_convergence (fun z => |D.F.src z|)
      (fun n => (D.s n).continuous.aestronglyMeasurable) D.F.integrable_src.abs
      (fun n => ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact D.s_bound n z)
      (ae_of_all _ D.s_limit)
  have hΛ : ∀ᵐ ω ∂D.Q₀, Tendsto (fun n => D.h' ω (s' n)) atTop (𝓝 (Λ' ω)) := by
    filter_upwards [D.pairing_limit] with ω hω
    have he : ∀ n, D.h' ω (s' n) = D.H₀ ω (D.s n) + c * ∫ z, s' n z := fun n =>
      D.translate ω (D.s n) (s' n) fun z => chartTest_apply D.y (D.s n) z
    simp only [he, hints]
    exact hω.add (hI.const_mul c)
  have hk : 0 < k' := mul_pos D.k_pos (Real.exp_pos _)
  have hdens : (fun ω => ENNReal.ofReal (k' * Real.exp (-Λ' ω))) =
      fun ω => ENNReal.ofReal (D.k * Real.exp (-D.Λ ω)) := by
    funext ω
    congr 1
    simp only [k', Λ', neg_add, Real.exp_add]
    rw [show D.k * Real.exp (c * I₀) * (Real.exp (-D.Λ ω) * Real.exp (-(c * I₀))) =
      D.k * Real.exp (-D.Λ ω) * (Real.exp (c * I₀) * Real.exp (-(c * I₀))) by ring,
      ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hprob : IsProbabilityMeasure (D.Q₀.withDensity fun ω => ENNReal.ofReal (k' * Real.exp (-Λ' ω))) := by
    rw [hdens]
    exact D.tilt_prob
  have hq : InnerProductSpace.HarmonicOnNhd (fun z => D.q (z + D.y)) H := fun z hz =>
    Exist.harmonicAt_comp_add_const (D.q_extension.1 _ (Exist.add_real_mem_H hz D.y))
  have h := isLocalSet_withDensity_cmiCut hloc D.coupling.2.1 (D.F.shift D.y) hs hslim hΛ hk hprob hq
  rw [hdens] at h
  exact h

end CMIVSetting
end InteractingSLE.Restart.FlowStopIdentCMI
