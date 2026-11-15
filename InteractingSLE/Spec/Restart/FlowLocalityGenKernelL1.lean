/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowLocalityGenKernelCov
import InteractingSLE.Spec.Restart.FlowLocalityGenSetting

/-!
# Flow locality with a general agreement set: `L¹` convergence of the tilt densities

Packet PROVE-G7A-LOC (PROVE-G3RESTART §5.2, step 2 (a)). The densities `e^{−h'(s'_n)}` of the chart pairings converge
to `e^{−Λ'}` in `L¹(Q₀)`: almost surely (the pairing limit) and with a uniform `L²` bound
`E e^{−2 H₀(s_n)} = e^{−2μ_n + 2v_n}` (the Gaussian law of each pairing; `μ_n`, `v_n` bounded by domination
`|s_n| ≤ |F.src|`, as in `FlowStopIdentCMI.integrable_exp_neg_of_isGFF`).

* `exists_integral_exp_neg_two_le`;
* **`GSetting.tendsto_eLpNorm_exp_neg_chart`**.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowLocalityGen
open QuantumZipper (H greenH)
open LQGMetric (TestOn DistOn)
open FlowStopIdentCMI

section Law
variable {b : ℝ → ℝ} {J : Finset ℝ} {S : Type*} [MeasurableSpace S] {Q₀ : Measure S} [IsProbabilityMeasure Q₀]
  {H₀ : S → DistOn upperHalfPlaneOpens}

/-- **A uniform bound for `E e^{−2 H₀(s_n)}`** along tests dominated by a cutoff source. -/
theorem exists_integral_exp_neg_two_le (hb : IsPiecewiseConstantBoundaryData b J)
    (hH : IsGFFWithBoundaryData Q₀ H₀ b J) (F : CMCut) {s : ℕ → TestOn upperHalfPlaneOpens}
    (hsle : ∀ n z, |s n z| ≤ |F.src z|) :
    ∃ B : ℝ, ∀ n, Integrable (fun x => Real.exp (-2 * H₀ x (s n))) Q₀ ∧
      ∫ x, Real.exp (-2 * H₀ x (s n)) ∂Q₀ ≤ B := by
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨C₀, hC₀⟩ := hu₀.2.1
  set A : ℝ := |C₀| * ∫ z, |F.src z| with hA
  set B : ℝ := ∫ p : ℂ × ℂ, |(|F.src p.1| * |F.src p.2| * greenH p.1 p.2)| ∂((volume : Measure ℂ).prod volume)
    with hB
  have hY := hH.2 u₀ hu₀
  refine ⟨Real.exp (2 * A + 2 * B), fun n => ?_⟩
  have hm : Measurable fun x => H₀ x (s n) := (LQGMetric.measurable_distOn_apply (s n)).comp hH.1
  have hmap := Coupling.map_eval_eq_gaussianReal_of_isZBGFFProcess hY (s n)
  set μn : ℝ := ∫ z, u₀ z * s n z with hμn
  set vn : ℝ := QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens (s n) (s n) with hvn
  have hvn0 : 0 ≤ vn := LocalSets.zeroGFFTestCov_self_nonneg upperHalfPlaneOpens.isOpen subset_rfl (s n)
  have hlaw : HasLaw (fun x => H₀ x (s n)) (gaussianReal μn vn.toNNReal) Q₀ := ⟨hm.aemeasurable, hmap⟩
  have hint : Integrable (fun x => Real.exp (-2 * H₀ x (s n))) Q₀ := by
    have h1 := integrable_exp_mul_gaussianReal (μ := μn) (v := vn.toNNReal) (-2)
    have h2 : Integrable (fun y : ℝ => Real.exp (-2 * y)) (Q₀.map fun x => H₀ x (s n)) := by rwa [hmap]
    exact h2.comp_measurable hm
  refine ⟨hint, ?_⟩
  have hmgf := mgf_gaussianReal hlaw (-2)
  have e : ∫ x, Real.exp (-2 * H₀ x (s n)) ∂Q₀ = mgf (fun x => H₀ x (s n)) Q₀ (-2) := by
    simp only [mgf]
  rw [e, hmgf, Real.coe_toNNReal _ hvn0]
  refine Real.exp_le_exp.2 ?_
  have hμ : -μn ≤ A := by
    have h1 : |μn| ≤ ∫ z, |C₀| * |F.src z| := by
      rw [hμn]
      refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _)
        (F.integrable_src.abs.const_mul _) (ae_of_all _ fun z => ?_))
      show |u₀ z * s n z| ≤ |C₀| * |F.src z|
      rw [abs_mul]
      by_cases hz : z ∈ H
      · exact mul_le_mul ((hC₀ z hz).trans (le_abs_self _)) (hsle n z) (abs_nonneg _) (abs_nonneg _)
      · have h0 := hsle n z
        rw [F.src_of_notMem hz, abs_zero] at h0
        rw [abs_nonpos_iff.1 h0, abs_zero, mul_zero]
        exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [integral_const_mul] at h1
    linarith [neg_le_abs μn]
  have hv : vn ≤ B := by
    have hvg : vn = LocalExt.greenEnergy (s n) (s n) := by
      rw [hvn, LQGMetric.zeroGFFTestCov_eq_green (V := upperHalfPlaneOpens) subset_rfl GFF.isConformalOnto_id_H]
      rfl
    rw [hvg]
    have hI := F.integrable_abs_mul_greenH.abs
    have hdom : ∀ p : ℂ × ℂ, |s n p.1 * s n p.2 * greenH p.1 p.2| ≤
        |(|F.src p.1| * |F.src p.2| * greenH p.1 p.2)| := fun p => by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_abs, abs_abs]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hsle n p.1) (hsle n p.2) (abs_nonneg _)
        (abs_nonneg _)) (abs_nonneg _)
    calc LocalExt.greenEnergy (s n) (s n) ≤ |LocalExt.greenEnergy (s n) (s n)| := le_abs_self _
      _ ≤ ∫ p : ℂ × ℂ, |s n p.1 * s n p.2 * greenH p.1 p.2| ∂((volume : Measure ℂ).prod volume) :=
        abs_integral_le_integral_abs
      _ ≤ B := integral_mono_of_nonneg (ae_of_all _ fun p => abs_nonneg _) hI (ae_of_all _ hdom)
  nlinarith

end Law

namespace GSetting
variable {S : Type u} [MeasurableSpace S] (D : GSetting S)

/-- **`L¹(Q₀)` convergence of the chart tilt densities** `e^{−h'(s'_n)} → e^{−Λ'}`, `s'_n = s_n(· + y)`,
`Λ' = Λ + θχ ∫ F.src`. -/
theorem tendsto_eLpNorm_exp_neg_chart :
    Tendsto (fun n => eLpNorm (fun x => Real.exp (-D.h' x (chartTest D.y (D.s n))) -
      Real.exp (-(D.Λ x + D.θ * QuantumZipper.chiC D.κ * ∫ z, D.F.src z))) 1 D.Q₀) atTop (𝓝 0) := by
  let _ := D.Q₀_prob
  set c : ℝ := D.θ * QuantumZipper.chiC D.κ with hc
  set I₀ : ℝ := ∫ z, D.F.src z with hI₀
  have hints : ∀ n, ∫ z, chartTest D.y (D.s n) z = ∫ z, D.s n z := fun n => by
    simp only [chartTest_apply]
    exact integral_add_right_eq_self (fun z => D.s n z) (D.y : ℂ)
  have hI : Tendsto (fun n => ∫ z, D.s n z) atTop (𝓝 I₀) :=
    tendsto_integral_of_dominated_convergence (fun z => |D.F.src z|) (fun n => (D.s n).continuous.aestronglyMeasurable)
      D.F.integrable_src.abs (fun n => ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact D.s_bound n z)
      (ae_of_all _ D.s_limit)
  have htr : ∀ x n, D.h' x (chartTest D.y (D.s n)) = D.H₀ x (D.s n) + c * ∫ z, D.s n z := fun x n => by
    rw [D.translate x (D.s n) (chartTest D.y (D.s n)) fun z => chartTest_apply D.y (D.s n) z, hints]
  have hIb : ∀ n, |∫ z, D.s n z| ≤ ∫ z, |D.F.src z| := fun n =>
    (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _)
      D.F.integrable_src.abs (ae_of_all _ fun z => D.s_bound n z))
  obtain ⟨B, hB⟩ := exists_integral_exp_neg_two_le D.b_pc D.H₀_gff D.F D.s_bound
  have hm : ∀ n, Measurable fun x => D.h' x (chartTest D.y (D.s n)) := fun n =>
    (LQGMetric.measurable_distOn_apply _).comp D.coupling.2.1
  have hint : Integrable (fun x => Real.exp (-(D.Λ x + c * I₀))) D.Q₀ := by
    refine ((integrable_exp_neg_of_prob D.Λ_measurable D.k_pos D.tilt_prob).const_mul
      (Real.exp (-(c * I₀)))).congr (ae_of_all _ fun x => ?_)
    simp only [neg_add, Real.exp_add]; ring
  have hsq : ∀ n x, Real.exp (-D.h' x (chartTest D.y (D.s n))) ^ 2 =
      Real.exp (-2 * D.H₀ x (D.s n)) * Real.exp (-2 * (c * ∫ z, D.s n z)) := fun n x => by
    rw [htr, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hE : ∀ n, Real.exp (-2 * (c * ∫ z, D.s n z)) ≤ Real.exp (2 * |c| * ∫ z, |D.F.src z|) := fun n => by
    refine Real.exp_le_exp.2 ?_
    have h1 : -2 * (c * ∫ z, D.s n z) ≤ 2 * |c * ∫ z, D.s n z| := by
      nlinarith [neg_abs_le (c * ∫ z, D.s n z)]
    have h2 : |c * ∫ z, D.s n z| ≤ |c| * ∫ z, |D.F.src z| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hIb n) (abs_nonneg c)
    nlinarith
  refine tendsto_eLpNorm_one_of_sq_le (fun n => Real.measurable_exp.comp (hm n).neg) hint ?_ (fun n => ?_)
    (B := B * Real.exp (2 * |c| * ∫ z, |D.F.src z|)) (fun n => ?_)
  · filter_upwards [D.pairing_limit] with x hx
    have hlim : Tendsto (fun n => D.h' x (chartTest D.y (D.s n))) atTop (𝓝 (D.Λ x + c * I₀)) := by
      simp only [htr]
      exact hx.add (hI.const_mul c)
    exact ((Real.continuous_exp.comp continuous_neg).tendsto _).comp hlim
  · simp only [hsq]
    exact ((hB n).1.mul_const _)
  · simp only [hsq]
    rw [integral_mul_const]
    exact mul_le_mul (hB n).2 (hE n) (Real.exp_pos _).le
      (((integral_nonneg fun x => (Real.exp_pos _).le)).trans (hB n).2)

end GSetting

end InteractingSLE.Restart.FlowLocalityGen
