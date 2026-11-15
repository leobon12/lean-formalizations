import MathFin.Probability.Brownian.UnifPart
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Left-point Riemann sums for Lebesgue–Stieltjes integrals

This is the deterministic bracket-integral passage needed by the
partition proof of Itô's formula. The integrator is Mathlib's existing
`StieltjesFunction`; it is not assumed absolutely continuous.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Ito.Gen

lemma integral_Ioc_partition (ν : Measure ℝ≥0) {g : ℝ≥0 → ℝ}
    {π : ℕ → ℝ≥0} (hπ : Monotone π) (n : ℕ)
    (hg : IntegrableOn g (Ioc (π 0) (π n)) ν) :
    (∫ u in Ioc (π 0) (π n), g u ∂ν) =
      ∑ k ∈ Finset.range n, ∫ u in Ioc (π k) (π (k + 1)), g u ∂ν := by
  have hUnion : (⋃ k ∈ Finset.range n, Ioc (π k) (π (k + 1))) = Ioc (π 0) (π n) := by
    simpa only [Finset.mem_range, Set.mem_Ico, Nat.zero_le, true_and, Order.succ_eq_add_one] using
      hπ.biUnion_Ico_Ioc_map_succ 0 n
  rw [← hUnion]
  refine integral_biUnion_finset _ (fun _ _ => measurableSet_Ioc) ?_ ?_
  · exact fun i _ j _ hij => hπ.pairwise_disjoint_on_Ioc_succ hij
  · intro k hk
    exact hg.mono_set (Ioc_subset_Ioc (hπ (Nat.zero_le k))
      (hπ (Finset.mem_range.1 hk)))

lemma stieltjes_measureReal_Ioc (A : StieltjesFunction ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) :
    A.measure.real (Ioc s t) = A t - A s := by
  rw [measureReal_def, StieltjesFunction.measure_Ioc, ENNReal.toReal_ofReal
    (sub_nonneg.2 (A.mono hst))]

lemma stieltjes_integral_sub (A : StieltjesFunction ℝ≥0) {g : ℝ≥0 → ℝ}
    (hg : Continuous g) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ u in Ioc 0 t, g u ∂A.measure) - (∫ u in Ioc 0 s, g u ∂A.measure) =
      ∫ u in Ioc s t, g u ∂A.measure := by
  have hgi (a b : ℝ≥0) : IntegrableOn g (Ioc a b) A.measure :=
    hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hd : Disjoint (Ioc (0 : ℝ≥0) s) (Ioc s t) :=
    Set.disjoint_left.2 fun _ hu hv => (not_lt_of_ge hu.2) hv.1
  have h := setIntegral_union hd measurableSet_Ioc (hgi 0 s) (hgi s t)
  rw [Ioc_union_Ioc_eq_Ioc (show (0 : ℝ≥0) ≤ s from bot_le) hst] at h
  rw [h, add_sub_cancel_left]

lemma abs_stieltjes_integral_le (A : StieltjesFunction ℝ≥0) {g : ℝ≥0 → ℝ}
    {s t : ℝ≥0} (hst : s ≤ t) {C : ℝ} (hg : ∀ u ∈ Ioc s t, |g u| ≤ C) :
    |∫ u in Ioc s t, g u ∂A.measure| ≤ C * (A t - A s) := by
  rw [← stieltjes_measureReal_Ioc A hst]
  simpa only [Real.norm_eq_abs] using
    norm_setIntegral_le_of_norm_le_const (μ := A.measure) (f := g)
      (measure_Ioc_lt_top (μ := A.measure)) (fun u hu => by
        simpa only [Real.norm_eq_abs] using hg u hu)

/-- On a partition, the Stieltjes-sum error is at most the oscillation of the
integrand within a cell, times the total mass of the interval. -/
lemma abs_stieltjes_sum_sub_integral_le (A : StieltjesFunction ℝ≥0)
    {g : ℝ≥0 → ℝ} (hg : Continuous g) {π : ℕ → ℝ≥0} (hπ : Monotone π)
    (n : ℕ) {η : ℝ}
    (hosc : ∀ k < n, ∀ u ∈ Ioc (π k) (π (k + 1)), |g (π k) - g u| ≤ η) :
    |(∑ k ∈ Finset.range n, g (π k) * (A (π (k + 1)) - A (π k))) -
      (∫ u in Ioc (π 0) (π n), g u ∂A.measure)| ≤ η * (A (π n) - A (π 0)) := by
  have hgi : IntegrableOn g (Ioc (π 0) (π n)) A.measure :=
    hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hcell (k : ℕ) : IntegrableOn g (Ioc (π k) (π (k + 1))) A.measure :=
    hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hconst (k : ℕ) (c : ℝ) : IntegrableOn (fun _ : ℝ≥0 => c)
      (Ioc (π k) (π (k + 1))) A.measure := by
    exact integrableOn_const (measure_Ioc_lt_top (μ := A.measure)).ne
  have heq (k : ℕ) : g (π k) * (A (π (k + 1)) - A (π k)) -
      (∫ u in Ioc (π k) (π (k + 1)), g u ∂A.measure) =
        ∫ u in Ioc (π k) (π (k + 1)), (g (π k) - g u) ∂A.measure := by
    rw [integral_sub (hconst k _) (hcell k), setIntegral_const,
      stieltjes_measureReal_Ioc A (hπ (Nat.le_succ k)), smul_eq_mul, mul_comm]
  rw [integral_Ioc_partition A.measure hπ n hgi, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ Finset.range n, (g (π k) * (A (π (k + 1)) - A (π k)) -
        (∫ u in Ioc (π k) (π (k + 1)), g u ∂A.measure))| ≤
        ∑ k ∈ Finset.range n, η * (A (π (k + 1)) - A (π k)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
      rw [heq k, ← stieltjes_measureReal_Ioc A (hπ (Nat.le_succ k))]
      simpa only [Real.norm_eq_abs] using norm_setIntegral_le_of_norm_le_const
        (μ := A.measure) (f := fun u => g (π k) - g u) (C := η)
        (measure_Ioc_lt_top (μ := A.measure))
        (fun u hu => by simpa only [Real.norm_eq_abs] using hosc k (Finset.mem_range.1 hk) u hu)
    _ = η * (A (π n) - A (π 0)) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => A (π k))]

/-- Uniform left-point sums converge to the Lebesgue–Stieltjes integral.
No density of the Stieltjes measure with respect to Lebesgue measure is used. -/
theorem tendsto_stieltjes_sum (A : StieltjesFunction ℝ≥0)
    {g : ℝ≥0 → ℝ} (hg : Continuous g) {s t : ℝ≥0} (hst : s ≤ t) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      g (MathFin.unifPartIcc s t n k) *
        (A (MathFin.unifPartIcc s t n (k + 1)) - A (MathFin.unifPartIcc s t n k))) atTop
      (𝓝 (∫ u in Ioc s t, g u ∂A.measure)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set D := A t - A s with hDdef
  have hD : 0 ≤ D := sub_nonneg.2 (A.mono hst)
  set η := ε / (D + 1) with hηdef
  have hη : 0 < η := div_pos hε (by linarith)
  have hηD : η * D < ε := by
    rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < D + 1)]
    nlinarith
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn) η hη
  obtain ⟨N, hN⟩ := exists_nat_gt (((t : ℝ) - s) / δ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : 0 < n := (Nat.succ_pos N).trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hmesh : ((t : ℝ) - s) / n < δ := by
    rw [div_lt_iff₀ hnR]
    rw [div_lt_iff₀ hδ] at hN
    have hnN : (N : ℝ) < n := by exact_mod_cast Nat.lt_of_succ_le hn
    nlinarith
  let π := MathFin.unifPartIcc s t n
  have hπ : Monotone π := MathFin.unifPartIcc_mono s t n
  have h0 : π 0 = s := MathFin.unifPartIcc_zero s t n
  have hlast : π n = t := MathFin.unifPartIcc_self hst hn0.ne'
  have hmem (k : ℕ) (hk : k ≤ n) : π k ∈ Icc s t := by
    constructor
    · exact h0 ▸ hπ (Nat.zero_le k)
    · exact (hπ hk).trans_eq hlast
  have hcell : ∀ k < n, ∀ u ∈ Ioc (π k) (π (k + 1)), |g (π k) - g u| ≤ η := by
    intro k hk u hu
    have humem : u ∈ Icc s t :=
      ⟨(hmem k hk.le).1.trans hu.1.le, hu.2.trans (hmem (k + 1) hk).2⟩
    have hdist : dist (π k) u < δ := by
      rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.2 (NNReal.coe_le_coe.2 hu.1.le))]
      have hstep : (π (k + 1) : ℝ) - π k = ((t : ℝ) - s) / n :=
        MathFin.unifPartIcc_succ_sub hst n k
      have hu' : (u : ℝ) ≤ π (k + 1) := hu.2
      linarith
    simpa only [Real.dist_eq] using (hosc (π k) (hmem k hk.le) u humem hdist).le
  have hb := abs_stieltjes_sum_sub_integral_le A hg hπ n hcell
  rw [h0, hlast] at hb
  rw [Real.dist_eq]
  exact hb.trans_lt hηD

end InteractingSLE.Ito.Gen
