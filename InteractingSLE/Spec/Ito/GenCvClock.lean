import InteractingSLE.Spec.Ito.GenStieltjes
import MathFin.Probability.Martingales.LevyQuadraticSums

/-!
# Continuous-clock substitution for the DDS reduction

The clock may have flat intervals or singular continuous variation. This module
only proves deterministic integral identities; it assumes no time-change theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open MathFin MathFin.ItoIntegralL2
open scoped NNReal ENNReal

namespace InteractingSLE.Ito.GenCont

/-- A continuous increasing nonnegative clock as a Stieltjes integrator. -/
def clockPath (a : ℝ≥0 → ℝ≥0) (ha : Monotone a) (hc : Continuous a) :
    StieltjesFunction ℝ≥0 where
  toFun t := a t
  mono' _ _ h := ha h
  right_continuous' _ := (NNReal.continuous_coe.comp hc).continuousWithinAt

@[simp] lemma clockPath_apply (a : ℝ≥0 → ℝ≥0) (ha : Monotone a) (hc : Continuous a)
    (t : ℝ≥0) : clockPath a ha hc t = a t := rfl

/-- The identity-clock Stieltjes measure is the port's time measure on every
integration interval. Restriction avoids an endpoint convention at zero. -/
lemma clockPath_id_restrict (s t : ℝ≥0) :
    (clockPath id monotone_id continuous_id).measure.restrict (Ioc s t) =
      timeMeasure.restrict (Ioc s t) := by
  have : IsFiniteMeasure ((clockPath id monotone_id continuous_id).measure.restrict
      (Ioc s t)) := ⟨by
    rw [Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  apply Measure.ext_of_Iic
  intro u
  rw [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  have hinter : Iic u ∩ Ioc s t = Ioc s (min u t) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
    tauto
  simp only [hinter, StieltjesFunction.measure_Ioc, clockPath_apply, id_eq,
    timeMeasure_Ioc]

/-- Stieltjes sums along any monotone partitions whose cell sizes tend to zero. -/
theorem tendsto_stieltjes_sum_of_mesh (A : StieltjesFunction ℝ≥0)
    {g : ℝ≥0 → ℝ} (hg : Continuous g) {π : ℕ → ℕ → ℝ≥0} {s t : ℝ≥0}
    (hπ : ∀ n, Monotone (π n))
    (h0 : ∀ᶠ n in atTop, π n 0 = s) (hlast : ∀ᶠ n in atTop, π n n = t)
    (hmesh : ∀ δ > (0 : ℝ), ∀ᶠ n in atTop,
      ∀ k < n, dist (π n k) (π n (k + 1)) < δ) :
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      g (π n k) * (A (π n (k + 1)) - A (π n k))) atTop
      (𝓝 (∫ u in Ioc s t, g u ∂A.measure)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let D := max (A t - A s) 0
  have hD : 0 ≤ D := le_max_right _ _
  let η := ε / (D + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hηD : η * D < ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < D + 1)]
    nlinarith
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn) η hη
  filter_upwards [h0, hlast, hmesh δ hδ] with n hn0 hnt hnmesh
  have hmem (k : ℕ) (hk : k ≤ n) : π n k ∈ Icc s t :=
    ⟨hn0 ▸ hπ n (Nat.zero_le k), (hπ n hk).trans_eq hnt⟩
  have hcell : ∀ k < n, ∀ u ∈ Ioc (π n k) (π n (k + 1)),
      |g (π n k) - g u| ≤ η := by
    intro k hk u hu
    have humem : u ∈ Icc s t :=
      ⟨(hmem k hk.le).1.trans hu.1.le, hu.2.trans (hmem (k + 1) hk).2⟩
    have hdist : dist (π n k) u < δ := by
      apply lt_of_le_of_lt _ (hnmesh k hk)
      rw [NNReal.dist_eq, NNReal.dist_eq,
        abs_of_nonpos (sub_nonpos.2 (NNReal.coe_le_coe.2 hu.1.le)),
        abs_of_nonpos (sub_nonpos.2 (NNReal.coe_le_coe.2 (hπ n (Nat.le_succ k))))]
      exact neg_le_neg (sub_le_sub_left (NNReal.coe_le_coe.2 hu.2) _)
    simpa only [Real.dist_eq] using (hosc _ (hmem k hk.le) u humem hdist).le
  have hb := Gen.abs_stieltjes_sum_sub_integral_le A hg (hπ n) n hcell
  rw [hn0, hnt] at hb
  rw [Real.dist_eq]
  exact hb.trans_lt ((mul_le_mul_of_nonneg_left (le_max_left _ _) hη.le).trans_lt hηD)

/-- Change of variable for Stieltjes integrators under a continuous clock.
This also transports singular finite-variation coordinates in the mixed formula. -/
theorem integral_comp_stieltjes (A D : StieltjesFunction ℝ≥0)
    {a : ℝ≥0 → ℝ≥0} (ha : Monotone a) (hc : Continuous a)
    (hAD : ∀ u, A u = D (a u))
    {g : ℝ≥0 → ℝ} (hg : Continuous g) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ u in Ioc s t, g (a u) ∂A.measure) =
      ∫ v in Ioc (a s) (a t), g v ∂D.measure := by
  let π := fun n k => a (unifPartIcc s t n k)
  have hzero : ∀ n, π n 0 = a s := fun n => congrArg a (unifPartIcc_zero s t n)
  have hlast : ∀ᶠ n in atTop, π n n = a t := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact congrArg a (unifPartIcc_self hst hn)
  have hmesh : ∀ δ > (0 : ℝ), ∀ᶠ n in atTop,
      ∀ k < n, dist (π n k) (π n (k + 1)) < δ := by
    intro δ hδ
    have hlim := LevyQuadraticSums.tendsto_maxIncr
      (M := fun r (_ : Unit) => (a r : ℝ))
      (fun _ => NNReal.continuous_coe.comp hc) s t ()
    filter_upwards [(tendsto_order.1 hlim).2 δ hδ] with n hn k hk
    rw [NNReal.dist_eq, abs_sub_comm]
    exact (LevyQuadraticSums.abs_le_maxIncr s t (Finset.mem_range.2 hk) ()).trans_lt hn
  have hright := tendsto_stieltjes_sum_of_mesh D hg
    (fun n => ha.comp (unifPartIcc_mono s t n)) (.of_forall hzero) hlast hmesh
  have hleft := Gen.tendsto_stieltjes_sum A (hg.comp hc) hst
  simp only [hAD] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The deterministic change of variable used after DDS. No density of the
clock with respect to time is assumed. -/
theorem integral_comp_clock {a : ℝ≥0 → ℝ≥0} (ha : Monotone a) (hc : Continuous a)
    {g : ℝ≥0 → ℝ} (hg : Continuous g) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ u in Ioc s t, g (a u) ∂(clockPath a ha hc).measure) =
      ∫ v in Ioc (a s) (a t), g v ∂timeMeasure := by
  have heq := integral_comp_stieltjes (clockPath a ha hc)
    (clockPath id monotone_id continuous_id) ha hc (fun _ => rfl) hg hst
  rw [clockPath_id_restrict] at heq
  exact heq

end InteractingSLE.Ito.GenCont
