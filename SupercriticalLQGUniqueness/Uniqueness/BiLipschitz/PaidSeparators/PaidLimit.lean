import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.PaidPair
import Mathlib.Analysis.SpecificLimits.Basic




 


set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators

def scaleEps (n : ℕ) : ℝ := (10 : ℝ) ^ (-(n : ℤ))

theorem scaleEps_pos (n : ℕ) : 0 < scaleEps n := by
  unfold scaleEps
  positivity

theorem scaleEps_tendsto_zero : Tendsto scaleEps atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((1 / 10 : ℝ) ^ n)) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact h.congr' (Filter.Eventually.of_forall fun n => by
    simp only [scaleEps, zpow_neg, zpow_natCast, inv_pow, one_div])

 

theorem metric_le_of_near_pairs (D' : LSCMetric) {z w : ℂ} {M : ℝ≥0∞}
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ z' w' : ℂ,
      dist z' z < ε ∧ dist w' w < ε ∧ D' (z', w') ≤ M) :
    D' (z, w) ≤ M := by
  have hchoice : ∀ n : ℕ, ∃ z' w' : ℂ,
      dist z' z < (1 : ℝ) / (n + 1) ∧
      dist w' w < (1 : ℝ) / (n + 1) ∧ D' (z', w') ≤ M := by
    intro n
    exact hnear _ (by positivity)
  choose z' w' hz hw hbound using hchoice
  have hε : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hzt : Tendsto z' atTop (𝓝 z) := by
    apply Metric.tendsto_atTop.mpr
    intro δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hε.eventually (gt_mem_nhds hδ))
    exact ⟨N, fun n hn => (hz n).trans (hN n hn)⟩
  have hwt : Tendsto w' atTop (𝓝 w) := by
    apply Metric.tendsto_atTop.mpr
    intro δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hε.eventually (gt_mem_nhds hδ))
    exact ⟨N, fun n hn => (hw n).trans (hN n hn)⟩
  have hpair : Tendsto (fun n => ((z' n, w' n), M)) atTop (𝓝 ((z, w), M)) :=
    (hzt.prodMk_nhds hwt).prodMk_nhds tendsto_const_nhds
  exact D'.lowerSemicontinuous.isClosed_epigraph.mem_of_tendsto hpair
    (Eventually.of_forall hbound)

 

theorem exists_unit_interval_near_curve (D : LSCMetric) (hL : D.IsLengthSpace)
    {z w : ℂ} (hzw : D (z, w) < ∞) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : ℝ → ℂ, D.IsCurve P 0 1 ∧ P 0 = z ∧ P 1 = w ∧
      D.len P 0 1 ≤ D (z, w) + ENNReal.ofReal δ := by
  obtain ⟨Q, a, b, hQ, hQa, hQb, hlen⟩ := hL z w hzw δ hδ
  obtain ⟨γ, hγ, -⟩ :=
    LQGMetric.MetricGeometry.exists_path_of_curve
      (P := D.pt ∘ Q) hQ.1 hQ.2
  let P : ℝ → ℂ := fun t => (γ.extend t : D.Space)
  have hcurve : D.IsCurve P 0 1 := by
    constructor
    · exact zero_le_one
    · change ContinuousOn γ.extend (Icc 0 1)
      exact γ.continuous_extend.continuousOn
  refine ⟨P, hcurve, ?_, ?_, ?_⟩
  · change γ.extend 0 = D.pt z
    rw [Path.extend_zero]
    exact congrArg D.pt hQa
  · change γ.extend 1 = D.pt w
    rw [Path.extend_one]
    exact congrArg D.pt hQb
  · change LQGMetric.MetricGeometry.curveLength γ.extend 0 1 ≤ _
    exact hγ.le.trans hlen

 

theorem good_grid_bound_along_path (D D' : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {A : ℝ} (hA : 1 ≤ A) (hgrid : GoodGridCover D D' A)
    {P : ℝ → ℂ} (hP : D.IsCurve P 0 1)
    (hfin : D.len P 0 1 ≠ ∞) :
    D' (P 0, P 1) ≤ ENNReal.ofReal (2 * A ^ 2) * D.len P 0 1 := by
  by_cases heq : P 0 = P 1
  · rw [heq, D'.isExtMetric.1]
    exact bot_le
  have hdist : 0 < dist (P 0) (P 1) := dist_pos.mpr heq
  have hPc : ContinuousOn P (Icc 0 1) :=
    BiLipschitz.Barrier.continuousOn_of_barrier D hB hP hfin
  have hbounded : Bornology.IsBounded (P '' Icc (0 : ℝ) 1) :=
    BiLipschitz.Barrier.isBounded_of_barrier D hB hP hfin
  obtain ⟨R, hR⟩ := hbounded.subset_ball (0 : ℂ)
  obtain ⟨m, hm⟩ := exists_nat_gt R
  have htrace : P '' Icc (0 : ℝ) 1 ⊆ closedBall (0 : ℂ) m := by
    intro y hy
    have hyR : dist y (0 : ℂ) < R := hR hy
    exact mem_closedBall.mpr (hyR.le.trans (by exact_mod_cast hm.le))
  obtain ⟨n₀, hgridm⟩ := hgrid m
  apply metric_le_of_near_pairs D'
  intro ε hε
  have hth : 0 < min (ε / 13) (dist (P 0) (P 1) / 6) := by
    apply lt_min
    · positivity
    · positivity
  have hev : ∀ᶠ n : ℕ in atTop,
      scaleEps n < min (ε / 13) (dist (P 0) (P 1) / 6) :=
    scaleEps_tendsto_zero.eventually (gt_mem_nhds hth)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  let n := max n₀ N₀
  have hn₀ : n₀ ≤ n := le_max_left _ _
  have hnN : N₀ ≤ n := le_max_right _ _
  obtain ⟨k, x, r, N, hr, hrange, hgood, hcover⟩ := hgridm n hn₀
  have hsmall := hN₀ n hnN
  have hdistScale : 6 * scaleEps n < dist (P 0) (P 1) := by
    have h := hsmall.trans_le (min_le_right _ _)
    linarith
  obtain ⟨z', w', hz', hw', hbound⟩ :=
    finite_stage_pair_bound D D' hB hL hA (scaleEps_pos n)
      hP hPc hfin hdistScale x r N hr
      (fun i => (hrange i).2) hgood
      (fun s hs => hcover (P s) (htrace ⟨s, hs, rfl⟩))
  refine ⟨z', w', ?_, ?_, hbound⟩
  · have h := hsmall.trans_le (min_le_left _ _)
    linarith
  · have h := hsmall.trans_le (min_le_left _ _)
    linarith

 


theorem paid_separator_all_pairs (D D' : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {A : ℝ} (hA : 1 ≤ A) (hgrid : GoodGridCover D D' A) :
    ∀ z w : ℂ, D' (z, w) ≤ ENNReal.ofReal (2 * A ^ 2) * D (z, w) := by
  have hCpos : 0 < 2 * A ^ 2 := by positivity
  have hCnn : 0 ≤ 2 * A ^ 2 := hCpos.le
  intro z w
  by_cases hzw_eq : z = w
  · subst w
    rw [D'.isExtMetric.1]
    exact bot_le
  by_cases hzw_top : D (z, w) = ∞
  · rw [hzw_top]
    have hCne : ENNReal.ofReal (2 * A ^ 2) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hCpos)
    change D' (z, w) ≤ ENNReal.ofReal (2 * A ^ 2) * ∞
    rw [ENNReal.mul_top hCne]
    exact le_top
  have hzw : D (z, w) < ∞ := lt_top_iff_ne_top.mpr hzw_top
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * A ^ 2)
  have hCfin : C < ∞ := ENNReal.ofReal_lt_top
  have htargetfin : C * D (z, w) < ∞ := ENNReal.mul_lt_top hCfin hzw
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let δ : ℝ := (ε : ℝ) / (2 * A ^ 2)
  have hδ : 0 < δ := div_pos (by exact_mod_cast hε) hCpos
  obtain ⟨P, hP, hP0, hP1, hlen⟩ :=
    exists_unit_interval_near_curve D hL hzw hδ
  have hfin : D.len P 0 1 ≠ ∞ := by
    apply ne_of_lt
    exact hlen.trans_lt (ENNReal.add_lt_top.mpr ⟨hzw, by simp⟩)
  have hpath := good_grid_bound_along_path D D' hB hL hA hgrid hP hfin
  have hCδ : C * ENNReal.ofReal δ = (ε : ℝ≥0∞) := by
    rw [show C = ENNReal.ofReal (2 * A ^ 2) from rfl,
      ← ENNReal.ofReal_mul hCnn]
    have hreal : (2 * A ^ 2) * δ = (ε : ℝ) := by
      dsimp [δ]
      field_simp
    rw [hreal]
    exact ENNReal.ofReal_coe_nnreal
  calc
    D' (z, w) = D' (P 0, P 1) := by rw [hP0, hP1]
    _ ≤ C * D.len P 0 1 := hpath
    _ ≤ C * (D (z, w) + ENNReal.ofReal δ) := by gcongr
    _ = C * D (z, w) + ε := by rw [mul_add, hCδ]


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators
