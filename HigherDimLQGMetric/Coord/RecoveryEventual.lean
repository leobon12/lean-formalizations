import HigherDimLQGMetric.Coord.ConfinedLimit

/-! # Eventual path recovery under uniformly converging coordinates -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

/-- A fixed competitor has quantitative recoveries for every sufficiently
large approximating coordinate. -/
theorem lemma24_eventual_recovery
    {X : Type*} [MetricSpace X]
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsCoordinate (ρ n)) (hρlim : IsCoordinate ρlim)
    (w : X → ℝ) {K O : Set X} (hKO : K ⊆ closure O)
    (hconv : TendstoUniformlyOn ρ ρlim atTop (closure O ×ˢ closure O))
    {L δ δloc χ Ω M : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hδloc : 2 * δ < δloc) (hχ : 0 ≤ χ) (hΩ : 0 ≤ Ω) (hΩM : Ω ≤ M)
    (hmodlim : ∀ u ∈ closure O, ∀ v ∈ closure O,
      ρlim (u, v) ≤ 2 * δ → dist u v ≤ χ)
    (hmod : ∀ n, ∀ u ∈ closure O, ∀ v ∈ closure O,
      ρ n (u, v) ≤ 2 * δ → dist u v ≤ χ)
    (hw : ∀ z ∈ closure O, 0 ≤ w z ∧ w z ≤ M)
    (hwosc : ∀ u ∈ closure O, ∀ v ∈ closure O,
      dist u v ≤ χ → |w u - w v| ≤ Ω)
    (hlocal : ∀ n, ∀ x ∈ K, ∀ y ∈ K, ρ n (x, y) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧ R 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ n (x, y)))
    (Q : I →ᵇ X) (hQK : ∀ t, Q t ∈ K)
    (hQlen : curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
      (Set.IccExtend zero_le_one Q) 0 1 ≤ ENNReal.ofReal L)
    {e : ℝ} (he : 0 < e) (heδ : e ≤ δ) :
    ∀ᶠ n in atTop,
      weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
          (closure O) (Q 0) (Q 1) ≤
        weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
          (Set.IccExtend zero_le_one Q) 0 1 +
          ENNReal.ofReal (2 * Ω * L + 2 * M * (L / δ + 1) * e) := by
  have hclose : ∀ᶠ n in atTop, ∀ u ∈ closure O, ∀ v ∈ closure O,
      |ρlim (u, v) - ρ n (u, v)| ≤ e := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv
    filter_upwards [hconv e he] with n hn u hu v hv
    have h := hn (u, v) ⟨hu, hv⟩
    rw [Real.dist_eq] at h
    simpa [abs_sub_comm] using h.le
  filter_upwards [hclose] with n hn
  obtain ⟨old, new, -, hNewO, -, hweighted, -⟩ :=
    lemma24 ρlim (ρ n) hρlim (hρ n) w hKO hL hδ he.le heδ hδloc
      hχ hΩ hΩM Q hQK hQlen hn hmodlim (hmod n) hw hwosc (hlocal n)
  have hdist := weylDistOnWith_le
    (E := fun u v => ENNReal.ofReal (ρ n (u, v)))
    (w := w) (S := closure O) (x := Q 0) (y := Q 1)
    (P := new.extend) new.continuous_extend.continuousOn
    new.extend_zero new.extend_one (fun t ht => by
      rw [Path.extend_apply new ht]
      exact hNewO ⟨t, ht⟩)
  exact hdist.trans hweighted

end HigherDimLQGMetric
