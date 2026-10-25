import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaNoLongLoop
import LQGMetric.Metric.CurveNatural

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_unit_speed_buffered_curve
    (D : LSCMetric) {V : Set ℂ} {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b)
    (hV : ∀ u ∈ Icc a b, P u ∈ V)
    (hfinite : D.len P a b ≠ ∞) :
    ∃ Q : ℝ → ℂ,
      D.IsCurve Q 0 (D.len P a b).toReal ∧
      HasUnitSpeedOn (D.pt ∘ Q) (Icc 0 (D.len P a b).toReal) ∧
      Q 0 = P a ∧ Q (D.len P a b).toReal = P b ∧
      (∀ u ∈ Icc 0 (D.len P a b).toReal, Q u ∈ V) ∧
      D.len Q 0 (D.len P a b).toReal = D.len P a b := by
  obtain ⟨γ, hγlen, hγrange⟩ :=
    LQGMetric.MetricGeometry.exists_path_of_curve hP.1 hP.2
  have hγfin : LQGMetric.MetricGeometry.pathLength γ ≠ ∞ := by
    rw [hγlen]
    exact hfinite
  obtain ⟨Q, hunit, hcont, hQ0, hQL, hQrange⟩ :=
    LQGMetric.MetricGeometry.exists_unitSpeed_of_path γ hγfin
  let Qc : ℝ → ℂ := Q
  have hL : LQGMetric.MetricGeometry.pathLength γ = D.len P a b := hγlen
  have hQcurve : D.IsCurve Qc 0 (D.len P a b).toReal := by
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    change ContinuousOn Q (Icc 0 (D.len P a b).toReal)
    rw [← hL]
    exact hcont
  have hQunit : HasUnitSpeedOn (D.pt ∘ Qc)
      (Icc 0 (D.len P a b).toReal) := by
    change HasUnitSpeedOn Q (Icc 0 (D.len P a b).toReal)
    rw [← hL]
    exact hunit
  have hQ0' : Qc 0 = P a := hQ0
  have hQL' : Qc (D.len P a b).toReal = P b := by
    change Q (D.len P a b).toReal = (D.pt ∘ P) b
    rw [← hL]
    exact hQL
  have hQV : ∀ u ∈ Icc 0 (D.len P a b).toReal, Qc u ∈ V := by
    intro u hu
    have hu' : u ∈ Icc 0 (LQGMetric.MetricGeometry.pathLength γ).toReal := by
      simpa only [hL] using hu
    obtain ⟨v, hv⟩ := hQrange u hu'
    obtain ⟨t, ht, hγt⟩ := hγrange ⟨v, hv⟩
    have hQt : Qc u = P t := by
      change Q u = (D.pt ∘ P) t
      exact hγt.symm
    rw [hQt]
    exact hV t ht
  have hQlen : D.len Qc 0 (D.len P a b).toReal = D.len P a b := by
    have h0 : (0 : ℝ) ∈ Icc 0 (D.len P a b).toReal :=
      ⟨le_rfl, ENNReal.toReal_nonneg⟩
    have h1 : (D.len P a b).toReal ∈ Icc 0 (D.len P a b).toReal :=
      ⟨ENNReal.toReal_nonneg, le_rfl⟩
    change LQGMetric.MetricGeometry.curveLength (D.pt ∘ Qc) 0
      (D.len P a b).toReal = D.len P a b
    rw [LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hQunit h0 h1]
    simp only [sub_zero, ENNReal.ofReal_toReal hfinite]
  exact ⟨Qc, hQcurve, hQunit, hQ0', hQL', hQV, hQlen⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
