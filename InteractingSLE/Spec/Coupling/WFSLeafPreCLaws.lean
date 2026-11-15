/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafPreCStop
import InteractingSLE.Spec.Exist.FlowField

/-!
# Cofinality transfer and the zero-cutoff case

Cofinality is a Borel property of a sequence of history rules, so equality of
the driving marginal transfers it to the reference. A Galmarino rule that takes
value zero on one continuous killed history takes value zero on every such
history. This separates the trivial zero cutoff from strictly positive cutoffs.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- Cofinality and the prefix bounds transfer solely by the history marginal. -/
theorem ae_rule_cofinal_of_map_eq
    {nL nR : ℕ} {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    {P : Measure Ω} {P₀ : Measure Ω₀} {Y : Ω → HistorySpace nL nR}
    {Y₀ : Ω₀ → HistorySpace nL nR} (hY : Measurable Y) (hY₀ : Measurable Y₀)
    (hlaw : P.map Y = P₀.map Y₀) {Q : ℕ → HistorySpace nL nR → ℝ≥0∞}
    (hQ : ∀ n, Measurable (Q n))
    (ha : ∀ᵐ ω ∂P, (∀ n, Q n (Y ω) ≤ (Y ω).1) ∧
      Tendsto (fun n => Q n (Y ω)) atTop (𝓝 (Y ω).1)) :
    ∀ᵐ ω ∂P₀, (∀ n, Q n (Y₀ ω) ≤ (Y₀ ω).1) ∧
      Tendsto (fun n => Q n (Y₀ ω)) atTop (𝓝 (Y₀ ω).1) := by
  have hm : MeasurableSet {γ : HistorySpace nL nR | (∀ n, Q n γ ≤ γ.1) ∧
      Tendsto (fun n => Q n γ) atTop (𝓝 γ.1)} := by
    simpa only [ofPred_and, ofPred_forall] using
      (MeasurableSet.iInter fun n => measurableSet_le (hQ n) measurable_fst).inter
        (measurableSet_tendsto_fun (l := atTop) hQ measurable_fst)
  have hb := (ae_map_iff hY.aemeasurable hm).2 ha
  rw [hlaw] at hb
  exact (ae_map_iff hY₀.aemeasurable hm).1 hb

/-- A Galmarino rule vanishing on one continuous killed history vanishes on
all continuous killed histories. No initial-state condition is needed. -/
theorem rule_eq_zero_of_exists_zero {nL nR : ℕ} {R : HistorySpace nL nR → ℝ≥0∞}
    (hR : IsHistGalmarino R)
    (hz : ∃ γ, IsKilledContHist γ ∧ R γ = 0)
    {δ : HistorySpace nL nR} (hδ : IsKilledContHist δ) : R δ = 0 := by
  obtain ⟨γ, hγ, h0⟩ := hz
  have he := hR γ δ hγ hδ (by rw [h0]; exact bot_le) (by rw [h0]; exact bot_le)
    (fun p hp => (not_lt_of_ge bot_le (h0 ▸ hp)).elim)
  exact he.trans h0

/-- An own-history Galmarino cutoff is almost surely zero or almost surely
strictly positive, even if its ambient probability space is not complete. -/
theorem ae_zero_or_ae_pos_of_selfRule
    {nL nR : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → HistorySpace nL nR} {R : HistorySpace nL nR → ℝ≥0∞}
    (hR : IsHistGalmarino R) (hc : ∀ᵐ ω ∂P, IsKilledContHist (Y ω))
    (hself : ∀ᵐ ω ∂P, (Y ω).1 = R (Y ω)) :
    (∀ᵐ ω ∂P, (Y ω).1 = 0) ∨ (∀ᵐ ω ∂P, 0 < (Y ω).1) := by
  classical
  by_cases hz : ∃ γ, IsKilledContHist γ ∧ R γ = 0
  · left
    filter_upwards [hc, hself] with ω hc hs
    exact hs.trans (rule_eq_zero_of_exists_zero hR hz hc)
  · right
    filter_upwards [hc, hself] with ω hc hs
    exact pos_iff_ne_zero.2 fun h0 => hz ⟨Y ω, hc, hs.symm.trans h0⟩

/-- Constant recorded histories add no information to the field law. -/
theorem map_pair_eq_of_ae_const
    {Ω Ω₀ Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] [MeasurableSpace Γ]
    {P : Measure Ω} {P₀ : Measure Ω₀}
    {h : Ω → DistOn upperHalfPlaneOpens} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) (hh₀ : Measurable h₀) (hlaw : P.map h = P₀.map h₀)
    {Y : Ω → Γ} {Y₀ : Ω₀ → Γ} {c : Γ} (hc : Y =ᵐ[P] fun _ => c)
    (hc₀ : Y₀ =ᵐ[P₀] fun _ => c) :
    P.map (fun ω => (h ω, Y ω)) = P₀.map (fun ω => (h₀ ω, Y₀ ω)) := by
  calc
    P.map (fun ω => (h ω, Y ω)) = P.map (fun ω => (h ω, c)) :=
      Measure.map_congr (hc.mono fun _ he => Prod.ext rfl he)
    _ = (P.map h).map (fun f => (f, c)) := (Measure.map_map
      (measurable_id.prodMk measurable_const) hh).symm
    _ = (P₀.map h₀).map (fun f => (f, c)) := by rw [hlaw]
    _ = P₀.map (fun ω => (h₀ ω, c)) := Measure.map_map
      (measurable_id.prodMk measurable_const) hh₀
    _ = P₀.map (fun ω => (h₀ ω, Y₀ ω)) :=
      Measure.map_congr (hc₀.mono fun _ he => Prod.ext rfl he.symm)

end InteractingSLE.WFS
