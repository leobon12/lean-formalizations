import QuantumZipper.Proofs.Section5.Prop16Area

/-!
# Proposition 1.6, D4-a′ (part 1): a Slutsky-type lemma for bounded continuous functionals

Decision D24 (`DECISIONS.md`). `tendsto_integral_sub_of_close`: if `V c, W c : Ω → ℝᵐ` are
a.e.-measurable, `V c` is tight (uniformly in large `c`), and `W c − V c → 0` in probability
coordinatewise, then `∫ F(W c) − ∫ F(V c) → 0` for every bounded continuous `F`.

This is the elementary half of Slutsky's theorem (Billingsley, *Convergence of Probability
Measures*, 2nd ed., Theorem 3.1: if `X_n ⇒ X` and `d(X_n, Y_n) → 0` in probability then
`Y_n ⇒ X`), proved here directly for a fixed bounded continuous `F`: `F` is uniformly continuous
on a large closed ball (Heine–Cantor), and the complement of "`V` in the ball and `W` close to `V`"
has small probability. Standard argument, written out (own elementary proof, AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

theorem tendsto_integral_sub_of_close {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hF : Continuous F) {B : ℝ}
    (hB : ∀ v, |F v| ≤ B) (V W : ℝ → Ω → Fin m → ℝ) (hV : ∀ c, AEMeasurable (V c) P)
    (hW : ∀ᶠ c in atTop, AEMeasurable (W c) P)
    (htight : ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, ∀ᶠ c in atTop, P {ω | M < ‖V c ω‖} < η)
    (hclose : ∀ j, ∀ δ > 0, Tendsto (fun c => P {ω | δ < |W c ω j - V c ω j|}) atTop (𝓝 0)) :
    Tendsto (fun c => ∫ ω, F (W c ω) ∂P - ∫ ω, F (V c ω) ∂P) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set B' := max B 1 with hB'
  have hB'0 : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hFB : ∀ v, |F v| ≤ B' := fun v => (hB v).trans (le_max_left _ _)
  have hη : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / (8 * B')) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨M, hM⟩ := htight _ hη
  have hK : IsCompact (Metric.closedBall (0 : Fin m → ℝ) (|M| + 1)) := isCompact_closedBall _ _
  obtain ⟨δ, hδ, hUC⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hF.continuousOn) (ε / 4) (by positivity)
  set δ' := min (δ / 2) 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min (by positivity) one_pos
  have hη' : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / (8 * B' * (m + 1))) :=
    ENNReal.ofReal_pos.2 (by positivity)
  have hcl : ∀ᶠ c in atTop, ∀ j, P {ω | δ' < |W c ω j - V c ω j|} <
      ENNReal.ofReal (ε / (8 * B' * (m + 1))) :=
    eventually_all.2 fun j => (hclose j δ' hδ'0).eventually (gt_mem_nhds hη')
  filter_upwards [hM, hcl, hW] with c hMc hclc hWc
  -- the bad set
  set S : Set Ω := {ω | M < ‖V c ω‖} ∪ ⋃ j, {ω | δ' < |W c ω j - V c ω j|} with hS
  have hPS : P S ≤ ENNReal.ofReal (ε / (4 * B')) := by
    calc P S ≤ P {ω | M < ‖V c ω‖} + ∑ j, P {ω | δ' < |W c ω j - V c ω j|} :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
      _ ≤ ENNReal.ofReal (ε / (8 * B')) + ∑ _j : Fin m, ENNReal.ofReal (ε / (8 * B' * (m + 1))) :=
          add_le_add hMc.le (Finset.sum_le_sum fun j _ => (hclc j).le)
      _ ≤ ENNReal.ofReal (ε / (8 * B')) + ENNReal.ofReal (ε / (8 * B')) := by
          gcongr
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          have : (0 : ℝ) ≤ ε * (8 * B') := by positivity
          nlinarith
      _ = ENNReal.ofReal (ε / (4 * B')) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; field_simp; ring
  set T := toMeasurable P S
  have hgood : ∀ ω ∉ S, |F (W c ω) - F (V c ω)| < ε / 4 := by
    intro ω hω
    simp only [hS, mem_union, mem_ofPred_eq, mem_iUnion, not_or, not_exists, not_lt] at hω
    have hV1 : V c ω ∈ Metric.closedBall (0 : Fin m → ℝ) (|M| + 1) := by
      rw [mem_closedBall_zero_iff]; linarith [le_abs_self M, hω.1]
    have hWV : ‖W c ω - V c ω‖ ≤ δ' :=
      (pi_norm_le_iff_of_nonneg hδ'0.le).2 fun j => by
        rw [Pi.sub_apply, Real.norm_eq_abs]; exact hω.2 j
    have hW1 : W c ω ∈ Metric.closedBall (0 : Fin m → ℝ) (|M| + 1) := by
      rw [mem_closedBall_zero_iff]
      calc ‖W c ω‖ = ‖(W c ω - V c ω) + V c ω‖ := by rw [sub_add_cancel]
        _ ≤ ‖W c ω - V c ω‖ + ‖V c ω‖ := norm_add_le _ _
        _ ≤ 1 + |M| := add_le_add (hWV.trans (min_le_right _ _)) (hω.1.trans (le_abs_self M))
        _ = |M| + 1 := add_comm _ _
    have hd : dist (W c ω) (V c ω) < δ := by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hWV.trans (min_le_left _ _)) (by linarith)
    have := hUC _ hW1 _ hV1 hd
    rwa [Real.dist_eq] at this
  have hAi : Integrable (fun ω => F (W c ω)) P :=
    Integrable.of_bound (hF.measurable.comp_aemeasurable hWc).aestronglyMeasurable B'
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFB _)
  have hBi : Integrable (fun ω => F (V c ω)) P :=
    Integrable.of_bound (hF.measurable.comp_aemeasurable (hV c)).aestronglyMeasurable B'
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFB _)
  have hTi : Integrable (T.indicator fun _ => 2 * B') P :=
    (integrable_const (2 * B')).indicator (measurableSet_toMeasurable _ _)
  rw [Real.dist_eq, sub_zero, ← integral_sub hAi hBi, ← Real.norm_eq_abs]
  have hbound : ‖∫ ω, (F (W c ω) - F (V c ω)) ∂P‖ ≤
      ∫ ω, (ε / 4 + T.indicator (fun _ => 2 * B') ω) ∂P := by
    refine norm_integral_le_of_norm_le ((integrable_const _).add hTi)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    by_cases hω : ω ∈ T
    · rw [indicator_of_mem hω]
      have h1 := hFB (W c ω)
      have h2 := hFB (V c ω)
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
    · rw [indicator_of_notMem hω]
      have := hgood ω fun h => hω (subset_toMeasurable _ _ h)
      linarith
  refine lt_of_le_of_lt hbound ?_
  rw [integral_add (integrable_const _) hTi, integral_const, integral_indicator_const _
    (measurableSet_toMeasurable _ _)]
  simp only [Measure.real, measure_toMeasurable, measure_univ, ENNReal.toReal_one,
    smul_eq_mul]
  have hT : (P S).toReal ≤ ε / (4 * B') := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hPS
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have : (P S).toReal * (2 * B') ≤ ε / 2 := by
    calc (P S).toReal * (2 * B') ≤ ε / (4 * B') * (2 * B') :=
          mul_le_mul_of_nonneg_right hT (by positivity)
      _ = ε / 2 := by field_simp; ring
  linarith

end Prop16Area

end QuantumZipper
