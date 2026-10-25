import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments.DyadicPaid
import SLUMetricAPI2




 




set_option autoImplicit false
noncomputable section

open Set Metric Filter LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments

 

theorem dyadic_paid_endpoint_curve
    (D : LSCMetric) (w : ℂ) (hw : w ≠ 0)
    (K : ℕ × Bool → Set ℂ)
    (P : ℕ × Bool → ℝ → ℂ) (a b : ℕ × Bool → ℝ)
    (hcurve : ∀ i, D.IsCurve (P i) (a i) (b i))
    (hEucl : ∀ i, ContinuousOn (P i) (Icc (a i) (b i)))
    (htrace : ∀ i, K i = P i '' Icc (a i) (b i))
    (hfinite : ∀ i, D.len (P i) (a i) (b i) < ∞)
    (hcompact : ∀ i, IsCompact (K i))
    (hann : ∀ i, K i ⊆ {z | Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 <
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) < Objects.BoundaryUnionDyadic.dyadicOuter w i})
    (hsep : ∀ i, LQGMetric.Disconnects (K i)
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2))
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i)))
    (hcost : (∑' i : ℕ × Bool, D.len (P i) (a i) (b i)) ≠ ∞) :
    ∃ Q : C(unitInterval, ℂ),
      Q 0 = 0 ∧ Q 1 = w ∧ (∀ t, Q t ∈ closedBall 0 ‖w‖) ∧
      D.IsCurve (fun t => Q (projIcc 0 1 zero_le_one t)) 0 1 ∧
      D.len (fun t => Q (projIcc 0 1 zero_le_one t)) 0 1 ≤
        ∑' i : ℕ × Bool, D.len (P i) (a i) (b i) := by
  classical
  let q : ℕ → ℝ := fun n => Objects.BoundaryUnionDyadic.dyadicQ (n + 1)
  have hq : Tendsto q atTop (nhds 0) := by
    have hp : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    change Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ ((n + 1) + 1)) atTop (nhds 0)
    exact hp.comp ((tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat 1))
  have hqpos (n : ℕ) : 0 < q n := by
    dsimp [q, Objects.BoundaryUnionDyadic.dyadicQ]
    positivity
  have hqhalf (n : ℕ) : q n ≤ 1 / 2 := by
    dsimp [q, Objects.BoundaryUnionDyadic.dyadicQ]
    rw [pow_succ]
    have hp := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := n + 1)
    nlinarith only [hp]
  have hfinitePath (n : ℕ) := finite_dyadic_paid_path D w hw K P a b
    hcurve hEucl htrace hfinite hcompact hann hsep
    (hqpos n) (by linarith [hqhalf n] : q n ≤ 1 - q n)
    (by linarith [hqpos n] : 1 - q n < 1)
  choose i j x y hi hj hxi hyj γ hγrange hγlen using hfinitePath
  have hleft : Tendsto (fun n => q n • w) atTop (nhds 0) := by
    have hc : Continuous (fun z : ℝ => z • w) := continuous_id.smul continuous_const
    simpa only [Function.comp_def, zero_smul] using (hc.tendsto 0).comp hq
  have hright : Tendsto (fun n => (1 - q n) • w) atTop (nhds w) := by
    have hc : Continuous (fun z : ℝ => (1 - z) • w) :=
      (continuous_const.sub continuous_id).smul continuous_const
    simpa only [Function.comp_def, sub_zero, one_smul] using (hc.tendsto 0).comp hq
  have hx : Tendsto x atTop (nhds 0) :=
    selected_left_trace_tendsto w hw K hcompact hann hsep
      (fun n => q n • w) x i hleft hi hxi
  have hy : Tendsto y atTop (nhds w) :=
    selected_right_trace_tendsto w hw K hcompact hann hsep
      (fun n => (1 - q n) • w) y j hright hj hyj
  let R : ℕ → ℝ → ℂ := fun n t =>
    (γ n (projIcc 0 1 zero_le_one t) : ℂ)
  have hRcurve : ∀ n, D.IsCurve (R n) 0 1 := by
    intro n
    refine ⟨zero_le_one, ?_⟩
    exact ((γ n).continuous.comp continuous_projIcc).continuousOn
  have hRtrace : ∀ n t, t ∈ Icc (0 : ℝ) 1 → R n t ∈ closedBall 0 ‖w‖ := by
    intro n t _
    have h := hγrange n (Set.mem_range_self (projIcc 0 1 zero_le_one t))
    obtain ⟨z, hz, hzeq⟩ := h
    change (γ n (projIcc 0 1 zero_le_one t) : ℂ) ∈
      Metric.closedBall (0 : ℂ) ‖w‖
    have hpoint : (γ n (projIcc 0 1 zero_le_one t) : ℂ) = z := by
      simpa [LSCMetric.pt, LSCMetric.Space] using hzeq.symm
    rw [hpoint]
    exact hz
  have hRlen : ∀ n, D.len (R n) 0 1 ≤
      ∑' i : ℕ × Bool, D.len (P i) (a i) (b i) := by
    intro n
    change pathLength (γ n) ≤ _
    exact hγlen n
  have hRstart : Tendsto (fun n => R n 0) atTop (nhds 0) := by
    have heq : (fun n => R n 0) = x := by
      funext n
      simpa [R, LSCMetric.pt, LSCMetric.Space] using (γ n).source
    rw [heq]
    exact hx
  have hRend : Tendsto (fun n => R n 1) atTop (nhds w) := by
    have heq : (fun n => R n 1) = y := by
      funext n
      simpa [R, LSCMetric.pt, LSCMetric.Space] using (γ n).target
    rw [heq]
    exact hy
  obtain ⟨_, _, Q, _, _, _, hQ0, hQ1, hQK, hQc, hQl⟩ :=
    Toolkit.PaidPathCompactness.boundedPaidPaths_compact D (isCompact_closedBall 0 ‖w‖)
      R (fun _ => 0) (fun _ => 1) hRcurve hRtrace hcost hRlen hRstart hRend
  exact ⟨Q, hQ0, hQ1, hQK, hQc, hQl⟩

 
theorem dyadic_internal_le_sum
    (D : LSCMetric) (w : ℂ) (hw : w ≠ 0)
    (K : ℕ × Bool → Set ℂ)
    (P : ℕ × Bool → ℝ → ℂ) (a b : ℕ × Bool → ℝ)
    (hcurve : ∀ i, D.IsCurve (P i) (a i) (b i))
    (hEucl : ∀ i, ContinuousOn (P i) (Icc (a i) (b i)))
    (htrace : ∀ i, K i = P i '' Icc (a i) (b i))
    (hfinite : ∀ i, D.len (P i) (a i) (b i) < ∞)
    (hcompact : ∀ i, IsCompact (K i))
    (hann : ∀ i, K i ⊆ {z | Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 <
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) < Objects.BoundaryUnionDyadic.dyadicOuter w i})
    (hsep : ∀ i, LQGMetric.Disconnects (K i)
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2))
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i)))
    (hcost : (∑' i : ℕ × Bool, D.len (P i) (a i) (b i)) ≠ ∞) :
    D.internal (closedBall 0 ‖w‖)
      (⟨w, by simp only [mem_closedBall, dist_zero_right, le_refl]⟩,
       ⟨0, mem_closedBall_self (norm_nonneg w)⟩) ≤
      ∑' i : ℕ × Bool, D.len (P i) (a i) (b i) := by
  let Y : Set ℂ := closedBall 0 ‖w‖
  obtain ⟨Q, hQ0, hQ1, hQY, hQc, hQl⟩ :=
    dyadic_paid_endpoint_curve D w hw K P a b hcurve hEucl htrace hfinite
      hcompact hann hsep hcost
  let C : ℝ → ℂ := fun t => Q (projIcc 0 1 zero_le_one t)
  have h0Y : (0 : ℂ) ∈ Y := mem_closedBall_self (norm_nonneg w)
  have hwY : w ∈ Y := by
    change dist w 0 ≤ ‖w‖
    rw [dist_zero_right]
  have hC0 : C 0 = 0 := by simpa [C] using hQ0
  have hC1 : C 1 = w := by simpa [C] using hQ1
  have hCY : ∀ t ∈ Icc (0 : ℝ) 1, C t ∈ Y := fun t _ => hQY _
  have hI : D.internal Y
      (⟨(0 : ℂ), h0Y⟩, ⟨w, hwY⟩) ≤
      D.len C 0 1 := by
    unfold LSCMetric.internal
    exact iInf_le_of_le C <| iInf_le_of_le 0 <| iInf_le_of_le 1 <|
      iInf_le_of_le hQc <| iInf_le_of_le hCY <|
      iInf_le_of_le hC0 <| iInf_le_of_le hC1 le_rfl
  have hsym := (D.isExtMetric_internal Y).2.2.1
    (⟨w, hwY⟩ : Y) (⟨(0 : ℂ), h0Y⟩ : Y)
  change D.internal Y _ ≤ _
  rw [hsym]
  exact hI.trans hQl

end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments
