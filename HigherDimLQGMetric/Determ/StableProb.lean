import HigherDimLQGMetric.B3.Interfaces
import LQGMetric.Papers.DFGPS.L1_3

/-!
# A stable-convergence form of DFGPS Lemma 1.3

The product-test definition of stable convergence is already strong enough for the
partition argument in the proof of DFGPS Lemma 1.3. This form avoids an
unnecessary conversion to joint weak convergence on a topology for distributions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

/-- Stable product tests and a measurable limiting factor give convergence in measure. -/
theorem determ_tendstoInMeasure_of_stable
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MetricSpace β] [MeasurableSpace β] [BorelSpace β]
    [TopologicalSpace.SeparableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → α) (Y : Ω → β) (Yn : ℕ → Ω → β)
    (hX : Measurable X) (hYn : ∀ n, Measurable (Yn n))
    (hstable : ∀ F : α → ℝ, Measurable F → (∃ C, ∀ x, |F x| ≤ C) →
      ∀ Θ : β → ℝ, Continuous Θ → (∃ C, ∀ y, |Θ y| ≤ C) →
        Tendsto (fun n => ∫ ω, F (X ω) * Θ (Yn n ω) ∂P) atTop
          (𝓝 (∫ ω, F (X ω) * Θ (Y ω) ∂P)))
    (hdet : LQGMetric.AEDeterminedBy Y X P) :
    TendstoInMeasure P Yn atTop Y := by
  obtain ⟨f, hf, hYf⟩ := hdet
  have hstable' : ∀ F : α → ℝ, Measurable F → (∃ C, ∀ x, |F x| ≤ C) →
      ∀ Θ : β → ℝ, Continuous Θ → (∃ C, ∀ y, |Θ y| ≤ C) →
        Tendsto (fun n => ∫ ω, F (X ω) * Θ (Yn n ω) ∂P) atTop
          (𝓝 (∫ ω, F (X ω) * Θ (f (X ω)) ∂P)) := by
    intro F hF hFb Θ hΘ hΘb
    have heq : (∫ ω, F (X ω) * Θ (Y ω) ∂P) =
        ∫ ω, F (X ω) * Θ (f (X ω)) ∂P :=
      integral_congr_ae (hYf.mono fun ω hω => by simp only [hω, Function.comp_apply])
    rw [← heq]
    exact hstable F hF hFb Θ hΘ hΘb
  have key : Tendsto (fun n => ∫ ω, min 1 (dist (Yn n ω) (f (X ω))) ∂P)
      atTop (𝓝 0) := by
    rcases isEmpty_or_nonempty β with hβ | hβ
    · have : IsEmpty Ω := ⟨fun ω => hβ.elim (f (X ω))⟩
      exact absurd (Measure.eq_zero_of_isEmpty P) (IsProbabilityMeasure.ne_zero P)
    obtain ⟨b, hb⟩ := TopologicalSpace.exists_dense_seq β
    have hfX : Measurable fun ω => f (X ω) := hf.comp hX
    have hnn : ∀ n ω, 0 ≤ min 1 (dist (Yn n ω) (f (X ω))) := fun _ _ =>
      le_min zero_le_one dist_nonneg
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
      ha.trans_le (integral_nonneg (hnn n)), fun a ha => ?_⟩
    set δ : ℝ := a / 5 with hδdef
    have hδ : 0 < δ := by positivity
    let E : ℕ → Set Ω := fun K => {ω | ∀ j < K, δ ≤ dist (f (X ω)) (b j)}
    have hEm : ∀ K, MeasurableSet (E K) := fun K =>
      hX (LQGMetric.DFGPS.L13.measurableSet_tail hf b δ K)
    have hEanti : Antitone E := fun K L hKL ω hω j hj => hω j (lt_of_lt_of_le hj hKL)
    have hEempty : (⋂ K, E K) = ∅ := by
      ext ω
      simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 hb (f (X ω)) δ hδ
      exact ⟨j + 1, fun h => absurd (h j (Nat.lt_succ_self j)) (not_le.2 hj)⟩
    have htail : Tendsto (fun K => P (E K)) atTop (𝓝 0) := by
      have ht := tendsto_measure_iInter_atTop (μ := P)
        (fun K => (hEm K).nullMeasurableSet) hEanti ⟨0, measure_ne_top P _⟩
      rwa [hEempty, measure_empty] at ht
    obtain ⟨K, hK⟩ := (htail.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ))).exists
    have hKr : P.real (E K) < δ := by
      rw [measureReal_def]
      exact (ENNReal.toReal_lt_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).2 hK |>.trans_le
        (ENNReal.toReal_ofReal hδ.le).le
    let A : ℕ → Set α := fun k =>
      {x | dist (f x) (b k) < δ ∧ ∀ j < k, δ ≤ dist (f x) (b j)}
    let F : ℕ → α → ℝ := fun k => (A k).indicator fun _ => (1 : ℝ)
    let Θ : ℕ → β → ℝ := fun k y => min 1 (dist y (b k))
    have hFm : ∀ k, Measurable (F k) := fun k =>
      measurable_const.indicator (LQGMetric.DFGPS.L13.measurableSet_piece hf b δ k)
    have hFb : ∀ k x, |F k x| ≤ 1 := fun k x => by
      simp only [F, Set.indicator]; split_ifs <;> simp
    have hΘc : ∀ k, Continuous (Θ k) := fun k =>
      continuous_const.min (continuous_id.dist continuous_const)
    have hΘb : ∀ k y, |Θ k y| ≤ 1 := fun k y => by
      rw [abs_of_nonneg (le_min zero_le_one dist_nonneg)]; exact min_le_left _ _
    have hint : ∀ k (Z : Ω → β), Measurable Z →
        Integrable (fun ω => F k (X ω) * Θ k (Z ω)) P :=
      fun k Z hZ => LQGMetric.DFGPS.L217.integrable_of_abs_le
        (((hFm k).comp hX).mul ((hΘc k).measurable.comp hZ))
        (C := 1) fun ω => by
          rw [abs_mul]
          nlinarith [hFb k (X ω), hΘb k (Z ω), abs_nonneg (F k (X ω)),
            abs_nonneg (Θ k (Z ω))]
    have hlim : Tendsto
        (fun n => ∑ k ∈ Finset.range K, ∫ ω, F k (X ω) * Θ k (Yn n ω) ∂P) atTop
        (𝓝 (∑ k ∈ Finset.range K, ∫ ω, F k (X ω) * Θ k (f (X ω)) ∂P)) :=
      tendsto_finsetSum _ fun k _ =>
        hstable' (F k) (hFm k) ⟨1, hFb k⟩ (Θ k) (hΘc k) ⟨1, hΘb k⟩
    have hlimle : (∑ k ∈ Finset.range K, ∫ ω, F k (X ω) * Θ k (f (X ω)) ∂P) ≤ δ := by
      rw [← integral_finsetSum _ fun k _ => hint k _ hfX]
      calc _ ≤ ∫ _ : Ω, δ ∂P := integral_mono_of_nonneg
              (Eventually.of_forall fun ω => Finset.sum_nonneg fun k _ =>
                mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
                  (le_min zero_le_one dist_nonneg))
              (integrable_const δ) (Eventually.of_forall fun ω =>
                LQGMetric.DFGPS.L13.sum_le_delta hδ.le K (X ω))
        _ = δ := by simp
    have hev : ∀ᶠ n in atTop,
        (∑ k ∈ Finset.range K, ∫ ω, F k (X ω) * Θ k (Yn n ω) ∂P) < 2 * δ :=
      hlim.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hev] with n hn
    have hbound : ∀ ω, min 1 (dist (Yn n ω) (f (X ω))) ≤
        (∑ k ∈ Finset.range K, F k (X ω) * Θ k (Yn n ω)) + δ +
          (E K).indicator (fun _ => (1 : ℝ)) ω := fun ω => by
      have hh := LQGMetric.DFGPS.L13.min_dist_le_sum (f := f) (b := b) hδ.le K (X ω) (Yn n ω)
      simpa [E, Set.indicator, F, A, Θ] using hh
    have hIE : Integrable ((E K).indicator fun _ => (1 : ℝ)) P :=
      (integrable_const (1 : ℝ)).indicator (hEm K)
    have hIS : Integrable (fun ω => ∑ k ∈ Finset.range K, F k (X ω) * Θ k (Yn n ω)) P :=
      integrable_finsetSum _ fun k _ => hint k _ (hYn n)
    have hISd : Integrable (fun ω => (∑ k ∈ Finset.range K, F k (X ω) * Θ k (Yn n ω)) + δ) P :=
      hIS.add (integrable_const δ)
    calc ∫ ω, min 1 (dist (Yn n ω) (f (X ω))) ∂P
        ≤ ∫ ω, ((∑ k ∈ Finset.range K, F k (X ω) * Θ k (Yn n ω)) + δ +
            (E K).indicator (fun _ => (1 : ℝ)) ω) ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall (hnn n))
            (hISd.add hIE) (Eventually.of_forall hbound)
      _ = (∑ k ∈ Finset.range K, ∫ ω, F k (X ω) * Θ k (Yn n ω) ∂P) + δ + P.real (E K) := by
          rw [integral_add hISd hIE, integral_add hIS (integrable_const δ),
            integral_finsetSum _ fun k _ => hint k _ (hYn n)]
          simp [integral_indicator (hEm K), measureReal_def]
      _ < a := by linarith
  refine TendstoInMeasure.congr_right (g := fun ω => f (X ω))
    (hYf.mono fun ω hω => hω.symm) ?_
  refine tendstoInMeasure_of_ne_top fun ε hε hεt => ?_
  set e : ℝ := min 1 ε.toReal with he
  have hepos : 0 < e := lt_min one_pos (ENNReal.toReal_pos hε.ne' hεt)
  have hint : ∀ n, Integrable (fun ω => min 1 (dist (Yn n ω) (f (X ω)))) P := fun n =>
    LQGMetric.DFGPS.L217.integrable_of_abs_le
      (measurable_const.min ((hYn n).dist (hf.comp hX))) (C := 1) fun ω => by
        rw [abs_of_nonneg (le_min zero_le_one dist_nonneg)]; exact min_le_left _ _
  have hle : ∀ n, P {ω | ε ≤ edist (Yn n ω) (f (X ω))} ≤
      ENNReal.ofReal ((∫ ω, min 1 (dist (Yn n ω) (f (X ω))) ∂P) / e) := fun n => by
    have hsub : {ω | ε ≤ edist (Yn n ω) (f (X ω))} ⊆
        {ω | e ≤ min 1 (dist (Yn n ω) (f (X ω)))} := fun ω hω => by
      have h1 : ε.toReal ≤ dist (Yn n ω) (f (X ω)) := by
        change ε ≤ edist (Yn n ω) (f (X ω)) at hω
        rw [edist_dist] at hω
        exact ENNReal.toReal_le_of_le_ofReal dist_nonneg hω
      exact min_le_min_left _ h1
    have hM := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Eventually.of_forall fun ω => le_min zero_le_one dist_nonneg) (hint n) e
    calc _ ≤ P {ω | e ≤ min 1 (dist (Yn n ω) (f (X ω)))} := measure_mono hsub
      _ = ENNReal.ofReal (P.real {ω | e ≤ min 1 (dist (Yn n ω) (f (X ω)))}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by rw [le_div_iff₀ hepos]; linarith)
  have hto : Tendsto
      (fun n => ENNReal.ofReal ((∫ ω, min 1 (dist (Yn n ω) (f (X ω))) ∂P) / e))
      atTop (𝓝 0) := by
    have h0 := key.div_const e
    rw [zero_div] at h0
    have ht := (ENNReal.continuous_ofReal.tendsto 0).comp h0
    rwa [ENNReal.ofReal_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto
    (fun _ => zero_le) hle

end HigherDimLQGMetric
