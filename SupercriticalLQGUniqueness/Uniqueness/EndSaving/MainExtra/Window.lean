import SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra.CircleSup




 









set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra

open LQGMetric (DistC)

 
theorem logb_count_mul_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Real.logb 8 ε⁻¹ + 2) * ε ^ 2 ≤ 3 * ε := by
  have hl8 : 1 ≤ Real.log 8 := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 8 := Real.log_le_log (Real.exp_pos 1) (by
          have := Real.exp_one_lt_d9; linarith)
  have hinv : 1 ≤ ε⁻¹ := one_le_inv_iff₀.2 ⟨hε, hε1⟩
  have hlog0 : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg hinv
  have hlogb : Real.logb 8 ε⁻¹ ≤ ε⁻¹ := by
    rw [Real.logb]
    calc Real.log ε⁻¹ / Real.log 8 ≤ Real.log ε⁻¹ :=
          div_le_self hlog0 hl8
      _ ≤ ε⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ ε⁻¹ := by linarith
  have h1 : Real.logb 8 ε⁻¹ * ε ^ 2 ≤ ε := by
    calc Real.logb 8 ε⁻¹ * ε ^ 2 ≤ ε⁻¹ * ε ^ 2 := by gcongr
      _ = ε := by field_simp
  nlinarith

 
theorem r51a_window :
    ∃ C ε₁ : ℝ, 0 < C ∧ 0 < ε₁ ∧ ε₁ < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (R : EndSaving.Interfaces.AdmissibleRadii) (b ε : Set.Ioi (0 : ℝ)), (ε : ℝ) ≤ ε₁ →
          P {ω | ¬ ∃ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr ∧
            ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → (ε : ℝ) ^ 2 * b ≤ r → (r : ℝ) ≤ ε * b →
              ∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)), ∃ hrz : ℝ,
                IsCircleAverage (h ω) r z hrz ∧
                  |hrz - hbr| ≤ 3 * Real.log (((r : ℝ) / (b : ℝ))⁻¹)} ≤
            ENNReal.ofReal (C * ε) := by
  classical
  obtain ⟨C₁, t₀, hC₁, ht₀, ht₀1, Hsup⟩ := sup_tail_circleAvg
  refine ⟨3 * C₁, t₀ / 2, by positivity, by positivity, by linarith, ?_⟩
  intro Ω _ P _ h hh R b ε hε
  obtain ⟨H, hH, hcirc⟩ := ae_isCircleAverage_all hh
  have hb : (0 : ℝ) < b := b.2
  have hε0 : (0 : ℝ) < ε := ε.2
  have hε1 : (ε : ℝ) ≤ 1 := by linarith
  set S : Set ℝ := R.radii ∩ Set.Icc ((ε : ℝ) ^ 2 * b) (ε * b) with hS
  have hpos : ∀ r ∈ S, 0 < r := fun r hr => (R.subset_unit hr.1).1
  have hac : (ε : ℝ) ^ 2 * b ≤ ε * b := by
    have : (ε : ℝ) ^ 2 ≤ ε := by nlinarith
    nlinarith
  obtain ⟨hfin, hcard⟩ := card_radii_le (S := S) (by positivity) hac
    (fun x y hx hy hxy => R.separated hx.1 hy.1 hxy) Set.inter_subset_right
  set Fin := hfin.toFinset with hFin
  
  have hG0 : ∀ᵐ ω ∂P, (∀ z, IsCircleAverage (h ω) b z (H b z ω)) ∧
      ∀ r (hr : r ∈ S), ∀ z, IsCircleAverage (h ω) ⟨r, hpos r hr⟩ z (H r z ω) := by
    refine (hcirc b).and ((ae_ball_iff hfin.countable).2 fun r hr => ?_)
    exact hcirc ⟨r, hpos r hr⟩
  set Bad : ℝ → Set Ω := fun r =>
    {ω | ∃ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)), 3 * Real.log (b / r) < |H r z ω - H b 0 ω|}
    with hBad
  have hsub : {ω | ¬ ∃ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr ∧
      ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → (ε : ℝ) ^ 2 * b ≤ r → (r : ℝ) ≤ ε * b →
        ∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)), ∃ hrz : ℝ,
          IsCircleAverage (h ω) r z hrz ∧ |hrz - hbr| ≤ 3 * Real.log (((r : ℝ) / (b : ℝ))⁻¹)} ⊆
      {ω | ¬ ((∀ z, IsCircleAverage (h ω) b z (H b z ω)) ∧
        ∀ r (hr : r ∈ S), ∀ z, IsCircleAverage (h ω) ⟨r, hpos r hr⟩ z (H r z ω))} ∪
      ⋃ r ∈ Fin, Bad r := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Set.mem_iUnion,
      not_exists] at hcon
    obtain ⟨⟨hbω, hrω⟩, hnb⟩ := hcon
    apply hω
    refine ⟨H b 0 ω, hbω 0, fun r hrR hlo hhi z hz => ⟨H r z ω, ?_, ?_⟩⟩
    · have hrS : r.1 ∈ S := ⟨hrR, hlo, hhi⟩
      exact hrω r.1 hrS z
    · have hrS : r.1 ∈ S := ⟨hrR, hlo, hhi⟩
      have hno := hnb r.1 (hfin.mem_toFinset.mpr hrS)
      simp only [hBad, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hno
      rw [inv_div]
      exact hno z hz
  have hnull : P {ω | ¬ ((∀ z, IsCircleAverage (h ω) b z (H b z ω)) ∧
      ∀ r (hr : r ∈ S), ∀ z, IsCircleAverage (h ω) ⟨r, hpos r hr⟩ z (H r z ω))} = 0 :=
    ae_iff.mp hG0
  have hbad : ∀ r ∈ Fin, P (Bad r) ≤ ENNReal.ofReal (C₁ * (ε : ℝ) ^ 2) := by
    intro r hr
    have hrS : r ∈ S := hfin.mem_toFinset.mp hr
    have hr0 := hpos r hrS
    have hrb : r ≤ t₀ * b := by
      have := hrS.2.2
      nlinarith
    refine (Hsup P H hH b r hr0 hrb).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : r / b ≤ ε := (div_le_iff₀ hb).2 (by linarith [hrS.2.2])
    have h2 : 0 ≤ r / b := by positivity
    gcongr
  calc P _ ≤ P ({ω | ¬ ((∀ z, IsCircleAverage (h ω) b z (H b z ω)) ∧
        ∀ r (hr : r ∈ S), ∀ z, IsCircleAverage (h ω) ⟨r, hpos r hr⟩ z (H r z ω))} ∪
        ⋃ r ∈ Fin, Bad r) := measure_mono hsub
    _ ≤ P {ω | ¬ ((∀ z, IsCircleAverage (h ω) b z (H b z ω)) ∧
        ∀ r (hr : r ∈ S), ∀ z, IsCircleAverage (h ω) ⟨r, hpos r hr⟩ z (H r z ω))} +
        P (⋃ r ∈ Fin, Bad r) := measure_union_le _ _
    _ ≤ 0 + ∑ r ∈ Fin, P (Bad r) := by
        rw [hnull]
        gcongr
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ _r ∈ Fin, ENNReal.ofReal (C₁ * (ε : ℝ) ^ 2) := by
        rw [zero_add]
        exact Finset.sum_le_sum hbad
    _ = ENNReal.ofReal (Fin.card * (C₁ * (ε : ℝ) ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (3 * C₁ * ε) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hc := hcard hfin
        have he : (ε : ℝ) * b / ((ε : ℝ) ^ 2 * b) = (ε : ℝ)⁻¹ := by
          field_simp
        rw [he] at hc
        have hlb := logb_count_mul_le hε0 hε1
        calc (Fin.card : ℝ) * (C₁ * (ε : ℝ) ^ 2) = C₁ * ((Fin.card : ℝ) * (ε : ℝ) ^ 2) := by
              ring
          _ ≤ C₁ * ((Real.logb 8 (ε : ℝ)⁻¹ + 2) * (ε : ℝ) ^ 2) := by gcongr
          _ ≤ C₁ * (3 * ε) := by gcongr
          _ = 3 * C₁ * ε := by ring

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra
