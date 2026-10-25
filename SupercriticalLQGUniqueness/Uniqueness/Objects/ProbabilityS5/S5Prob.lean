import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS5.S5




 






set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS5

open SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
open LQGMetric (DistC)

 


theorem exists_s5_site_tail (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) :
    ∃ R₀ CU CL : ℝ, 1 ≤ R₀ ∧ 0 < CU ∧ 0 < CL ∧
      ∀ (μ : Measure DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF (id : DistC → DistC) μ →
        ∀ (C : Objects.CorrectedEvent.Constants), C.ξ = ξ → C.Q = Q →
          ∀ (k : ℕ), R₀ ≤ (Objects.CorrectedEvent.compareScale k) ^ (-(1:ℝ)/16) →
            ∀ (z : ℂ),
              μ {g | ¬ s5Site C (D g) k z} ≤
                ENNReal.ofReal ((CU + CL) *
                  ((Objects.CorrectedEvent.compareScale k) ^ (-(1:ℝ)/16)) ^ (-(64:ℝ))) := by
  obtain ⟨RU, CU, hRU, hCU, hU⟩ :=
    around_upper_tail ξ Q hQ D hD (a := 11/5) (b := 14/5)
      (by norm_num) (by norm_num) 64 (by norm_num)
  obtain ⟨RL, CL, hRL, hCL, hL⟩ :=
    acr_lower_tail ξ Q hQ D hD (a := 3/10) (b := 9/20)
      (by norm_num) (by norm_num) 64 (by norm_num)
  refine ⟨max RU RL, CU, CL, le_max_of_le_left hRU, hCU, hCL, ?_⟩
  intro μ _ hμ C hCξ hCQ k hR z
  set t : ℝ := Objects.CorrectedEvent.compareScale k with htdef
  have ht : 0 < t := by rw [htdef]; unfold Objects.CorrectedEvent.compareScale; positivity
  set R : ℝ := t ^ (-(1:ℝ)/16) with hRdef
  have hRpos : 0 < R := Real.rpow_pos_of_pos ht _
  let s : Ioi (0 : ℝ) := ⟨t*C.r, mul_pos ht C.rPos⟩
  have hRU' : RU ≤ R := (le_max_left _ _).trans hR
  have hRL' : RL ≤ R := (le_max_right _ _).trans hR
  have hUsite := hU μ id hμ R hRU' s z
  have hLsite := hL μ id hμ R hRL' s z
  have hFin := ae_acr_lt_top ξ Q hQ D hD μ id hμ
    (a := 3/10) (b := 9/20) (by norm_num) (by norm_num) s z
  let A : Set DistC := {g | ENNReal.ofReal R * Objects.CorrectedEvent.normalizer C g (t*C.r) z <
    Objects.CorrectedEvent.around (D g) z ((11/5)*t*C.r) ((14/5)*t*C.r)}
  let B : Set DistC := {g | Objects.CorrectedEvent.acr (D g) z ((3/10)*t*C.r) ((9/20)*t*C.r) <
    ENNReal.ofReal R⁻¹ * Objects.CorrectedEvent.normalizer C g (t*C.r) z}
  let F : Set DistC := {g | ¬ Objects.CorrectedEvent.acr (D g) z ((3/10)*t*C.r) ((9/20)*t*C.r) < ⊤}
  have hN : ∀ g : DistC, nrm ξ Q g s z = Objects.CorrectedEvent.normalizer C g (t*C.r) z := by
    intro g
    rw [← nrm_eq_normalizer, hCξ, hCQ]
  have hUA : μ A ≤ ENNReal.ofReal (CU * R ^ (-(64:ℝ))) := by
    convert hUsite using 2
    ext g
    simp only [A, mem_ofPred_eq, id, hN]
    have e1 : 11/5*t*C.r = 11/5*(s:ℝ) := by change 11/5*t*C.r = 11/5*(t*C.r); ring
    have e2 : 14/5*t*C.r = 14/5*(s:ℝ) := by change 14/5*t*C.r = 14/5*(t*C.r); ring
    rw [e1, e2]
  have hLB : μ B ≤ ENNReal.ofReal (CL * R ^ (-(64:ℝ))) := by
    convert hLsite using 2
    ext g
    simp only [B, mem_ofPred_eq, id, hN]
    have e1 : 3/10*t*C.r = 3/10*(s:ℝ) := by change 3/10*t*C.r = 3/10*(t*C.r); ring
    have e2 : 9/20*t*C.r = 9/20*(s:ℝ) := by change 9/20*t*C.r = 9/20*(t*C.r); ring
    rw [e1, e2]
  have hF : μ F = 0 := by
    apply (ae_iff).1
    simpa only [F, id, not_not, s, mul_assoc] using hFin
  have hsub : {g | ¬ s5Site C (D g) k z} ⊆ A ∪ B ∪ F := by
    have hRi : R⁻¹ = t ^ ((1:ℝ)/16) := by
      rw [hRdef, ← Real.rpow_neg ht.le]
      congr 1
      ring
    intro g hg
    rcases s5_bad_subset C D k z hg with hAB | hF
    · rcases hAB with hA | hB
      · exact Or.inl (Or.inl hA)
      · exact Or.inl (Or.inr (by simpa only [B, hRi, htdef] using hB))
    · exact Or.inr hF
  calc μ {g | ¬ s5Site C (D g) k z}
      ≤ μ (A ∪ B ∪ F) := measure_mono hsub
    _ ≤ μ A + μ B + μ F := by
      calc μ (A ∪ B ∪ F) ≤ μ (A ∪ B) + μ F := measure_union_le _ _
        _ ≤ (μ A + μ B) + μ F := by gcongr; exact measure_union_le _ _
        _ = μ A + μ B + μ F := by rw [add_assoc]
    _ ≤ ENNReal.ofReal (CU * R ^ (-(64:ℝ))) +
        ENNReal.ofReal (CL * R ^ (-(64:ℝ))) := by rw [hF, add_zero]; exact add_le_add hUA hLB
    _ = ENNReal.ofReal ((CU + CL) * R ^ (-(64:ℝ))) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS5
