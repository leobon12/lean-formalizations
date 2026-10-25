import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.LMIter2
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge




 










set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 
theorem annulus_iteration2_ae_open (s₁ s₂ : ℝ) (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ b < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω),
          (∀ k, 0 < r k) → Antitone r →
          (∀ k, r (k + 1) / r k ≤ s₁) →
          (∀ k, LQGMetric.Blueprint.AEEventIn P
            (LQGMetric.Blueprint.fieldSigma
              (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) 0))
              (LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k))) (E k)) →
          (∀ k, ENNReal.ofReal p ≤ P (E k)) →
          ∀ K : ℕ, P {ω | (LQGMetric.Blueprint.countOcc E K ω : ℝ) < b * K} ≤
            ENNReal.ofReal (c * Real.exp (-a * K)) := by
  obtain ⟨a, b, c, ha, hb0, hb1, hc0, hmain⟩ := lmLem3_1b s₁ s₂ hs₁ hs₁₂ hs₂ p hp0 hp1
  refine ⟨a, b, c, ha, hb0, hb1, hc0, ?_⟩
  intro Ω _ P _ h hh r E hr hanti hratio hE hpE K
  classical
  choose F hFm hEF using hE
  have hF : LQGMetric.Blueprint.AnnulusIterHyp h s₁ s₂ r F :=
    ⟨hr, hanti, hratio, hFm⟩
  have hpF : ∀ k, ENNReal.ofReal p ≤ P (F k) := by
    intro k
    rw [← measure_congr (hEF k)]
    exact hpE k
  rw [LQGMetric.LM.prob_countOcc_congr hEF b K]
  exact hmain P h (Toolkit.AnnulusIteration.normalized_old_of_new hh) r F hF hpF K

 
theorem annulus_iteration2_ae_translated_open (s₁ s₂ : ℝ) (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ b < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), LQGMetric.IsWholePlaneGFF h P →
        ∀ (z : ℂ) (r : ℕ → ℝ) (E : ℕ → Set Ω),
          (∀ k, 0 < r k) → Antitone r →
          (∀ k, r (k + 1) / r k ≤ s₁) →
          (∀ k, LQGMetric.Blueprint.AEEventIn P
            (LQGMetric.Blueprint.fieldSigma
              (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) z))
              (LQGMetric.Blueprint.annulus z (s₁ * r k) (s₂ * r k))) (E k)) →
          (∀ k, ENNReal.ofReal p ≤ P (E k)) →
          ∀ K : ℕ, P {ω | (LQGMetric.Blueprint.countOcc E K ω : ℝ) < b * K} ≤
            ENNReal.ofReal (c * Real.exp (-a * K)) := by
  obtain ⟨a, b, c, ha, hb0, hb1, hc0, hmain⟩ :=
    annulus_iteration2_ae_open s₁ s₂ hs₁ hs₁₂ hs₂ p hp0 hp1
  refine ⟨a, b, c, ha, hb0, hb1, hc0, ?_⟩
  intro Ω _ P _ h hh z r E hr hanti hratio hE hpE K
  let hz : Ω → DistC := fun ω => LQGMetric.addConst (translateDist z (h ω))
    (-LQGMetric.circleAvg (h ω) 1 z)
  have hnorm : IsNormalizedWholePlaneGFF hz P := Toolkit.AnnulusIteration.translated_normalized hh z
  apply hmain P hz hnorm r E hr hanti hratio _ hpE K
  intro k
  have hVW : ∀ y : ℂ, y ∈ LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k) ↔
      y + z ∈ LQGMetric.Blueprint.annulus z (s₁ * r k) (s₂ * r k) := by
    intro y
    change (s₁ * r k < ‖y - 0‖ ∧ ‖y - 0‖ < s₂ * r k) ↔
      (s₁ * r k < ‖y + z - z‖ ∧ ‖y + z - z‖ < s₂ * r k)
    simp only [sub_zero, add_sub_cancel_right]
  exact Toolkit.AnnulusIteration.aeEventIn_translated_centered hh z (hr k)
    (LQGMetric.Blueprint.annulus z (s₁ * r k) (s₂ * r k))
    (LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k)) hVW (E k) (hE k)

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
