import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldLMScale




 







set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

 

theorem shield_count_lt_le
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hMarg : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal q ≤ μ {g | Objects.Excursions.shieldAt C (D g) t}) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ b < 1 ∧ 0 < c ∧
      ∀ (R : ℝ) (_hR : 0 < R) (K : ℕ),
        μ {g | (countOcc
          (fun k => {x | Objects.Excursions.shieldAt C (D x) (shieldScale R K k)}) K g : ℝ) < b * K} ≤
        ENNReal.ofReal (c * Real.exp (-a * K)) := by
  obtain ⟨a, b, c, ha, hb, hb1, hc, HLM⟩ :=
    EndSaving.MainExtra.lmLem3_1b (1 / 5) (4 / 5)
      (by norm_num) (by norm_num) (by norm_num) q hq hq1
  refine ⟨a, b, c, ha, hb, hb1, hc, ?_⟩
  intro R hR K
  let t : ℕ → ℝ := shieldScale R K
  let r : ℕ → ℝ := fun k => (22 / 5) * t k
  let E : ℕ → Set LQGMetric.DistC :=
    fun k => {g | Objects.Excursions.shieldAt C (D g) (t k)}
  have ht : ∀ k, 0 < t k := fun k => shieldScale_pos hR K k
  have hLocal : ∀ k, AEEventIn μ
      (fieldSigma (fun g : LQGMetric.DistC =>
        LQGMetric.addConst g (-LQGMetric.circleAvg g (r k) 0))
        (annulus 0 ((1 / 5) * r k) ((4 / 5) * r k))) (E k) := by
    intro k
    have h := aeEventIn_shieldAt_recentered μ hμ ξ Q D hD C (t k) (ht k)
    convert h using 1
    all_goals simp only [r, t, Objects.ShieldLocality.shieldWindow]
    all_goals ring_nf
  classical
  choose F hF using hLocal
  have hiter : AnnulusIterHyp (id : LQGMetric.DistC → LQGMetric.DistC)
      (1 / 5) (4 / 5) r F := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      exact mul_pos (by norm_num) (ht k)
    · intro i j hij
      dsimp [r, t]
      exact mul_le_mul_of_nonneg_left (shieldScale_antitone hR K hij) (by norm_num)
    · intro k
      exact shieldScale_ratio hR K k
    · intro k
      exact (hF k).1
  have hprob : ∀ k, ENNReal.ofReal q ≤ μ (F k) := by
    intro k
    rw [← measure_congr (hF k).2]
    exact hMarg (t k) (ht k)
  have hOld : LQGMetric.IsNormalizedWPGFF
      (id : LQGMetric.DistC → LQGMetric.DistC) μ :=
    (isNormalizedWholePlaneGFF_iff_old).mp hμ
  have hKey := HLM μ id hOld r F hiter hprob K
  rw [EndSaving.MainExtra.measure_countOcc_lt_congr (fun k _ => (hF k).2) b K]
  exact hKey

 

theorem shield_failure_le
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hMarg : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal q ≤ μ {g | Objects.Excursions.shieldAt C (D g) t}) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ (T : Objects.CorrectedEvent.TubeData) (K : ℕ) (_hR : 0 < T.rho * T.r) (_hK : 1 ≤ K),
        μ {g | ¬ Objects.Excursions.shield C T K (D g)} ≤
          ENNReal.ofReal (c * Real.exp (-a * K)) := by
  obtain ⟨a, b, c, ha, hb, _, hc, Hcount⟩ :=
    shield_count_lt_le μ hμ ξ Q D hD C q hq hq1 hMarg
  refine ⟨a, c, ha, hc, ?_⟩
  intro T K hR hK
  let E : ℕ → Set LQGMetric.DistC :=
    fun k => {g | Objects.Excursions.shieldAt C (D g) (shieldScale (T.rho * T.r) K k)}
  have hsub : {g | ¬ Objects.Excursions.shield C T K (D g)} ⊆
      {g | (countOcc E K g : ℝ) < b * K} := by
    intro g hg
    have hzero : countOcc E K g = 0 := by
      classical
      unfold countOcc
      refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun k hk => ?_)
      obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hk
      intro hgood
      apply hg
      exact ⟨k, Finset.mem_Icc.mpr ⟨hk1, hkK⟩,
        by simpa only [E, Set.mem_ofPred_eq, shieldScale_eq_block _ K k hkK] using hgood⟩
    change (countOcc E K g : ℝ) < b * K
    have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
    simpa only [hzero, Nat.cast_zero] using mul_pos hb hKreal
  exact (measure_mono hsub).trans (Hcount (T.rho * T.r) hR K)

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
