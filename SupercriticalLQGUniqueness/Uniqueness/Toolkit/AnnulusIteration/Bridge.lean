import SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LQGMetric.Papers.LM.L3_4M6
import LQGMetric.Field.CircleAvgRate
import LQGMetric.Papers.GM.S2.SpatialIndepShift
import LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LQGMetric.Papers.LM.L3_1N2P1
import LQGMetric.Papers.GM.S2.SpatialIndep
import LQGMetric.Field.MarkovFinal
import LQGMetric.Papers.MQ.Lem41
import LQGMetric.Papers.CONF.S3D110A
import LQGMetric.Papers.GM.S5.Tubes58Indep




 
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration

open LQGMetric

private theorem circleAverage_iff_tendsto (g : DistC) (r : Set.Ioi (0 : ℝ)) (z : ℂ)
    (a : ℝ) : IsCircleAverage g r z a ↔
      Tendsto (fun n => LQGMetric.CircleAvg.mollAvg g n z (r : ℝ)) atTop (𝓝 a) := by
  rfl

theorem circleAvg_eq_of_isCircleAverage (g : DistC) (r : Set.Ioi (0 : ℝ))
    (z : ℂ) (a : ℝ) (ha : IsCircleAverage g r z a) :
    LQGMetric.circleAvg g (r : ℝ) z = a := by
  exact LQGMetric.CircleAvg.circleAvg_eq_of_tendsto
    ((circleAverage_iff_tendsto g r z a).mp ha)

theorem normalized_old_of_new {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) : IsNormalizedWPGFF h P := by
  refine ⟨hh.1, ?_⟩
  filter_upwards [hh.2] with ω hω
  exact circleAvg_eq_of_isCircleAverage (h ω) ⟨1, by norm_num⟩ 0 0 hω


theorem ae_isCircleAverage_circleAvg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (r : Set.Ioi (0 : ℝ)) (z : ℂ) :
    ∀ᵐ ω ∂P, IsCircleAverage (h ω) r z (LQGMetric.circleAvg (h ω) (r : ℝ) z) := by
  filter_upwards [LQGMetric.CircleAvg.ae_tendsto_mollAvg hh z r.2] with ω hω
  obtain ⟨a, ha⟩ := hω
  have heq : LQGMetric.circleAvg (h ω) (r : ℝ) z = a :=
    LQGMetric.CircleAvg.circleAvg_eq_of_tendsto ha
  rw [heq]
  exact (circleAverage_iff_tendsto (h ω) r z a).mpr ha

theorem normalized_new_of_old {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) : IsNormalizedWholePlaneGFF h P := by
  refine ⟨hh.1, ?_⟩
  filter_upwards [ae_isCircleAverage_circleAvg hh.1 ⟨1, by norm_num⟩ 0, hh.2]
    with ω hω heq
  simpa only [heq] using hω

theorem normalize_new {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P) :
    IsNormalizedWholePlaneGFF
      (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) 1 0)) P := by
  apply normalized_new_of_old
  have hc : Measurable fun ω => -LQGMetric.circleAvg (h ω) 1 0 :=
    ((LQGMetric.measurable_circleAvg_left 1 0).comp hh.measurable).neg
  refine ⟨hh.addConst hc, ?_⟩
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
  rw [hω]
  ring

theorem translateDist_eq_affineComp_one (g : DistC) (z : ℂ) :
    SupercriticalLQGUniqueness.translateDist z g = LQGMetric.affineComp 1 z g := by
  apply DFunLike.ext
  intro φ
  have ht : SupercriticalLQGUniqueness.testTranslate z φ =
      LQGMetric.testAffinePull 1 z φ := by
    ext x
    rw [LQGMetric.testAffinePull_apply 1 z one_ne_zero]
    simp only [Complex.ofReal_one, div_one]
    rfl
  change g (SupercriticalLQGUniqueness.testTranslate z φ) =
    (LQGMetric.affineComp 1 z g) φ
  rw [LQGMetric.GFFInv.affineComp_apply, ht]
  norm_num


theorem fieldSigmaClosed_le_fieldSigma_of_compact {Ω : Type} [MeasurableSpace Ω]
    (h : Ω → DistC) (K : Set ℂ) (V : TopologicalSpace.Opens ℂ)
    (hK : IsCompact K) (hKV : K ⊆ V) :
    LQGMetric.Blueprint.fieldSigmaClosed h K ≤ LQGMetric.Blueprint.fieldSigma h V := by
  obtain ⟨ε, hε, hsub⟩ := hK.exists_thickening_subset_open V.2 hKV
  have hneigh : LQGMetric.Blueprint.nbhdO ε K ≤ V := hsub
  exact (iInf_le_of_le ε (iInf_le _ hε)).trans
    (LQGMetric.GM.fieldSigma_mono h hneigh)

theorem circleAvg_translateDist (g : DistC) (r : ℝ) (z w : ℂ) :
    LQGMetric.circleAvg (translateDist z g) r w = LQGMetric.circleAvg g r (w + z) := by
  rw [translateDist_eq_affineComp_one]
  exact LQGMetric.GM.circleAvg_affineComp_one_at g r z w

theorem translated_normalized {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ) :
    IsNormalizedWholePlaneGFF
      (fun ω => LQGMetric.addConst (translateDist z (h ω))
        (-LQGMetric.circleAvg (h ω) 1 z)) P := by
  have hEq : (fun ω => LQGMetric.addConst (translateDist z (h ω))
        (-LQGMetric.circleAvg (h ω) 1 z)) =
      (fun ω => LQGMetric.addConst (LQGMetric.affineComp 1 z (h ω))
        (-LQGMetric.circleAvg (LQGMetric.affineComp 1 z (h ω)) 1 0)) := by
    funext ω
    rw [translateDist_eq_affineComp_one,
      LQGMetric.GM.circleAvg_affineComp_one_at]
    simp only [zero_add]
  rw [hEq]
  exact normalized_new_of_old (LQGMetric.GM.isNormalized_shift hh z)


theorem ae_centered_translate {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P,
      LQGMetric.addConst
        (LQGMetric.addConst (translateDist z (h ω)) (-LQGMetric.circleAvg (h ω) 1 z))
        (-LQGMetric.circleAvg
          (LQGMetric.addConst (translateDist z (h ω)) (-LQGMetric.circleAvg (h ω) 1 z)) r 0) =
      translateDist z (LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) r z)) := by
  have htr : IsWholePlaneGFF (fun ω => translateDist z (h ω)) P := by
    simpa only [translateDist_eq_affineComp_one] using hh.affineComp one_pos z
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst htr 0 hr] with ω hω
  rw [hω, circleAvg_translateDist]
  simp only [zero_add]
  rw [LQGMetric.GM.addConst_addConst]
  have hc : -LQGMetric.circleAvg (h ω) 1 z +
      -(LQGMetric.circleAvg (h ω) r z + -LQGMetric.circleAvg (h ω) 1 z) =
      -LQGMetric.circleAvg (h ω) r z := by ring
  rw [hc, translateDist_eq_affineComp_one]
  conv_rhs => rw [translateDist_eq_affineComp_one]
  exact (LQGMetric.GM.affineComp_addConst one_pos z (h ω)
    (-LQGMetric.circleAvg (h ω) r z)).symm


theorem annulus_iteration_ae_open (s₁ s₂ : ℝ) (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1) (a : ℝ) (ha : 0 < a)
    (b : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
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
  obtain ⟨p, c, hp0, hp1, hc0, hmain⟩ :=
    LQGMetric.LM.lmLem3_1a s₁ s₂ hs₁ hs₁₂ hs₂ a ha b hb hb1
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
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
  exact hmain P h (normalized_old_of_new hh) r F hF hpF K


theorem annulus_iteration_ae_compact_interior (s₁ s₂ : ℝ) (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1) (a : ℝ) (ha : 0 < a)
    (b : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (r : ℕ → ℝ) (Kset : ℕ → Set ℂ) (E : ℕ → Set Ω),
          (∀ k, 0 < r k) → Antitone r →
          (∀ k, r (k + 1) / r k ≤ s₁) →
          (∀ k, IsCompact (Kset k)) →
          (∀ k, Kset k ⊆ LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k)) →
          (∀ k, LQGMetric.Blueprint.AEEventIn P
            (LQGMetric.Blueprint.fieldSigmaClosed
              (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) 0))
              (Kset k)) (E k)) →
          (∀ k, ENNReal.ofReal p ≤ P (E k)) →
          ∀ K : ℕ, P {ω | (LQGMetric.Blueprint.countOcc E K ω : ℝ) < b * K} ≤
            ENNReal.ofReal (c * Real.exp (-a * K)) := by
  obtain ⟨p, c, hp0, hp1, hc0, hmain⟩ :=
    annulus_iteration_ae_open s₁ s₂ hs₁ hs₁₂ hs₂ a ha b hb hb1
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh r Kset E hr hanti hratio hcompact hsub hE hpE K
  apply hmain P h hh r E hr hanti hratio _ hpE K
  intro k
  obtain ⟨F, hFm, hEF⟩ := hE k
  exact ⟨F, (fieldSigmaClosed_le_fieldSigma_of_compact
    (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) 0))
    (Kset k) (LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k))
    (hcompact k) (hsub k)) F hFm, hEF⟩


theorem gm_spatial_selected_circleAverage (s p q : ℝ) (hs : 0 < s)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    ∃ n₀ : ℕ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P →
      ∀ (Z : Finset ℂ), n₀ ≤ Z.card →
      (∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 2 * (1 + s) ≤ ‖z - w‖) →
      ∀ (E : ℂ → Set Ω) (avg : ℂ → Ω → ℝ),
      (∀ z ∈ Z, ∀ᵐ ω ∂P,
        IsCircleAverage (h ω) ⟨1 + s, Set.mem_Ioi.mpr (add_pos one_pos hs)⟩ z (avg z ω)) →
      (∀ z ∈ Z, LQGMetric.Blueprint.AEEventIn P
        (LQGMetric.Blueprint.fieldSigma
          (fun ω => LQGMetric.addConst (h ω) (-avg z ω))
          (LQGMetric.Blueprint.ballO z 1)) (E z)) →
      (∀ z ∈ Z, ENNReal.ofReal p ≤ P (E z)) →
      ENNReal.ofReal q ≤ P (⋃ z ∈ Z, E z) := by
  obtain ⟨n₀, hn₀⟩ := LQGMetric.GM.gm_L2_7
    LQGMetric.MarkovFinal.lmLem2_1 LQGMetric.MQ.mqLem4_1Gen hs hp hp1 hq hq1
  refine ⟨n₀, ?_⟩
  intro Ω _ P _ h hh Z hZ hsep E avg havg hE hpE
  apply hn₀ P h hh Z hZ hsep E _ hpE
  intro z hz
  have hEq : ∀ᵐ ω ∂P,
      LQGMetric.addConst (h ω) (-avg z ω) =
        LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (1 + s) z) := by
    filter_upwards [havg z hz] with ω ha
    rw [circleAvg_eq_of_isCircleAverage (h ω) ⟨1 + s, Set.mem_Ioi.mpr (add_pos one_pos hs)⟩ z (avg z ω) ha]
  exact LQGMetric.GM.aeEventIn_of_ae_eq hEq
    (LQGMetric.Blueprint.ballO z 1) (hE z hz)


theorem fieldSigma0On_le_centered {Ω : Type} [MeasurableSpace Ω]
    (h : Ω → DistC) (c : Ω → ℝ) (V : Set ℂ) (hV : IsOpen V) :
    LQGMetric.Blueprint.fieldSigma0On h V ≤
      LQGMetric.Blueprint.fieldSigma (fun ω => LQGMetric.addConst (h ω) (c ω))
        (LQGMetric.Blueprint.toOpens V hV) := by
  rw [← LQGMetric.CONF.fieldSigma0On_addConst h c V]
  exact LQGMetric.CONF.fieldSigma0On_le_fieldSigma _ hV

theorem fieldSigmaClosed0_le_centered_open {Ω : Type} [MeasurableSpace Ω]
    (h : Ω → DistC) (c : Ω → ℝ) (K : Set ℂ)
    (V : TopologicalSpace.Opens ℂ) (hK : IsCompact K) (hKV : K ⊆ V) :
    LQGMetric.Blueprint.fieldSigmaClosed0 h K ≤
      LQGMetric.Blueprint.fieldSigma (fun ω => LQGMetric.addConst (h ω) (c ω)) V := by
  rw [← LQGMetric.CONF.fieldSigmaClosed0_addConst h c K]
  exact (LQGMetric.CONF.fieldSigmaClosed0_le_fieldSigmaClosed _ K).trans
    (fieldSigmaClosed_le_fieldSigma_of_compact _ K V hK hKV)


theorem gm_spatial_scaled_modConst (s p q : ℝ) (hs : 0 < s)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    ∃ n₀ : ℕ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P →
      ∀ R : ℝ, 0 < R → ∀ Z : Finset ℂ, n₀ ≤ Z.card →
      (∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 2 * (1 + s) * R ≤ ‖z - w‖) →
      ∀ E : ℂ → Set Ω,
      (∀ z ∈ Z, LQGMetric.Blueprint.AEEventIn P
        (LQGMetric.Blueprint.fieldSigma0On h (Metric.ball z R)) (E z)) →
      (∀ z ∈ Z, ENNReal.ofReal p ≤ P (E z)) →
      ENNReal.ofReal q ≤ P (⋃ z ∈ Z, E z) := by
  obtain ⟨n₀, hn₀⟩ := LQGMetric.GM.gm_L2_7_scaled
    (LQGMetric.GM.gm_L2_7 LQGMetric.MarkovFinal.lmLem2_1
      LQGMetric.MQ.mqLem4_1Gen) hs hp hp1 hq hq1
  refine ⟨n₀, ?_⟩
  intro Ω _ P _ h hh R hR Z hZ hsep E hE hpE
  apply hn₀ P h hh R hR Z hZ hsep E _ hpE
  intro z hz c hc
  obtain ⟨F, hFm, hEF⟩ := hE z hz
  exact ⟨F, (fieldSigma0On_le_centered h c (Metric.ball z R)
    (Metric.isOpen_ball)) F hFm, hEF⟩


theorem aeEventIn_translated_centered {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (z : ℂ) {r : ℝ} (hr : 0 < r)
    (V W : TopologicalSpace.Opens ℂ)
    (hVW : ∀ y : ℂ, y ∈ W ↔ y + z ∈ V) (E : Set Ω)
    (hE : LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) r z)) V) E) :
    LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω =>
          let hz := LQGMetric.addConst (translateDist z (h ω))
            (-LQGMetric.circleAvg (h ω) 1 z)
          LQGMetric.addConst hz (-LQGMetric.circleAvg hz r 0)) W) E := by
  obtain ⟨F, hFm, hEF⟩ := hE
  have hVW' : ∀ y : ℂ, y ∈ W ↔ (1 : ℝ) • y + z ∈ V := by
    intro y
    simpa only [one_smul] using hVW y
  have hE1 : LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.affineComp 1 z
          (LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) r z))) W) E :=
    ⟨F, (LQGMetric.GM.fieldSigma_le_affineComp one_pos hVW'
      (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) r z))) F hFm,
      hEF⟩
  apply LQGMetric.GM.aeEventIn_of_ae_eq (P := P) _ W hE1
  filter_upwards [ae_centered_translate hh z hr] with ω hω
  simpa only [translateDist_eq_affineComp_one] using hω.symm


theorem annulus_iteration_ae_translated_open (s₁ s₂ : ℝ) (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1) (a : ℝ) (ha : 0 < a)
    (b : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P →
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
  obtain ⟨p, c, hp0, hp1, hc0, hmain⟩ :=
    annulus_iteration_ae_open s₁ s₂ hs₁ hs₁₂ hs₂ a ha b hb hb1
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh z r E hr hanti hratio hE hpE K
  let hz : Ω → DistC := fun ω => LQGMetric.addConst (translateDist z (h ω))
    (-LQGMetric.circleAvg (h ω) 1 z)
  have hnorm : IsNormalizedWholePlaneGFF hz P := translated_normalized hh z
  apply hmain P hz hnorm r E hr hanti hratio _ hpE K
  intro k
  have hVW : ∀ y : ℂ, y ∈ LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k) ↔
      y + z ∈ LQGMetric.Blueprint.annulus z (s₁ * r k) (s₂ * r k) := by
    intro y
    change (s₁ * r k < ‖y - 0‖ ∧ ‖y - 0‖ < s₂ * r k) ↔
      (s₁ * r k < ‖y + z - z‖ ∧ ‖y + z - z‖ < s₂ * r k)
    simp only [sub_zero, add_sub_cancel_right]
  exact aeEventIn_translated_centered hh z (hr k)
    (LQGMetric.Blueprint.annulus z (s₁ * r k) (s₂ * r k))
    (LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k)) hVW (E k) (hE k)


private theorem exists_annulus_rescale {i o : ℝ} (hi : 0 < i) (hio : i < o)
    (ho1 : o < 1) :
    ∃ c t : ℝ, 0 < c ∧ c < 1 ∧ i < t ∧ t < 1 ∧ c * i < i ∧ o < c * t := by
  let c : ℝ := (1 + o) / 2
  let t : ℝ := (o + c) / (2 * c)
  have ho : 0 < o := lt_trans hi hio
  have hc0 : 0 < c := by dsimp [c]; linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
  have hoc : o < c := by dsimp [c]; linarith
  have ht0 : 0 < t := by dsimp [t]; positivity
  have hct : c * t = (o + c) / 2 := by
    dsimp [t]
    field_simp
  have hot : o < c * t := by rw [hct]; linarith
  have hti : i < t := by nlinarith
  have ht1 : t < 1 := by
    rw [div_lt_one (mul_pos two_pos hc0)]
    exact by linarith
  have hci : c * i < i := by nlinarith
  exact ⟨c, t, hc0, hc1, hti, ht1, hci, hot⟩

def closedAnnulus (z : ℂ) (u v : ℝ) : Set ℂ :=
  {w | u ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ v}

private theorem closedAnnulus_compact (z : ℂ) (u v : ℝ) :
    IsCompact (closedAnnulus z u v) := by
  have hclosed : IsClosed (closedAnnulus z u v) := by
    exact (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
      (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)
  have hsub : closedAnnulus z u v ⊆ Metric.closedBall z v := by
    intro w hw
    exact Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using hw.2)
  exact (isCompact_closedBall z v).of_isClosed_subset hclosed hsub


private theorem closedAnnulus_offcenter_subset (s₀ s₁ s₂ c t r : ℝ)
    (z : ℂ) (hr : 0 < r) (hz : ‖z‖ ≤ s₀ * r)
    (hci : c * (s₁ - s₀) < s₁ - s₀)
    (hot : s₂ + s₀ < c * t) :
    closedAnnulus z (s₁ * r) (s₂ * r) ⊆
      LQGMetric.Blueprint.annulus 0 ((s₁ - s₀) * (c * r)) (t * (c * r)) := by
  intro w hw
  change s₁ * r ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ s₂ * r at hw
  change (s₁ - s₀) * (c * r) < ‖w - 0‖ ∧ ‖w - 0‖ < t * (c * r)
  have hrev : ‖w - z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le w z
  have hfor : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
  constructor
  · simp only [sub_zero]
    nlinarith [mul_lt_mul_of_pos_right hci hr]
  · simp only [sub_zero]
    nlinarith [mul_lt_mul_of_pos_right hot hr]


theorem annulus_iteration_ae_offcenter_modConst (s₀ s₁ s₂ : ℝ)
    (hs₀ : 0 < s₀) (hs₀₁ : s₀ < s₁) (hs₁₂ : s₁ < s₂)
    (hs₀₂ : s₀ < 1 - s₂) (a : ℝ) (ha : 0 < a)
    (b : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    ∃ p c₀ : ℝ, 0 < p ∧ p < 1 ∧ 0 < c₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P →
        ∀ (r : ℕ → ℝ) (z : ℕ → ℂ) (E : ℕ → Set Ω),
          (∀ k, 0 < r k) → Antitone r →
          (∀ k, r (k + 1) / r k ≤ s₁ - s₀) →
          (∀ k, ‖z k‖ ≤ s₀ * r k) →
          (∀ k, LQGMetric.Blueprint.AEEventIn P
            (LQGMetric.Blueprint.fieldSigmaClosed0 h
              (closedAnnulus (z k) (s₁ * r k) (s₂ * r k))) (E k)) →
          (∀ k, ENNReal.ofReal p ≤ P (E k)) →
          ∀ K : ℕ, P {ω | (LQGMetric.Blueprint.countOcc E K ω : ℝ) < b * K} ≤
            ENNReal.ofReal (c₀ * Real.exp (-a * K)) := by
  have hi : 0 < s₁ - s₀ := by linarith
  have hio : s₁ - s₀ < s₂ + s₀ := by linarith
  have ho1 : s₂ + s₀ < 1 := by linarith
  obtain ⟨c, t, hc0, hc1, hit, ht1, hci, hot⟩ :=
    exists_annulus_rescale hi hio ho1
  obtain ⟨p, c₀, hp0, hp1, hc₀, hmain⟩ :=
    annulus_iteration_ae_open (s₁ - s₀) t hi hit ht1 a ha b hb hb1
  refine ⟨p, c₀, hp0, hp1, hc₀, ?_⟩
  intro Ω _ P _ h hh r z E hr hanti hratio hz hE hpE K
  let h0 : Ω → DistC := fun ω =>
    LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) 1 0)
  have hnorm : IsNormalizedWholePlaneGFF h0 P := normalize_new hh
  have hr0 : ∀ k, 0 < c * r k := fun k => mul_pos hc0 (hr k)
  have hanti0 : Antitone (fun k => c * r k) := by
    intro j k hjk
    exact mul_le_mul_of_nonneg_left (hanti hjk) hc0.le
  have hratio0 : ∀ k, (c * r (k + 1)) / (c * r k) ≤ s₁ - s₀ := by
    intro k
    calc
      (c * r (k + 1)) / (c * r k) = r (k + 1) / r k := by
        field_simp
      _ ≤ s₁ - s₀ := hratio k
  apply hmain P h0 hnorm (fun k => c * r k) E hr0 hanti0 hratio0 _ hpE K
  intro k
  let A : Set ℂ := closedAnnulus (z k) (s₁ * r k) (s₂ * r k)
  obtain ⟨F, hFm, hEF⟩ := hE k
  have hFm0 : MeasurableSet[LQGMetric.Blueprint.fieldSigmaClosed0 h0 A] F := by
    rw [show LQGMetric.Blueprint.fieldSigmaClosed0 h0 A =
      LQGMetric.Blueprint.fieldSigmaClosed0 h A from
        LQGMetric.CONF.fieldSigmaClosed0_addConst h
          (fun ω => -LQGMetric.circleAvg (h ω) 1 0) A]
    exact hFm
  have hsub : A ⊆ LQGMetric.Blueprint.annulus 0
      ((s₁ - s₀) * (c * r k)) (t * (c * r k)) :=
    closedAnnulus_offcenter_subset s₀ s₁ s₂ c t (r k) (z k)
      (hr k) (hz k) hci hot
  exact ⟨F, (fieldSigmaClosed0_le_centered_open h0
      (fun ω => -LQGMetric.circleAvg (h0 ω) (c * r k) 0) A
      (LQGMetric.Blueprint.annulus 0 ((s₁ - s₀) * (c * r k)) (t * (c * r k)))
      (closedAnnulus_compact _ _ _) hsub) F hFm0, hEF⟩


theorem ae_countable_isCircleAverage {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (r : ℕ → Set.Ioi (0 : ℝ)) (z : ℕ → ℂ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      IsCircleAverage (h ω) (r k) (z k)
        (LQGMetric.circleAvg (h ω) (r k : ℝ) (z k)) := by
  exact ae_all_iff.mpr fun k => ae_isCircleAverage_circleAvg hh (r k) (z k)

theorem ae_countable_translated_circleAvg {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (z : ℂ) (r : ℕ → Set.Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      LQGMetric.circleAvg
        (LQGMetric.addConst (translateDist z (h ω))
          (-LQGMetric.circleAvg (h ω) 1 z)) (r k : ℝ) 0 =
        LQGMetric.circleAvg (h ω) (r k : ℝ) z -
          LQGMetric.circleAvg (h ω) 1 z := by
  have htr : IsWholePlaneGFF (fun ω => translateDist z (h ω)) P := by
    simpa only [translateDist_eq_affineComp_one] using hh.affineComp one_pos z
  rw [ae_all_iff]
  intro k
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst htr 0 (r k).2]
    with ω hω
  rw [hω, circleAvg_translateDist]
  simp only [zero_add]
  ring

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration


