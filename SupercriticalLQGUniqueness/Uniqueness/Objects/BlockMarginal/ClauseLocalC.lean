import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.ClauseLocalB
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.S7




 












set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter
open LQGMetric.Blueprint
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC restrictTo addConst)

 

theorem narrowStart_pos (C : Objects.CorrectedEvent.Constants) : 1 ≤ Objects.CorrectedEvent.narrowStart C := by
  unfold Objects.CorrectedEvent.narrowStart
  omega

theorem narrowScale_pos (C : Objects.CorrectedEvent.Constants) (n : ℕ) : 0 < Objects.CorrectedEvent.narrowScale C n := by
  unfold Objects.CorrectedEvent.narrowScale
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) C.rPos

theorem rpow_two_neg_le {x y : ℝ} (h : x ≤ y) : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem narrowSite_closedBall_subset (C : Objects.CorrectedEvent.Constants) {n : ℕ} (hn : Objects.CorrectedEvent.narrowStart C ≤ n)
    {v : ℂ} (hv : v ∈ Objects.CorrectedEvent.narrowSites C n) :
    closedBall v (Objects.CorrectedEvent.narrowScale C n) ⊆ bigAnn C := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (narrowStart_pos C).trans hn
  have hr := C.rPos
  have h1 : (2 : ℝ) ^ (-(n : ℝ) - 1) ≤ (2 : ℝ) ^ (-2 : ℝ) := rpow_two_neg_le (by linarith)
  have h2 : (2 : ℝ) ^ (-(n : ℝ) - 4) ≤ (2 : ℝ) ^ (-5 : ℝ) := rpow_two_neg_le (by linarith)
  have e1 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by norm_num [Real.rpow_neg, Real.rpow_two]
  have e2 : (2 : ℝ) ^ (-5 : ℝ) = 1 / 32 := by
    rw [Real.rpow_neg (by norm_num), show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  apply closedBall_subset_bigAnn_of_infDist C hv.2
  unfold Objects.CorrectedEvent.narrowScale
  rw [e1] at h1
  rw [e2] at h2
  nlinarith

theorem S6_congr (C : Objects.CorrectedEvent.Constants) (D₁ D₂ : LSCMetric) (g₁ g₂ : DistC)
    (h : ∀ n : ℕ, Objects.CorrectedEvent.narrowStart C ≤ n → ∀ v ∈ Objects.CorrectedEvent.narrowSites C n,
      Objects.CorrectedEvent.acr D₁ v (Objects.CorrectedEvent.narrowScale C n / 4) (Objects.CorrectedEvent.narrowScale C n) =
          Objects.CorrectedEvent.acr D₂ v (Objects.CorrectedEvent.narrowScale C n / 4) (Objects.CorrectedEvent.narrowScale C n) ∧
        LQGMetric.circleAvg g₁ (Objects.CorrectedEvent.narrowScale C n) v =
          LQGMetric.circleAvg g₂ (Objects.CorrectedEvent.narrowScale C n) v)
    (h0 : LQGMetric.circleAvg g₁ C.r 0 = LQGMetric.circleAvg g₂ C.r 0) :
    Objects.CorrectedEvent.S6 C D₁ g₁ ↔ Objects.CorrectedEvent.S6 C D₂ g₂ := by
  unfold Objects.CorrectedEvent.S6
  constructor
  · intro h1 n hn v hv
    obtain ⟨ha, hc⟩ := h n hn v hv
    have := h1 n hn v hv
    rw [ha, Objects.CorrectedEvent.normalizer, hc, h0] at this
    rw [Objects.CorrectedEvent.normalizer]
    exact this
  · intro h1 n hn v hv
    obtain ⟨ha, hc⟩ := h n hn v hv
    have := h1 n hn v hv
    rw [← ha, Objects.CorrectedEvent.normalizer, ← hc, ← h0] at this
    rw [Objects.CorrectedEvent.normalizer]
    exact this

theorem measurableSet_S6 (C : Objects.CorrectedEvent.Constants) (D : DistC → LSCMetric) (hD : Measurable D) :
    MeasurableSet {g | Objects.CorrectedEvent.S6 C (D g) g} := by
  have htest (n : ℕ) (v : ℂ) : MeasurableSet {g : DistC |
      ENNReal.ofReal ((2:ℝ) ^ (-(Objects.CorrectedEvent.zeta C)*(n:ℝ))) *
          Objects.CorrectedEvent.normalizer C g (Objects.CorrectedEvent.narrowScale C n) v ≤
        Objects.CorrectedEvent.acr (D g) v (Objects.CorrectedEvent.narrowScale C n / 4) (Objects.CorrectedEvent.narrowScale C n) ∧
      |LQGMetric.circleAvg g (Objects.CorrectedEvent.narrowScale C n) v - LQGMetric.circleAvg g C.r 0| ≤
        (2 + Objects.CorrectedEvent.zeta C) * (n : ℝ) * Real.log 2} := by
    have hN := Objects.ClauseMeasurability.measurable_normalizer C (Objects.CorrectedEvent.narrowScale C n) v
    have hA := (Objects.ClauseMeasurability.measurable_acr v (Objects.CorrectedEvent.narrowScale C n / 4) (Objects.CorrectedEvent.narrowScale C n)).comp hD
    have hc : Measurable fun g : DistC =>
        |LQGMetric.circleAvg g (Objects.CorrectedEvent.narrowScale C n) v - LQGMetric.circleAvg g C.r 0| :=
      ((LQGMetric.measurable_circleAvg_left _ v).sub
        (LQGMetric.measurable_circleAvg_left _ 0)).abs
    exact (measurableSet_le (measurable_const.mul hN) hA).inter
      (measurableSet_le hc measurable_const)
  have hsites (n : ℕ) : (Objects.CorrectedEvent.narrowSites C n).Countable :=
    (grid_countable _).mono fun z hz => hz.1
  have hn (n : ℕ) : MeasurableSet {g : DistC | Objects.CorrectedEvent.narrowStart C ≤ n →
      ∀ v ∈ Objects.CorrectedEvent.narrowSites C n,
      ENNReal.ofReal ((2:ℝ) ^ (-(Objects.CorrectedEvent.zeta C)*(n:ℝ))) *
          Objects.CorrectedEvent.normalizer C g (Objects.CorrectedEvent.narrowScale C n) v ≤
        Objects.CorrectedEvent.acr (D g) v (Objects.CorrectedEvent.narrowScale C n / 4) (Objects.CorrectedEvent.narrowScale C n) ∧
      |LQGMetric.circleAvg g (Objects.CorrectedEvent.narrowScale C n) v - LQGMetric.circleAvg g C.r 0| ≤
        (2 + Objects.CorrectedEvent.zeta C) * (n : ℝ) * Real.log 2} := by
    by_cases hnA : Objects.CorrectedEvent.narrowStart C ≤ n
    · simp only [hnA, true_implies]
      have h := MeasurableSet.biInter (hsites n) (fun v _ => htest n v)
      simpa only [← Set.ofPred_forall, Set.mem_iInter] using h
    · simp only [hnA, false_implies, Set.ofPred_true, MeasurableSet.univ]
  have h := MeasurableSet.iInter hn
  simpa only [← Set.ofPred_forall, Objects.CorrectedEvent.S6] using h

theorem aeEventIn_S6 (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (C : Objects.CorrectedEvent.Constants) (hCξ : C.ξ = ξ) :
    AEEventIn μ (fieldSigmaClosed0 id (bigAnn C)) {g | Objects.CorrectedEvent.S6 C (D g) g} := by
  obtain ⟨ψ, hψK, hψ1⟩ := exists_bigAnn_test C
  have hwhole : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  refine aeEventIn_closed0_of_det μ hμ ξ Q D hD (bigAnn C) ψ hψK hψ1 _
    (measurableSet_S6 C D hD.measurable) ?_ ?_
  · intro ε hε g₁ g₂ hB₁ hB₂ hL₁ hL₂ hint hres h1
    refine (S6_congr C (D g₁) (D g₂) g₁ g₂ ?_ ?_).mp h1
    · intro n hn v hv
      have hs := narrowScale_pos C n
      have hball := narrowSite_closedBall_subset C hn hv
      constructor
      · refine acr_eq_of_internal_eq (D g₁) (D g₂) hB₁ hB₂ hL₁ hL₂ _ hint v (by positivity)
          (by linarith) ?_
        intro x hx
        exact subset_nbhdO hε hball (mem_closedBall.mpr hx.2)
      · refine circleAvg_eq_of_restrictTo_eq hres hε (thickening_subset_nbhdO ?_)
        intro x hx
        rw [mem_sphere, abs_of_pos hs] at hx
        exact hball (mem_closedBall.mpr hx.le)
    · exact circleAvg_eq_of_restrictTo_eq hres hε
        (thickening_subset_nbhdO (sphere_r_subset_bigAnn C))
  · have hcirc : ∀ᵐ g ∂μ, ∀ n : ℕ, ∀ v ∈ Objects.CorrectedEvent.narrowSites C n, ∀ c : ℝ,
        LQGMetric.circleAvg (addConst g c) (Objects.CorrectedEvent.narrowScale C n) v =
          LQGMetric.circleAvg g (Objects.CorrectedEvent.narrowScale C n) v + c := by
      rw [ae_all_iff]
      intro n
      rw [ae_ball_iff ((grid_countable _).mono fun z hz => hz.1)]
      intro v _
      exact LQGMetric.CircleAvg.ae_circleAvg_addConst hμ.1 v (narrowScale_pos C n)
    filter_upwards [ae_scale_facts μ hμ ξ Q D hD (fun g => -(g ψ)) C, hcirc] with g hg hcg
    obtain ⟨hs, hc0⟩ := hg
    set c : ℝ := -(g ψ) with hcdef
    set e : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) with hedef
    have he0 : e ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have heTop : e ≠ ⊤ := ENNReal.ofReal_ne_top
    have hscale : ∀ x y : ℂ, D (addConst g c) (x, y) = e * D g (x, y) := fun x y => hs (x, y)
    unfold Objects.CorrectedEvent.S6
    constructor
    · intro h1 n hn v hv
      have := h1 n hn v hv
      have hN := normalizer_addConst C (hcg n v hv c)
      rw [hCξ] at hN
      rw [Objects.ProbabilityS3.acr_eq_mul_of_dist_scale (D g) (D (addConst g c)) e he0 heTop hscale,
        hN, scale_le_iff he0 heTop, hcg n v hv c, hc0] at this
      refine ⟨this.1, ?_⟩
      have h2 := this.2
      rwa [show LQGMetric.circleAvg g (Objects.CorrectedEvent.narrowScale C n) v + c -
          (LQGMetric.circleAvg g C.r 0 + c) = LQGMetric.circleAvg g (Objects.CorrectedEvent.narrowScale C n) v -
            LQGMetric.circleAvg g C.r 0 by ring] at h2
    · intro h1 n hn v hv
      have := h1 n hn v hv
      have hN := normalizer_addConst C (hcg n v hv c)
      rw [hCξ] at hN
      rw [Objects.ProbabilityS3.acr_eq_mul_of_dist_scale (D g) (D (addConst g c)) e he0 heTop hscale,
        hN, scale_le_iff he0 heTop, hcg n v hv c, hc0]
      refine ⟨this.1, ?_⟩
      rw [show LQGMetric.circleAvg g (Objects.CorrectedEvent.narrowScale C n) v + c -
          (LQGMetric.circleAvg g C.r 0 + c) = LQGMetric.circleAvg g (Objects.CorrectedEvent.narrowScale C n) v -
            LQGMetric.circleAvg g C.r 0 by ring]
      exact this.2

 

theorem aeEventIn_S7 (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (C : Objects.CorrectedEvent.Constants) (hCξ : C.ξ = ξ) (T : Objects.CorrectedEvent.TubeData) (hρ : 0 < T.netRadius)
    (hS7 : ∀ x ∈ T.netSites, closedBall x (2 * T.netRadius) ⊆ bigAnn C) :
    AEEventIn μ (fieldSigmaClosed0 id (bigAnn C)) {g | Objects.CorrectedEvent.S7 C T (D g) g} := by
  obtain ⟨ψ, hψK, hψ1⟩ := exists_bigAnn_test C
  refine aeEventIn_closed0_of_det μ hμ ξ Q D hD (bigAnn C) ψ hψK hψ1 _
    (Objects.ProbabilityS7S9.measurableSet_S7 hD.measurable C T hρ) ?_ ?_
  · intro ε hε g₁ g₂ _ _ _ _ hint hres h1
    have hN : Objects.CorrectedEvent.normalizer C g₁ C.r 0 = Objects.CorrectedEvent.normalizer C g₂ C.r 0 :=
      normalizer_eq_of_circleAvg_eq C (circleAvg_eq_of_restrictTo_eq hres hε
        (thickening_subset_nbhdO (sphere_r_subset_bigAnn C)))
    intro x hx
    have ha : Objects.CorrectedEvent.around (D g₁) x T.netRadius (2 * T.netRadius) =
        Objects.CorrectedEvent.around (D g₂) x T.netRadius (2 * T.netRadius) := by
      refine around_eq_of_internal_eq (D g₁) (D g₂) _ hint x hρ (by linarith) ?_
      intro y hy
      exact subset_nbhdO hε (hS7 x hx) (mem_closedBall.mpr hy.2.le)
    have := h1 x hx
    rw [ha, hN] at this
    exact this
  · filter_upwards [ae_scale_facts μ hμ ξ Q D hD (fun g => -(g ψ)) C] with g hg
    obtain ⟨hs, hc⟩ := hg
    have he0 : ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hN := normalizer_addConst C hc
    rw [hCξ] at hN
    change (∀ x ∈ T.netSites, Objects.CorrectedEvent.around (D (addConst g (-(g ψ)))) x T.netRadius (2*T.netRadius) <
        ENNReal.ofReal (C.A_internal / (2*T.netSites.card)) *
          Objects.CorrectedEvent.normalizer C (addConst g (-(g ψ))) C.r 0) ↔
      (∀ x ∈ T.netSites, Objects.CorrectedEvent.around (D g) x T.netRadius (2*T.netRadius) <
        ENNReal.ofReal (C.A_internal / (2*T.netSites.card)) * Objects.CorrectedEvent.normalizer C g C.r 0)
    simp only [Objects.ProbabilityS3.around_eq_mul_of_dist_scale (D g) (D (addConst g (-(g ψ)))) _ he0
      ENNReal.ofReal_ne_top (fun x y => hs (x, y)), hN, scale_lt_iff' he0 ENNReal.ofReal_ne_top]

 

theorem supRadius_pos (C : Objects.CorrectedEvent.Constants) (k : ℕ) : 0 < Objects.CorrectedEvent.supRadius C k := by
  unfold Objects.CorrectedEvent.supRadius
  have := C.supPos
  have := C.rPos
  positivity

theorem supGood_congr (C : Objects.CorrectedEvent.Constants) (D₁ D₂ : LSCMetric) (c : ℂ) (s : ℝ) (l : Objects.CorrectedEvent.Cell)
    (k : ℕ)
    (ha : Objects.CorrectedEvent.around D₁ (Objects.CorrectedEvent.cellCenter c s l) ((2+1/20) * Objects.CorrectedEvent.supRadius C k)
        ((3-1/20) * Objects.CorrectedEvent.supRadius C k) =
      Objects.CorrectedEvent.around D₂ (Objects.CorrectedEvent.cellCenter c s l) ((2+1/20) * Objects.CorrectedEvent.supRadius C k)
        ((3-1/20) * Objects.CorrectedEvent.supRadius C k))
    (hc : Objects.CorrectedEvent.acr D₁ (Objects.CorrectedEvent.cellCenter c s l) ((1+1/20) * Objects.CorrectedEvent.supRadius C k)
        ((2-1/20) * Objects.CorrectedEvent.supRadius C k) =
      Objects.CorrectedEvent.acr D₂ (Objects.CorrectedEvent.cellCenter c s l) ((1+1/20) * Objects.CorrectedEvent.supRadius C k)
        ((2-1/20) * Objects.CorrectedEvent.supRadius C k)) :
    Objects.CorrectedEvent.supGood C D₁ c s l k ↔ Objects.CorrectedEvent.supGood C D₂ c s l k := by
  unfold Objects.CorrectedEvent.supGood
  dsimp only
  rw [ha, hc]

theorem supGood_iff_of_scale (C : Objects.CorrectedEvent.Constants) (D₁ D₂ : LSCMetric) {e : ℝ≥0∞}
    (he0 : e ≠ 0) (heTop : e ≠ ⊤) (hscale : ∀ x y : ℂ, D₂ (x, y) = e * D₁ (x, y))
    (c : ℂ) (s : ℝ) (l : Objects.CorrectedEvent.Cell) (k : ℕ) :
    Objects.CorrectedEvent.supGood C D₂ c s l k ↔ Objects.CorrectedEvent.supGood C D₁ c s l k := by
  unfold Objects.CorrectedEvent.supGood
  dsimp only
  rw [Objects.ProbabilityS3.around_eq_mul_of_dist_scale D₁ D₂ e he0 heTop hscale,
    Objects.ProbabilityS3.acr_eq_mul_of_dist_scale D₁ D₂ e he0 heTop hscale,
    scale_lt_top_iff he0 heTop, scale_pos_iff he0, scale_lt_top_iff he0 heTop,
    scale_le_iff' he0 heTop]

theorem badLength_congr (C : Objects.CorrectedEvent.Constants) (D₁ D₂ : LSCMetric) (c : ℂ) (s : ℝ)
    (h : ∀ l : Objects.CorrectedEvent.Cell, ∀ k ∈ Finset.Icc 1 (Objects.CorrectedEvent.supK C),
      (Objects.CorrectedEvent.supGood C D₁ c s l k ↔ Objects.CorrectedEvent.supGood C D₂ c s l k)) :
    Objects.CorrectedEvent.badLength C D₁ c s = Objects.CorrectedEvent.badLength C D₂ c s := by
  classical
  unfold Objects.CorrectedEvent.badLength
  refine Finset.sum_congr rfl fun l _ => ?_
  have hb : Objects.CorrectedEvent.badCell C D₁ c s (Objects.CorrectedEvent.circleCell C s l) ↔
      Objects.CorrectedEvent.badCell C D₂ c s (Objects.CorrectedEvent.circleCell C s l) := by
    unfold Objects.CorrectedEvent.badCell
    constructor
    · intro h1 k hk h2
      exact h1 k hk ((h _ k hk).2 h2)
    · intro h1 k hk h2
      exact h1 k hk ((h _ k hk).1 h2)
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hb.1 h1) h2
  · exact absurd (hb.2 h2) h1
  · rfl

theorem S8_congr (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (D₁ D₂ : LSCMetric)
    (h : ∀ k : Fin T.K, ∀ l : Objects.CorrectedEvent.Cell, ∀ j ∈ Finset.Icc 1 (Objects.CorrectedEvent.supK C),
      (Objects.CorrectedEvent.supGood C D₁ (Objects.CorrectedEvent.innerCenter T k) T.blockRadius l j ↔
          Objects.CorrectedEvent.supGood C D₂ (Objects.CorrectedEvent.innerCenter T k) T.blockRadius l j) ∧
        (Objects.CorrectedEvent.supGood C D₁ (Objects.CorrectedEvent.outerCenter T k) T.blockRadius l j ↔
          Objects.CorrectedEvent.supGood C D₂ (Objects.CorrectedEvent.outerCenter T k) T.blockRadius l j)) :
    Objects.CorrectedEvent.S8 C T D₁ ↔ Objects.CorrectedEvent.S8 C T D₂ := by
  unfold Objects.CorrectedEvent.S8
  have hi : ∀ k : Fin T.K, Objects.CorrectedEvent.badLength C D₁ (Objects.CorrectedEvent.innerCenter T k) T.blockRadius =
      Objects.CorrectedEvent.badLength C D₂ (Objects.CorrectedEvent.innerCenter T k) T.blockRadius := fun k =>
    badLength_congr C D₁ D₂ _ _ fun l j hj => (h k l j hj).1
  have ho : ∀ k : Fin T.K, Objects.CorrectedEvent.badLength C D₁ (Objects.CorrectedEvent.outerCenter T k) T.blockRadius =
      Objects.CorrectedEvent.badLength C D₂ (Objects.CorrectedEvent.outerCenter T k) T.blockRadius := fun k =>
    badLength_congr C D₁ D₂ _ _ fun l j hj => (h k l j hj).2
  simp only [hi, ho]

theorem measurable_badLength (C : Objects.CorrectedEvent.Constants) (D : DistC → LSCMetric) (hD : Measurable D)
    (c : ℂ) (s : ℝ) : Measurable fun g : DistC => Objects.CorrectedEvent.badLength C (D g) c s := by
  classical
  have hgood (l : Objects.CorrectedEvent.Cell) (k : ℕ) : MeasurableSet {g : DistC | Objects.CorrectedEvent.supGood C (D g) c s l k} := by
    have hR := supRadius_pos C k
    have hA : Measurable fun g : DistC => Objects.CorrectedEvent.around (D g) (Objects.CorrectedEvent.cellCenter c s l)
        ((2+1/20) * Objects.CorrectedEvent.supRadius C k) ((3-1/20) * Objects.CorrectedEvent.supRadius C k) :=
      (Objects.ClauseMeasurability.measurable_around _ _ _ (by positivity) (by nlinarith)).comp hD
    have hB : Measurable fun g : DistC => Objects.CorrectedEvent.acr (D g) (Objects.CorrectedEvent.cellCenter c s l)
        ((1+1/20) * Objects.CorrectedEvent.supRadius C k) ((2-1/20) * Objects.CorrectedEvent.supRadius C k) :=
      (Objects.ClauseMeasurability.measurable_acr _ _ _).comp hD
    change MeasurableSet {g : DistC |
      Objects.CorrectedEvent.around (D g) (Objects.CorrectedEvent.cellCenter c s l) ((2+1/20) * Objects.CorrectedEvent.supRadius C k)
          ((3-1/20) * Objects.CorrectedEvent.supRadius C k) < ⊤ ∧
        0 < Objects.CorrectedEvent.acr (D g) (Objects.CorrectedEvent.cellCenter c s l) ((1+1/20) * Objects.CorrectedEvent.supRadius C k)
          ((2-1/20) * Objects.CorrectedEvent.supRadius C k) ∧
        Objects.CorrectedEvent.acr (D g) (Objects.CorrectedEvent.cellCenter c s l) ((1+1/20) * Objects.CorrectedEvent.supRadius C k)
          ((2-1/20) * Objects.CorrectedEvent.supRadius C k) < ⊤ ∧
        Objects.CorrectedEvent.around (D g) (Objects.CorrectedEvent.cellCenter c s l) ((2+1/20) * Objects.CorrectedEvent.supRadius C k)
          ((3-1/20) * Objects.CorrectedEvent.supRadius C k) ≤
          ENNReal.ofReal (1/2 * Real.exp (-C.ξ*C.A_max)) *
            Objects.CorrectedEvent.acr (D g) (Objects.CorrectedEvent.cellCenter c s l) ((1+1/20) * Objects.CorrectedEvent.supRadius C k)
              ((2-1/20) * Objects.CorrectedEvent.supRadius C k)}
    exact (measurableSet_lt hA measurable_const).inter
      ((measurableSet_lt measurable_const hB).inter
        ((measurableSet_lt hB measurable_const).inter (measurableSet_le hA (measurable_const.mul hB))))
  have hbad (l : Objects.CorrectedEvent.Cell) : MeasurableSet {g : DistC | Objects.CorrectedEvent.badCell C (D g) c s l} := by
    have h := MeasurableSet.biInter (Finset.Icc 1 (Objects.CorrectedEvent.supK C)).countable_toSet
      (fun k _ => (hgood l k).compl)
    have heq : {g : DistC | Objects.CorrectedEvent.badCell C (D g) c s l} =
        ⋂ k ∈ ((Finset.Icc 1 (Objects.CorrectedEvent.supK C) : Finset ℕ) : Set ℕ),
          {g : DistC | Objects.CorrectedEvent.supGood C (D g) c s l k}ᶜ := by
      ext g
      simp only [Objects.CorrectedEvent.badCell, Set.mem_iInter, Finset.mem_coe, Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [heq]
    exact h
  unfold Objects.CorrectedEvent.badLength
  refine Finset.measurable_sum _ fun l _ => ?_
  exact Measurable.ite (hbad _) measurable_const measurable_const

theorem measurableSet_S8 (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (D : DistC → LSCMetric)
    (hD : Measurable D) : MeasurableSet {g | Objects.CorrectedEvent.S8 C T (D g)} := by
  have h := MeasurableSet.iInter fun k : Fin T.K =>
    (measurableSet_le (measurable_badLength C D hD (Objects.CorrectedEvent.innerCenter T k) T.blockRadius)
      (measurable_const (a := C.lamConst*C.A_endpt*C.ρ*C.r))).inter
    (measurableSet_le (measurable_badLength C D hD (Objects.CorrectedEvent.outerCenter T k) T.blockRadius)
      (measurable_const (a := C.lamConst*C.A_endpt*C.ρ*C.r)))
  convert h using 1
  ext g
  simp only [Objects.CorrectedEvent.S8, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]

theorem aeEventIn_S8 (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (hS8 : ∀ k : Fin T.K, ∀ l : Objects.CorrectedEvent.Cell, ∀ j ∈ Finset.Icc 1 (Objects.CorrectedEvent.supK C),
      closedBall (Objects.CorrectedEvent.cellCenter (Objects.CorrectedEvent.innerCenter T k) T.blockRadius l)
          (3 * Objects.CorrectedEvent.supRadius C j) ⊆ bigAnn C ∧
        closedBall (Objects.CorrectedEvent.cellCenter (Objects.CorrectedEvent.outerCenter T k) T.blockRadius l)
          (3 * Objects.CorrectedEvent.supRadius C j) ⊆ bigAnn C) :
    AEEventIn μ (fieldSigmaClosed0 id (bigAnn C)) {g | Objects.CorrectedEvent.S8 C T (D g)} := by
  obtain ⟨ψ, hψK, hψ1⟩ := exists_bigAnn_test C
  have hwhole : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  refine aeEventIn_closed0_of_det μ hμ ξ Q D hD (bigAnn C) ψ hψK hψ1 _
    (measurableSet_S8 C T D hD.measurable) ?_ ?_
  · intro ε hε g₁ g₂ hB₁ hB₂ hL₁ hL₂ hint _ h1
    have hcell : ∀ (c : ℂ) (l : Objects.CorrectedEvent.Cell) (j : ℕ),
        closedBall (Objects.CorrectedEvent.cellCenter c T.blockRadius l) (3 * Objects.CorrectedEvent.supRadius C j) ⊆ bigAnn C →
        (Objects.CorrectedEvent.supGood C (D g₁) c T.blockRadius l j ↔ Objects.CorrectedEvent.supGood C (D g₂) c T.blockRadius l j) := by
      intro c l j hball
      have hR := supRadius_pos C j
      have hU := hball.trans (self_subset_thickening hε (bigAnn C))
      apply supGood_congr
      · refine around_eq_of_internal_eq (D g₁) (D g₂) _ hint _ (by positivity) (by nlinarith) ?_
        intro x hx
        exact hU (mem_closedBall.mpr (by have := hx.2; nlinarith))
      · refine acr_eq_of_internal_eq (D g₁) (D g₂) hB₁ hB₂ hL₁ hL₂ _ hint _ (by positivity)
          (by nlinarith) ?_
        intro x hx
        exact hU (mem_closedBall.mpr (by have := hx.2; nlinarith))
    refine (S8_congr C T (D g₁) (D g₂) fun k l j hj =>
      ⟨hcell _ l j (hS8 k l j hj).1, hcell _ l j (hS8 k l j hj).2⟩).mp h1
  · filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD (fun g => -(g ψ))] with g hs
    have he0 : ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    exact S8_congr C T _ _ fun k l j _ =>
      ⟨supGood_iff_of_scale C (D g) _ he0 ENNReal.ofReal_ne_top (fun x y => hs (x, y)) _ _ _ _,
        supGood_iff_of_scale C (D g) _ he0 ENNReal.ofReal_ne_top (fun x y => hs (x, y)) _ _ _ _⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
