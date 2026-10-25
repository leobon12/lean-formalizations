import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.ClauseLocalA




 











set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter
open LQGMetric.Blueprint
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC restrictTo addConst)

theorem isClosed_bigAnn (C : Objects.CorrectedEvent.Constants) : IsClosed (bigAnn C) := by
  have h1 : IsClosed {x : ℂ | C.r ≤ dist x 0} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have h2 : IsClosed {x : ℂ | dist x 0 ≤ 4 * C.r} :=
    isClosed_le (continuous_id.dist continuous_const) continuous_const
  exact h1.inter h2

theorem closedBall_subset_bigAnn_of_ball (C : Objects.CorrectedEvent.Constants) {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ball z ρ ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) : closedBall z ρ ⊆ bigAnn C := by
  rw [← closure_ball z hρ.ne']
  exact closure_minimal (h.trans (ann_subset_bigAnn C le_rfl le_rfl)) (isClosed_bigAnn C)

theorem grid_countable (a : ℝ) : (Objects.CorrectedEvent.grid a).Countable := by
  have h : Objects.CorrectedEvent.grid a ⊆ range (fun mn : ℤ × ℤ =>
      ((a * mn.1 : ℝ) : ℂ) + ((a * mn.2 : ℝ) : ℂ) * Complex.I) := by
    rintro z ⟨m, n, rfl⟩
    exact ⟨(m, n), rfl⟩
  exact (countable_range _).mono h

 

theorem S3_congr (C : Objects.CorrectedEvent.Constants) (D₁ D₂ : LSCMetric)
    (h : ∀ k : ℕ, C.k0 ≤ k → ∀ z ∈ Objects.CorrectedEvent.regSites C k, ∀ j ∈ Finset.Icc 1 (Objects.CorrectedEvent.regK k),
      (Objects.CorrectedEvent.regGood C D₁ (4 ^ j * Objects.CorrectedEvent.lam k * C.r) z ↔
        Objects.CorrectedEvent.regGood C D₂ (4 ^ j * Objects.CorrectedEvent.lam k * C.r) z)) :
    Objects.CorrectedEvent.S3 C D₁ ↔ Objects.CorrectedEvent.S3 C D₂ := by
  classical
  unfold Objects.CorrectedEvent.S3
  have hf : ∀ k : ℕ, C.k0 ≤ k → ∀ z ∈ Objects.CorrectedEvent.regSites C k,
      (Finset.Icc 1 (Objects.CorrectedEvent.regK k)).filter
          (fun j => Objects.CorrectedEvent.regGood C D₁ (4 ^ j * Objects.CorrectedEvent.lam k * C.r) z) =
        (Finset.Icc 1 (Objects.CorrectedEvent.regK k)).filter
          (fun j => Objects.CorrectedEvent.regGood C D₂ (4 ^ j * Objects.CorrectedEvent.lam k * C.r) z) := by
    intro k hk z hz
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj, hg⟩
      exact ⟨hj, (h k hk z hz j hj).1 hg⟩
    · rintro ⟨hj, hg⟩
      exact ⟨hj, (h k hk z hz j hj).2 hg⟩
  constructor
  · intro h1 k hk z hz
    have := h1 k hk z hz
    rwa [hf k hk z hz] at this
  · intro h1 k hk z hz
    have := h1 k hk z hz
    rwa [← hf k hk z hz] at this

theorem regSite_closedBall_subset (C : Objects.CorrectedEvent.Constants) {k : ℕ} {z : ℂ}
    (hz : z ∈ Objects.CorrectedEvent.regSites C k) {j : ℕ} (hj : j ∈ Finset.Icc 1 (Objects.CorrectedEvent.regK k)) :
    closedBall z (2 * (4 ^ j * Objects.CorrectedEvent.lam k * C.r)) ⊆ bigAnn C := by
  have hr := C.rPos
  have hlam : 0 < Objects.CorrectedEvent.lam k := Real.rpow_pos_of_pos (by norm_num) _
  have hjK : j ≤ Objects.CorrectedEvent.regK k := (Finset.mem_Icc.mp hj).2
  have hpow : (4 : ℝ) ^ j ≤ 4 ^ Objects.CorrectedEvent.regK k := pow_le_pow_right₀ (by norm_num) hjK
  have hρ : 0 < 2 * 4 ^ Objects.CorrectedEvent.regK k * Objects.CorrectedEvent.lam k * C.r := by positivity
  refine (closedBall_subset_closedBall ?_).trans
    (closedBall_subset_bigAnn_of_ball C hρ hz.2)
  have := mul_le_mul_of_nonneg_right hpow (mul_pos hlam hr).le
  nlinarith

theorem regGood_iff_of_local (C : Objects.CorrectedEvent.Constants) (D₁ D₂ : LSCMetric)
    (hB₁ : BiLipschitz.Barrier.Barrier D₁) (hB₂ : BiLipschitz.Barrier.Barrier D₂) (hL₁ : D₁.IsLengthSpace) (hL₂ : D₂.IsLengthSpace)
    {ε : ℝ} (hε : 0 < ε)
    (hint : D₁.internal (thickening ε (bigAnn C)) = D₂.internal (thickening ε (bigAnn C)))
    (w : ℂ) (s : ℝ) (hs : 0 < s) (hball : closedBall w (2 * s) ⊆ bigAnn C) :
    Objects.CorrectedEvent.regGood C D₁ s w ↔ Objects.CorrectedEvent.regGood C D₂ s w := by
  have hU : closedBall w (2 * s) ⊆ thickening ε (bigAnn C) :=
    hball.trans (self_subset_thickening hε _)
  apply Objects.ProbabilityS3.regGood_iff_of_internal_eq C D₁ D₂ hB₁ hB₂ hL₁ hL₂ w s hs _
  · intro x hx
    apply hU
    rw [mem_closedBall, dist_eq_norm]
    exact hx.2
  · intro x hx
    apply hU
    change x ∈ ball w (2 * s) \ closure (ball w s) at hx
    exact ball_subset_closedBall hx.1
  · exact hint

theorem aeEventIn_S3 (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (C : Objects.CorrectedEvent.Constants) :
    AEEventIn μ (fieldSigmaClosed0 id (bigAnn C)) {g | Objects.CorrectedEvent.S3 C (D g)} := by
  obtain ⟨ψ, hψK, hψ1⟩ := exists_bigAnn_test C
  have hwhole : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  refine aeEventIn_closed0_of_det μ hμ ξ Q D hD (bigAnn C) ψ hψK hψ1 _
    (Objects.ClauseMeasurability.measurableSet_S3 C D hD.measurable) ?_ ?_
  · intro ε hε g₁ g₂ hB₁ hB₂ hL₁ hL₂ hint _ h1
    refine (S3_congr C (D g₁) (D g₂) ?_).mp h1
    intro k _ z hz j hj
    have hlam : 0 < Objects.CorrectedEvent.lam k := Real.rpow_pos_of_pos (by norm_num) _
    exact regGood_iff_of_local C (D g₁) (D g₂) hB₁ hB₂ hL₁ hL₂ hε hint z _
      (by have := C.rPos; positivity) (regSite_closedBall_subset C hz hj)
  · filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD (fun g => -(g ψ))] with g hs
    have he0 : ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    refine S3_congr C _ _ fun k _ z _ j _ => ?_
    exact Objects.ProbabilityS3.regGood_iff_of_dist_scale C (D g) (D (addConst g (-(g ψ)))) _ he0
      ENNReal.ofReal_ne_top (fun x y => hs (x, y)) z _

 

theorem compareScale_pos (k : ℕ) : 0 < Objects.CorrectedEvent.compareScale k :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem cann_middle_nonempty (C : Objects.CorrectedEvent.Constants) :
    (Objects.CorrectedEvent.cann 0 (1.5 * C.r) (3 * C.r)).Nonempty := by
  have hr := C.rPos
  refine ⟨((2 * C.r : ℝ) : ℂ), ?_⟩
  change 1.5 * C.r ≤ dist ((2 * C.r : ℝ) : ℂ) 0 ∧ dist ((2 * C.r : ℝ) : ℂ) 0 ≤ 3 * C.r
  rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  constructor <;> linarith

theorem isCompact_cann (w : ℂ) (a b : ℝ) : IsCompact (Objects.CorrectedEvent.cann w a b) := by
  have heq : Objects.CorrectedEvent.cann w a b = closedBall w b ∩ (ball w a)ᶜ := by
    ext x
    simp only [Objects.CorrectedEvent.cann, mem_ofPred_eq, mem_inter_iff, mem_closedBall,
      mem_compl_iff, mem_ball, not_lt]
    tauto
  rw [heq]
  exact (isCompact_closedBall w b).inter_right isOpen_ball.isClosed_compl

 

theorem closedBall_subset_bigAnn_of_infDist (C : Objects.CorrectedEvent.Constants) {z : ℂ} {δ R : ℝ}
    (hz : infDist z (Objects.CorrectedEvent.cann 0 (1.5 * C.r) (3 * C.r)) ≤ δ) (hRδ : R + δ ≤ C.r / 2) :
    closedBall z R ⊆ bigAnn C := by
  obtain ⟨y, hy, hyz⟩ := (isCompact_cann 0 (1.5 * C.r) (3 * C.r)).exists_infDist_eq_dist
    (cann_middle_nonempty C) z
  intro x hx
  rw [mem_closedBall] at hx
  have hzy : dist z y ≤ δ := hyz ▸ hz
  have hy1 : 1.5 * C.r ≤ dist y 0 := hy.1
  have hy2 : dist y 0 ≤ 3 * C.r := hy.2
  have hr := C.rPos
  have t1 : dist x 0 ≤ dist x z + dist z 0 := dist_triangle x z 0
  have t2 : dist z 0 ≤ dist z y + dist y 0 := dist_triangle z y 0
  have t4 : dist y 0 ≤ dist y x + dist x 0 := dist_triangle y x 0
  have t5 : dist y x ≤ dist y z + dist z x := dist_triangle y z x
  have e1 : dist y z = dist z y := dist_comm y z
  have e2 : dist z x = dist x z := dist_comm z x
  constructor <;> linarith

theorem S5_congr (C : Objects.CorrectedEvent.Constants) (D₁ D₂ : LSCMetric)
    (h : ∀ k : ℕ, Objects.CorrectedEvent.compareScale k ≤ C.A_nar → ∀ z ∈ Objects.CorrectedEvent.compareSites C k,
      Objects.CorrectedEvent.around D₁ z ((11/5) * Objects.CorrectedEvent.compareScale k * C.r) ((14/5) * Objects.CorrectedEvent.compareScale k * C.r) =
          Objects.CorrectedEvent.around D₂ z ((11/5) * Objects.CorrectedEvent.compareScale k * C.r) ((14/5) * Objects.CorrectedEvent.compareScale k * C.r) ∧
        Objects.CorrectedEvent.acr D₁ z ((3/10) * Objects.CorrectedEvent.compareScale k * C.r) ((9/20) * Objects.CorrectedEvent.compareScale k * C.r) =
          Objects.CorrectedEvent.acr D₂ z ((3/10) * Objects.CorrectedEvent.compareScale k * C.r) ((9/20) * Objects.CorrectedEvent.compareScale k * C.r)) :
    Objects.CorrectedEvent.S5 C D₁ ↔ Objects.CorrectedEvent.S5 C D₂ := by
  unfold Objects.CorrectedEvent.S5
  constructor
  · intro h1 k hk z hz
    have := h1 k hk z hz
    obtain ⟨ha, hc⟩ := h k hk z hz
    dsimp only at this ⊢
    rwa [← ha, ← hc]
  · intro h1 k hk z hz
    have := h1 k hk z hz
    obtain ⟨ha, hc⟩ := h k hk z hz
    dsimp only at this ⊢
    rwa [ha, hc]

theorem S5_iff_of_scale (C : Objects.CorrectedEvent.Constants) (D₁ D₂ : LSCMetric) {e : ℝ≥0∞}
    (he0 : e ≠ 0) (heTop : e ≠ ⊤) (hscale : ∀ x y : ℂ, D₂ (x, y) = e * D₁ (x, y)) :
    Objects.CorrectedEvent.S5 C D₂ ↔ Objects.CorrectedEvent.S5 C D₁ := by
  unfold Objects.CorrectedEvent.S5
  simp only [Objects.ProbabilityS3.around_eq_mul_of_dist_scale D₁ D₂ e he0 heTop hscale,
    Objects.ProbabilityS3.acr_eq_mul_of_dist_scale D₁ D₂ e he0 heTop hscale,
    scale_le_iff' he0 heTop, scale_lt_top_iff he0 heTop, scale_pos_iff he0]

theorem measurableSet_S5 (C : Objects.CorrectedEvent.Constants) (D : DistC → LSCMetric) (hD : Measurable D) :
    MeasurableSet {g | Objects.CorrectedEvent.S5 C (D g)} := by
  have hr := C.rPos
  have htest (k : ℕ) (z : ℂ) : MeasurableSet {g : DistC |
      Objects.CorrectedEvent.around (D g) z ((11/5) * Objects.CorrectedEvent.compareScale k * C.r) ((14/5) * Objects.CorrectedEvent.compareScale k * C.r) ≤
          ENNReal.ofReal (Objects.CorrectedEvent.compareScale k ^ (-(1:ℝ)/8)) *
            Objects.CorrectedEvent.acr (D g) z ((3/10) * Objects.CorrectedEvent.compareScale k * C.r)
              ((9/20) * Objects.CorrectedEvent.compareScale k * C.r) ∧
        Objects.CorrectedEvent.around (D g) z ((11/5) * Objects.CorrectedEvent.compareScale k * C.r)
            ((14/5) * Objects.CorrectedEvent.compareScale k * C.r) < ⊤ ∧
        0 < Objects.CorrectedEvent.acr (D g) z ((3/10) * Objects.CorrectedEvent.compareScale k * C.r)
            ((9/20) * Objects.CorrectedEvent.compareScale k * C.r) ∧
        Objects.CorrectedEvent.acr (D g) z ((3/10) * Objects.CorrectedEvent.compareScale k * C.r)
            ((9/20) * Objects.CorrectedEvent.compareScale k * C.r) < ⊤} := by
    have ht := compareScale_pos k
    have hA : Measurable fun g : DistC => Objects.CorrectedEvent.around (D g) z
        ((11/5) * Objects.CorrectedEvent.compareScale k * C.r) ((14/5) * Objects.CorrectedEvent.compareScale k * C.r) :=
      (Objects.ClauseMeasurability.measurable_around z _ _ (by positivity) (by nlinarith)).comp hD
    have hB : Measurable fun g : DistC => Objects.CorrectedEvent.acr (D g) z
        ((3/10) * Objects.CorrectedEvent.compareScale k * C.r) ((9/20) * Objects.CorrectedEvent.compareScale k * C.r) :=
      (Objects.ClauseMeasurability.measurable_acr z _ _).comp hD
    exact (measurableSet_le hA (measurable_const.mul hB)).inter
      ((measurableSet_lt hA measurable_const).inter
        ((measurableSet_lt measurable_const hB).inter (measurableSet_lt hB measurable_const)))
  have hsites (k : ℕ) : (Objects.CorrectedEvent.compareSites C k).Countable :=
    (grid_countable _).mono fun z hz => hz.1
  have hk (k : ℕ) : MeasurableSet {g : DistC | Objects.CorrectedEvent.compareScale k ≤ C.A_nar →
      ∀ z ∈ Objects.CorrectedEvent.compareSites C k,
      Objects.CorrectedEvent.around (D g) z ((11/5) * Objects.CorrectedEvent.compareScale k * C.r) ((14/5) * Objects.CorrectedEvent.compareScale k * C.r) ≤
          ENNReal.ofReal (Objects.CorrectedEvent.compareScale k ^ (-(1:ℝ)/8)) *
            Objects.CorrectedEvent.acr (D g) z ((3/10) * Objects.CorrectedEvent.compareScale k * C.r)
              ((9/20) * Objects.CorrectedEvent.compareScale k * C.r) ∧
        Objects.CorrectedEvent.around (D g) z ((11/5) * Objects.CorrectedEvent.compareScale k * C.r)
            ((14/5) * Objects.CorrectedEvent.compareScale k * C.r) < ⊤ ∧
        0 < Objects.CorrectedEvent.acr (D g) z ((3/10) * Objects.CorrectedEvent.compareScale k * C.r)
            ((9/20) * Objects.CorrectedEvent.compareScale k * C.r) ∧
        Objects.CorrectedEvent.acr (D g) z ((3/10) * Objects.CorrectedEvent.compareScale k * C.r)
            ((9/20) * Objects.CorrectedEvent.compareScale k * C.r) < ⊤} := by
    by_cases hkA : Objects.CorrectedEvent.compareScale k ≤ C.A_nar
    · simp only [hkA, true_implies]
      have h := MeasurableSet.biInter (hsites k) (fun z _ => htest k z)
      simpa only [← Set.ofPred_forall, Set.mem_iInter] using h
    · simp only [hkA, false_implies, Set.ofPred_true, MeasurableSet.univ]
  have h := MeasurableSet.iInter hk
  simpa only [← Set.ofPred_forall, Objects.CorrectedEvent.S5] using h

theorem compareSite_closedBall_subset (C : Objects.CorrectedEvent.Constants) (hnar : C.A_nar < 1 / 6)
    {k : ℕ} (hk : Objects.CorrectedEvent.compareScale k ≤ C.A_nar) {z : ℂ} (hz : z ∈ Objects.CorrectedEvent.compareSites C k) :
    closedBall z ((14/5) * Objects.CorrectedEvent.compareScale k * C.r) ⊆ bigAnn C := by
  have ht := compareScale_pos k
  have hr := C.rPos
  apply closedBall_subset_bigAnn_of_infDist C hz.2
  nlinarith

theorem aeEventIn_S5 (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (C : Objects.CorrectedEvent.Constants) (hnar : C.A_nar < 1 / 6) :
    AEEventIn μ (fieldSigmaClosed0 id (bigAnn C)) {g | Objects.CorrectedEvent.S5 C (D g)} := by
  obtain ⟨ψ, hψK, hψ1⟩ := exists_bigAnn_test C
  have hwhole : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  refine aeEventIn_closed0_of_det μ hμ ξ Q D hD (bigAnn C) ψ hψK hψ1 _
    (measurableSet_S5 C D hD.measurable) ?_ ?_
  · intro ε hε g₁ g₂ hB₁ hB₂ hL₁ hL₂ hint _ h1
    refine (S5_congr C (D g₁) (D g₂) ?_).mp h1
    intro k hk z hz
    have ht := compareScale_pos k
    have hr := C.rPos
    have hball := compareSite_closedBall_subset C hnar hk hz
    have hU : closedBall z ((14/5) * Objects.CorrectedEvent.compareScale k * C.r) ⊆ thickening ε (bigAnn C) :=
      hball.trans (self_subset_thickening hε _)
    constructor
    · refine around_eq_of_internal_eq (D g₁) (D g₂) _ hint z (by positivity) (by nlinarith) ?_
      intro x hx
      exact hU (mem_closedBall.mpr hx.2.le)
    · refine acr_eq_of_internal_eq (D g₁) (D g₂) hB₁ hB₂ hL₁ hL₂ _ hint z (by positivity)
        (by nlinarith) ?_
      intro x hx
      exact hU (mem_closedBall.mpr (by have := hx.2; nlinarith))
  · filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD (fun g => -(g ψ))] with g hs
    have he0 : ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    exact S5_iff_of_scale C (D g) (D (addConst g (-(g ψ)))) he0 ENNReal.ofReal_ne_top
      (fun x y => hs (x, y))

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
