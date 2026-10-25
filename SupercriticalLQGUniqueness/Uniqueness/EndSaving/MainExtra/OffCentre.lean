import SupercriticalLQGUniqueness.Uniqueness.EndSaving.CircleRange.CircleRange
import LQGMetric.Papers.LM.L3_4M6
import LQGMetric.Papers.LM.L3_1N2P5
import LQGMetric.Papers.LM.L3_1InQ
import LQGMetric.Papers.GM.S3.DeterministicScale
import LQGMetric.Papers.CONF.S3D110A




 


















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra

open LQGMetric (DistC IsWholePlaneGFF IsNormalizedWPGFF addConst affineComp circleAvg)
open LQGMetric.Blueprint (countOcc AnnulusIterHyp fieldSigma fieldSigmaClosed0 annulus)

 

 


theorem lmLem3_1b :
    ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → ∀ p : ℝ, 0 < p → p < 1 →
      ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ b < 1 ∧ 0 < c ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsNormalizedWPGFF h P →
          ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω), AnnulusIterHyp h s₁ s₂ r E →
          (∀ k, ENNReal.ofReal p ≤ P (E k)) →
          ∀ K : ℕ, P {ω | (countOcc E K ω : ℝ) < b * K} ≤
            ENNReal.ofReal (c * Real.exp (-a * K)) := by
  intro s₁ s₂ hs₁ hs₁₂ hs₂ p hp0 hp1
  obtain ⟨C, M₁, M₀, c₀, hC, hc₀, H⟩ :=
    LQGMetric.LM.lmAnnulusIterInputQ_of_canon (fun s₁ _ _ => LQGMetric.LM.lmNestCanonLeaf s₁)
      s₁ s₂ hs₁ hs₁₂ hs₂
  set M : ℝ := max (M₀ 1 (1 / 2)) (M₁ p) with hM
  set q : ℝ := min ((p / 4) ^ 4 / C M) 1 with hq
  have hq0 : 0 < q := lt_min (by have := hC M; positivity) one_pos
  have hq1 : q ≤ 1 := min_le_right _ _
  set θ : ℝ := 1 - q + q * Real.exp (-1) with hθ
  have hexp1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hexp0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hθ1 : θ < 1 := by rw [hθ]; nlinarith
  have hθe : Real.exp (-1) ≤ θ := by rw [hθ]; nlinarith
  have hθ0 : 0 < θ := hexp0.trans_le hθe
  set γ : ℝ := -Real.log θ / 2 with hγ
  have hlogθ : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  have hlogθ1 : -1 ≤ Real.log θ := by
    have := Real.log_le_log hexp0 hθe
    rwa [Real.log_exp] at this
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hγ1 : γ ≤ 1 / 2 := by rw [hγ]; linarith
  refine ⟨min 1 (γ * (1 / 2)), γ * (1 / 2), c₀ 1 (1 / 2) + 1,
    lt_min one_pos (by positivity), by positivity, by nlinarith,
    by linarith [hc₀ 1 (1 / 2)], ?_⟩
  intro Ω _ P _ h hh r E hE hpE K
  obtain ⟨hr0, hrA, hrs, hEm⟩ := hE
  obtain ⟨Good, hGood, hmono, h38, h310⟩ := H P h hh r hr0 hrA hrs
  have hs₁1 : s₁ ≤ 1 := by linarith
  have hqk : ∀ k, ∀ᵐ ω ∂P, ω ∈ Good M k →
      q ≤ P[(E k).indicator (fun _ => (1 : ℝ)) | LQGMetric.LM.lmFiltration P hh.1 hr0 hrA k] ω := by
    intro k
    filter_upwards [h38 p hp0 hp1.le M (le_max_right _ _) k (E k) (hEm k)] with ω hω hG
    exact (min_le_left _ _).trans ((hω hG).2 (LQGMetric.LM.real_ge_of_ofReal_le (hpE k)))
  have hρ : Real.exp (1 * γ) * (1 - q + q * Real.exp (-1)) ≤ Real.exp (-γ) := by
    rw [one_mul, ← hθ, ← Real.exp_log hθ0, ← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [hγ]
    linarith
  have hmain := LQGMetric.LM.prob_countOcc_lt_le (LQGMetric.LM.lmFiltration P hh.1 hr0 hrA)
    (G := Good M) (E := E) (hGood M)
    (fun k => LQGMetric.LM.annSigma_le_lmFiltration hh.1 hr0 hrA hs₁1 hrs k _ (hEm k))
    (q := q) (l := 1) (α := γ) (β := 1 / 2) (b := γ * (1 / 2)) (γ := γ)
    hq0.le hq1 zero_le_one hγ0.le le_rfl hγ0.le hρ hqk K
  have hgood := (LQGMetric.LM.prob_countOcc_mono (P := P) (G := Good (M₀ 1 (1 / 2)))
    (G' := Good M) (fun k => hmono _ _ k (le_max_left _ _)) (1 / 2) K).trans
    (h310 1 one_pos (1 / 2) (by norm_num) (by norm_num) K)
  apply LQGMetric.LM.measure_le_ofReal_of_real
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have ha1 : Real.exp (-1 * K) ≤ Real.exp (-min 1 (γ * (1 / 2)) * K) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left 1 (γ * (1 / 2))])
  have ha2 : Real.exp (-(γ * (1 / 2)) * K) ≤ Real.exp (-min 1 (γ * (1 / 2)) * K) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right 1 (γ * (1 / 2))])
  calc P.real {ω | (countOcc E K ω : ℝ) < γ * (1 / 2) * K}
      ≤ c₀ 1 (1 / 2) * Real.exp (-1 * K) + Real.exp (-(γ * (1 / 2)) * K) := by linarith
    _ ≤ c₀ 1 (1 / 2) * Real.exp (-min 1 (γ * (1 / 2)) * K) +
          Real.exp (-min 1 (γ * (1 / 2)) * K) := by
        gcongr
        · exact (hc₀ 1 (1 / 2)).le
    _ = (c₀ 1 (1 / 2) + 1) * Real.exp (-min 1 (γ * (1 / 2)) * K) := by ring

 

 
theorem countOcc_congr_pos {Ω : Type} {E E' : ℕ → Set Ω} (hEE : ∀ k, 1 ≤ k → E k = E' k)
    (K : ℕ) (ω : Ω) : countOcc E K ω = countOcc E' K ω := by
  classical
  unfold countOcc
  congr 1
  refine Finset.filter_congr fun k hk => ?_
  rw [hEE k (Finset.mem_Icc.mp hk).1]

 
theorem ae_countOcc_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {E E' : ℕ → Set Ω}
    (hEE : ∀ k, 1 ≤ k → E k =ᵐ[P] E' k) (K : ℕ) :
    ∀ᵐ ω ∂P, countOcc E K ω = countOcc E' K ω := by
  classical
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, 1 ≤ k → (ω ∈ E k ↔ ω ∈ E' k) := by
    refine ae_all_iff.2 fun k => ?_
    by_cases hk : 1 ≤ k
    · filter_upwards [(hEE k hk).mem_iff] with ω hω _ using hω
    · exact Eventually.of_forall fun ω hk' => absurd hk' hk
  filter_upwards [hall] with ω hω
  unfold countOcc
  congr 1
  exact Finset.filter_congr fun k hk => hω k (Finset.mem_Icc.mp hk).1

 
theorem measure_countOcc_lt_congr {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {E E' : ℕ → Set Ω} (hEE : ∀ k, 1 ≤ k → E k =ᵐ[P] E' k) (b : ℝ) (K : ℕ) :
    P {ω | (countOcc E K ω : ℝ) < b * K} = P {ω | (countOcc E' K ω : ℝ) < b * K} := by
  refine measure_congr ?_
  filter_upwards [ae_countOcc_eq hEE K] with ω hω
  simp only [eq_iff_iff]
  rw [hω]

 

 
theorem half_one_add_sq_gt {t : ℝ} (ht : t < 1) : t < ((1 + t) / 2) ^ 2 := by
  nlinarith [sq_nonneg (1 - t)]

 

theorem closedAnnulus_subset_annulus {s₀ s₁ s₂ r : ℝ} {z w : ℂ} (hr : 0 < r)
    (hs₀₁ : s₀ < s₁) (hs₀₂ : s₂ + s₀ < 1) (hz : dist z w ≤ s₀ * r) :
    {x : ℂ | s₁ * r ≤ dist x z ∧ dist x z ≤ s₂ * r} ⊆
      (annulus w ((s₁ - s₀) * ((1 + (s₂ + s₀)) / 2 * r))
        ((1 + (s₂ + s₀)) / 2 * ((1 + (s₂ + s₀)) / 2 * r)) : Set ℂ) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have hμ1 : (1 + (s₂ + s₀)) / 2 < 1 := by linarith
  have hμ2 := half_one_add_sq_gt hs₀₂
  have ht₁ := dist_triangle x w z
  have ht₂ := dist_triangle x z w
  have hzw : dist w z = dist z w := dist_comm w z
  change (s₁ - s₀) * ((1 + (s₂ + s₀)) / 2 * r) < ‖x - w‖ ∧
    ‖x - w‖ < (1 + (s₂ + s₀)) / 2 * ((1 + (s₂ + s₀)) / 2 * r)
  rw [← dist_eq_norm]
  have hρ : 0 < s₁ - s₀ := by linarith
  constructor
  · have h1 : (s₁ - s₀) * r ≤ dist x w := by nlinarith
    have h2 : (s₁ - s₀) * ((1 + (s₂ + s₀)) / 2 * r) < (s₁ - s₀) * r := by
      have : (1 + (s₂ + s₀)) / 2 * r < r := by nlinarith
      exact mul_lt_mul_of_pos_left this hρ
    linarith
  · have h1 : dist x w ≤ (s₂ + s₀) * r := by nlinarith
    have h2 : (s₂ + s₀) * r < (1 + (s₂ + s₀)) / 2 * ((1 + (s₂ + s₀)) / 2 * r) := by
      have : (1 + (s₂ + s₀)) / 2 * ((1 + (s₂ + s₀)) / 2 * r) = ((1 + (s₂ + s₀)) / 2) ^ 2 * r := by
        ring
      rw [this]
      exact mul_lt_mul_of_pos_right hμ2 hr
    linarith

 
theorem isCompact_closedAnnulusSet (z : ℂ) (a b : ℝ) :
    IsCompact {x : ℂ | a ≤ dist x z ∧ dist x z ≤ b} := by
  have hinner : IsClosed {x : ℂ | a ≤ dist x z} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have houter : IsCompact {x : ℂ | dist x z ≤ b} := by
    simpa only [Metric.closedBall] using isCompact_closedBall z b
  exact houter.inter_left hinner

 

theorem fieldSigmaClosed0_le_translated {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (w : ℂ) (a d : Ω → ℝ) {K : Set ℂ} (hK : IsCompact K) {ρ₁ ρ₂ : ℝ}
    (hKV : K ⊆ (annulus w ρ₁ ρ₂ : Set ℂ)) :
    fieldSigmaClosed0 h K ≤ fieldSigma (fun ω =>
      addConst (addConst (affineComp 1 w (h ω)) (a ω)) (d ω)) (annulus 0 ρ₁ ρ₂) := by
  set h' : Ω → DistC := fun ω => addConst (h ω) (a ω)
  have hUV : ∀ y : ℂ, y ∈ annulus 0 ρ₁ ρ₂ ↔ (1 : ℝ) • y + w ∈ annulus w ρ₁ ρ₂ := by
    intro y
    change ρ₁ < ‖y - 0‖ ∧ ‖y - 0‖ < ρ₂ ↔ ρ₁ < ‖(1 : ℝ) • y + w - w‖ ∧ ‖(1 : ℝ) • y + w - w‖ < ρ₂
    simp only [sub_zero, one_smul, add_sub_cancel_right]
  have e : (fun ω => affineComp 1 w (addConst (h' ω) (d ω))) =
      fun ω => addConst (addConst (affineComp 1 w (h ω)) (a ω)) (d ω) := by
    funext ω
    simp only [h', LQGMetric.GM.affineComp_addConst one_pos]
  calc fieldSigmaClosed0 h K = fieldSigmaClosed0 h' K :=
        (LQGMetric.CONF.fieldSigmaClosed0_addConst h a K).symm
    _ ≤ fieldSigma (fun ω => addConst (h' ω) (d ω)) (annulus w ρ₁ ρ₂) :=
        EndSaving.CircleRange.fieldSigmaClosed0_le_recentered_open h' d K _ hK hKV
    _ ≤ fieldSigma (fun ω => affineComp 1 w (addConst (h' ω) (d ω))) (annulus 0 ρ₁ ρ₂) :=
        LQGMetric.GM.fieldSigma_le_affineComp one_pos hUV _
    _ = _ := by rw [e]

 

 

theorem isNormalizedWPGFF_translate {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (w : ℂ) :
    IsNormalizedWPGFF (fun ω => addConst (affineComp 1 w (h ω))
      (-circleAvg (affineComp 1 w (h ω)) 1 0)) P := by
  have hz := hh.affineComp one_pos w
  refine ⟨hz.addConst ((LQGMetric.measurable_circleAvg_left 1 0).comp hz.measurable).neg, ?_⟩
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero hz] with ω hω
  rw [hω]
  ring

 



theorem offcenter_transfer {s₀ s₁ s₂ : ℝ} (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1) (hs₀ : 0 < s₀)
    (hs₀' : s₀ < min s₁ (1 - s₂)) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (w : ℂ)
    {r : ℕ → ℝ} {z : ℕ → ℂ} {E : ℕ → Set Ω}
    (hr0 : ∀ k, 1 ≤ k → 0 < r k) (hrA : ∀ k, 1 ≤ k → r (k + 1) ≤ r k)
    (hrs : ∀ k, 1 ≤ k → r (k + 1) / r k ≤ s₁ - s₀)
    (hz : ∀ k, 1 ≤ k → dist (z k) w ≤ s₀ * r k)
    (hE : ∀ k, 1 ≤ k → ∃ E₀ : Set Ω, MeasurableSet[fieldSigmaClosed0 h
      {x | s₁ * r k ≤ dist x (z k) ∧ dist x (z k) ≤ s₂ * r k}] E₀ ∧ E k =ᵐ[P] E₀) :
    ∃ (g : Ω → DistC) (R : ℕ → ℝ) (E' : ℕ → Set Ω), IsNormalizedWPGFF g P ∧
      AnnulusIterHyp g (s₁ - s₀) ((1 + (s₂ + s₀)) / 2) R E' ∧ E' 0 = univ ∧
      ∀ k, 1 ≤ k → E k =ᵐ[P] E' k := by
  classical
  have hs₀₁ : s₀ < s₁ := hs₀'.trans_le (min_le_left _ _)
  have hs₀₂ : s₂ + s₀ < 1 := by linarith [hs₀'.trans_le (min_le_right s₁ (1 - s₂))]
  set ρ : ℝ := s₁ - s₀ with hρdef
  set μ : ℝ := (1 + (s₂ + s₀)) / 2 with hμdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; linarith
  have hμ0 : 0 < μ := by rw [hμdef]; linarith
  have hE' : ∀ k, ∃ E₀ : Set Ω, 1 ≤ k → (MeasurableSet[fieldSigmaClosed0 h
      {x | s₁ * r k ≤ dist x (z k) ∧ dist x (z k) ≤ s₂ * r k}] E₀ ∧ E k =ᵐ[P] E₀) := by
    intro k
    by_cases hk : 1 ≤ k
    · obtain ⟨E₀, h1, h2⟩ := hE k hk
      exact ⟨E₀, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨univ, fun h1 => absurd h1 hk⟩
  choose E₀ hE₀ using hE'
  set g₁ : Ω → DistC := fun ω => affineComp 1 w (h ω) with hg₁
  set g : Ω → DistC := fun ω => addConst (g₁ ω) (-circleAvg (g₁ ω) 1 0) with hg
  set R : ℕ → ℝ := fun k => if k = 0 then μ * r 1 / ρ else μ * r k with hR
  set E' : ℕ → Set Ω := fun k => if k = 0 then univ else E₀ k with hE'def
  have hr1 : 0 < r 1 := hr0 1 le_rfl
  have hRpos : ∀ k, 0 < R k := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp only [hR, hk, ↓reduceIte]; positivity
    · simp only [hR, Nat.pos_iff_ne_zero.mp hk, ↓reduceIte]
      exact mul_pos hμ0 (hr0 k hk)
  have hRsucc : ∀ k, R (k + 1) = μ * r (k + 1) := fun k => by simp [hR]
  have hR0 : R 0 = μ * r 1 / ρ := by simp [hR]
  refine ⟨g, R, E', isNormalizedWPGFF_translate hh w, ⟨hRpos, ?_, ?_, ?_⟩, by simp [hE'def], ?_⟩
  · refine antitone_nat_of_succ_le fun k => ?_
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [hRsucc, hR0, zero_add, le_div_iff₀ hρ0]
      have : 0 < μ * r 1 := mul_pos hμ0 hr1
      nlinarith
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [hRsucc, hRsucc]
      exact mul_le_mul_of_nonneg_left (hrA (j + 1) (by omega)) hμ0.le
  · intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [hRsucc, hR0, zero_add]
      have : 0 < μ * r 1 := mul_pos hμ0 hr1
      have e : μ * r 1 / (μ * r 1 / ρ) = ρ := by field_simp
      rw [e]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [hRsucc, hRsucc, mul_div_mul_left _ _ hμ0.ne']
      exact hrs (j + 1) (by omega)
  · intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [hE'def, ↓reduceIte]
      exact MeasurableSet.univ
    · have hk1 : 1 ≤ k := hk
      have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
      have hRk : R k = μ * r k := by simp only [hR, hkne, ↓reduceIte]
      have hE'k : E' k = E₀ k := by simp only [hE'def, hkne, ↓reduceIte]
      rw [hE'k, hRk]
      have hsub : {x : ℂ | s₁ * r k ≤ dist x (z k) ∧ dist x (z k) ≤ s₂ * r k} ⊆
          (annulus w (ρ * (μ * r k)) (μ * (μ * r k)) : Set ℂ) :=
        closedAnnulus_subset_annulus (hr0 k hk1) hs₀₁ hs₀₂ (hz k hk1)
      exact fieldSigmaClosed0_le_translated h w (fun ω => -circleAvg (g₁ ω) 1 0)
        (fun ω => -circleAvg (g ω) (μ * r k) 0)
        (isCompact_closedAnnulusSet (z k) (s₁ * r k) (s₂ * r k)) hsub _ (hE₀ k hk1).1
  · intro k hk
    have hkne : k ≠ 0 := by omega
    simp only [hE'def, hkne, ↓reduceIte]
    exact (hE₀ k hk).2

 

 

theorem annulusOffcenterAt_part1 :
    ∀ s₀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → 0 < s₀ → s₀ < min s₁ (1 - s₂) →
    ∀ a : ℝ, 0 < a → ∀ b : ℝ, 0 < b → b < 1 →
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P →
        ∀ (w : ℂ) (r : ℕ → ℝ) (z : ℕ → ℂ) (E : ℕ → Set Ω),
        (∀ k, 1 ≤ k → 0 < r k) → (∀ k, 1 ≤ k → r (k + 1) ≤ r k) →
        (∀ k, 1 ≤ k → r (k + 1) / r k ≤ s₁ - s₀) →
        (∀ k, 1 ≤ k → dist (z k) w ≤ s₀ * r k) →
        (∀ k, 1 ≤ k → ∃ E₀ : Set Ω, MeasurableSet[fieldSigmaClosed0 h
          {x | s₁ * r k ≤ dist x (z k) ∧ dist x (z k) ≤ s₂ * r k}] E₀ ∧ E k =ᵐ[P] E₀) →
        (∀ k, 1 ≤ k → ENNReal.ofReal p ≤ P (E k)) →
        ∀ K : ℕ, 1 ≤ K →
          P {ω | (countOcc E K ω : ℝ) < b * K} ≤ ENNReal.ofReal (c * Real.exp (-a * K)) := by
  intro s₀ s₁ s₂ hs₁ hs₁₂ hs₂ hs₀ hs₀' a ha b hb0 hb1
  have hs₀₁ : s₀ < s₁ := hs₀'.trans_le (min_le_left _ _)
  have hs₀₂ : s₂ + s₀ < 1 := by linarith [hs₀'.trans_le (min_le_right s₁ (1 - s₂))]
  obtain ⟨p, c, hp0, hp1, hc, HLM⟩ := LQGMetric.LM.lmLem3_1a (s₁ - s₀) ((1 + (s₂ + s₀)) / 2)
    (by linarith) (by linarith) (by linarith) a ha b hb0 hb1
  refine ⟨p, c, hp0, hp1, hc, ?_⟩
  intro Ω _ P _ h hh w r z E hr0 hrA hrs hz hE hpE K _
  obtain ⟨g, R, E', hg, hAI, hE'0, hEE'⟩ :=
    offcenter_transfer hs₁₂ hs₂ hs₀ hs₀' hh w hr0 hrA hrs hz hE
  have hpE' : ∀ k, ENNReal.ofReal p ≤ P (E' k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [hE'0, measure_univ]
      exact ENNReal.ofReal_le_one.2 hp1.le
    · rw [← measure_congr (hEE' k hk)]
      exact hpE k hk
  rw [measure_countOcc_lt_congr hEE' b K]
  exact HLM P g hg R E' hAI hpE' K

 
theorem annulusOffcenterAt_part2 :
    ∀ s₀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → 0 < s₀ → s₀ < min s₁ (1 - s₂) →
    ∀ p : ℝ, 0 < p → p < 1 →
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ b < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P →
        ∀ (w : ℂ) (r : ℕ → ℝ) (z : ℕ → ℂ) (E : ℕ → Set Ω),
        (∀ k, 1 ≤ k → 0 < r k) → (∀ k, 1 ≤ k → r (k + 1) ≤ r k) →
        (∀ k, 1 ≤ k → r (k + 1) / r k ≤ s₁ - s₀) →
        (∀ k, 1 ≤ k → dist (z k) w ≤ s₀ * r k) →
        (∀ k, 1 ≤ k → ∃ E₀ : Set Ω, MeasurableSet[fieldSigmaClosed0 h
          {x | s₁ * r k ≤ dist x (z k) ∧ dist x (z k) ≤ s₂ * r k}] E₀ ∧ E k =ᵐ[P] E₀) →
        (∀ k, 1 ≤ k → ENNReal.ofReal p ≤ P (E k)) →
        ∀ K : ℕ, 1 ≤ K →
          P {ω | (countOcc E K ω : ℝ) < b * K} ≤ ENNReal.ofReal (c * Real.exp (-a * K)) := by
  intro s₀ s₁ s₂ hs₁ hs₁₂ hs₂ hs₀ hs₀' p hp0 hp1
  have hs₀₁ : s₀ < s₁ := hs₀'.trans_le (min_le_left _ _)
  have hs₀₂ : s₂ + s₀ < 1 := by linarith [hs₀'.trans_le (min_le_right s₁ (1 - s₂))]
  obtain ⟨a, b, c, ha, hb0, hb1, hc, HLM⟩ := lmLem3_1b (s₁ - s₀) ((1 + (s₂ + s₀)) / 2)
    (by linarith) (by linarith) (by linarith) p hp0 hp1
  refine ⟨a, b, c, ha, hb0, hb1, hc, ?_⟩
  intro Ω _ P _ h hh w r z E hr0 hrA hrs hz hE hpE K _
  obtain ⟨g, R, E', hg, hAI, hE'0, hEE'⟩ :=
    offcenter_transfer hs₁₂ hs₂ hs₀ hs₀' hh w hr0 hrA hrs hz hE
  have hpE' : ∀ k, ENNReal.ofReal p ≤ P (E' k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [hE'0, measure_univ]
      exact ENNReal.ofReal_le_one.2 hp1.le
    · rw [← measure_congr (hEE' k hk)]
      exact hpE k hk
  rw [measure_countOcc_lt_congr hEE' b K]
  exact HLM P g hg R E' hAI hpE' K

 

 





theorem annulusOffcenter_part1 :
    ∀ s₀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → 0 < s₀ → s₀ < min s₁ (1 - s₂) →
    ∀ a : ℝ, 0 < a → ∀ b : ℝ, 0 < b → b < 1 →
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P →
        ∀ (r : ℕ → ℝ) (z : ℕ → ℂ) (E : ℕ → Set Ω),
        (∀ k, 1 ≤ k → 0 < r k) → (∀ k, 1 ≤ k → r (k + 1) ≤ r k) →
        (∀ k, 1 ≤ k → r (k + 1) / r k ≤ s₁ - s₀) →
        (∀ k, 1 ≤ k → ‖z k‖ ≤ s₀ * r k) →
        (∀ k, 1 ≤ k → ∃ E₀ : Set Ω, MeasurableSet[fieldSigmaClosed0 h
          {x | s₁ * r k ≤ dist x (z k) ∧ dist x (z k) ≤ s₂ * r k}] E₀ ∧ E k =ᵐ[P] E₀) →
        (∀ k, 1 ≤ k → ENNReal.ofReal p ≤ P (E k)) →
        ∀ K : ℕ, 1 ≤ K →
          P {ω | (countOcc E K ω : ℝ) < b * K} ≤ ENNReal.ofReal (c * Real.exp (-a * K)) := by
  intro s₀ s₁ s₂ hs₁ hs₁₂ hs₂ hs₀ hs₀' a ha b hb0 hb1
  obtain ⟨p, c, hp0, hp1, hc, H⟩ :=
    annulusOffcenterAt_part1 s₀ s₁ s₂ hs₁ hs₁₂ hs₂ hs₀ hs₀' a ha b hb0 hb1
  refine ⟨p, c, hp0, hp1, hc, ?_⟩
  intro Ω _ P _ h hh r z E hr0 hrA hrs hz hE hpE K hK
  exact H P h hh 0 r z E hr0 hrA hrs (fun k hk => by rw [dist_zero_right]; exact hz k hk)
    hE hpE K hK

 



theorem annulusOffcenter_part2 :
    ∀ s₀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → 0 < s₀ → s₀ < min s₁ (1 - s₂) →
    ∀ p : ℝ, 0 < p → p < 1 →
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ b < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P →
        ∀ (r : ℕ → ℝ) (z : ℕ → ℂ) (E : ℕ → Set Ω),
        (∀ k, 1 ≤ k → 0 < r k) → (∀ k, 1 ≤ k → r (k + 1) ≤ r k) →
        (∀ k, 1 ≤ k → r (k + 1) / r k ≤ s₁ - s₀) →
        (∀ k, 1 ≤ k → ‖z k‖ ≤ s₀ * r k) →
        (∀ k, 1 ≤ k → ∃ E₀ : Set Ω, MeasurableSet[fieldSigmaClosed0 h
          {x | s₁ * r k ≤ dist x (z k) ∧ dist x (z k) ≤ s₂ * r k}] E₀ ∧ E k =ᵐ[P] E₀) →
        (∀ k, 1 ≤ k → ENNReal.ofReal p ≤ P (E k)) →
        ∀ K : ℕ, 1 ≤ K →
          P {ω | (countOcc E K ω : ℝ) < b * K} ≤ ENNReal.ofReal (c * Real.exp (-a * K)) := by
  intro s₀ s₁ s₂ hs₁ hs₁₂ hs₂ hs₀ hs₀' p hp0 hp1
  obtain ⟨a, b, c, ha, hb0, hb1, hc, H⟩ :=
    annulusOffcenterAt_part2 s₀ s₁ s₂ hs₁ hs₁₂ hs₂ hs₀ hs₀' p hp0 hp1
  refine ⟨a, b, c, ha, hb0, hb1, hc, ?_⟩
  intro Ω _ P _ h hh r z E hr0 hrA hrs hz hE hpE K hK
  exact H P h hh 0 r z E hr0 hrA hrs (fun k hk => by rw [dist_zero_right]; exact hz k hk)
    hE hpE K hK

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra
