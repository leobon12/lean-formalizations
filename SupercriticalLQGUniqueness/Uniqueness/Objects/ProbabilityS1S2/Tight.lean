import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2.Bridges
import SLUFieldSupport
import NV1Evidence




 






set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2

open LQGMetric (DistC circleAvg)

theorem normalizer_mul (ξ Q : ℝ) (r : Ioi (0 : ℝ)) (c : ℝ) :
    ENNReal.ofReal ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)) *
      ENNReal.ofReal ((r : ℝ) ^ (-(ξ * Q)) * Real.exp (-(ξ * c))) = 1 := by
  have hr : (0 : ℝ) < r := r.2
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
  congr 1
  rw [Real.rpow_neg hr.le, Real.exp_neg]
  have h1 : (r : ℝ) ^ (ξ * Q) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have h2 : Real.exp (ξ * c) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

theorem lower_from_normed {n N X M : ℝ≥0∞} (hnN : N * n = 1)
    (h : M ≤ n * X) : M * N ≤ X := by
  calc
    M * N ≤ n * X * N := mul_le_mul' h le_rfl
    _ = X * (N * n) := by ring
    _ = X := by rw [hnN, mul_one]

theorem upper_from_normed {n N X M : ℝ≥0∞} (hnN : N * n = 1)
    (h : n * X ≤ M) : X ≤ M * N := by
  calc
    X = N * n * X := by rw [hnN, one_mul]
    _ = N * (n * X) := mul_assoc _ _ _
    _ ≤ N * M := mul_le_mul' le_rfl h
    _ = M * N := mul_comm _ _

 
theorem s1_of_normalized_tests (C : Objects.CorrectedEvent.Constants) (D : LSCMetric) (g : DistC)
    (M₁ M₂ : ℝ) (hA₁ : C.A_across ≤ M₁⁻¹) (hA₂ : C.A_across ≤ M₂⁻¹)
    (h₁ : ENNReal.ofReal M₁⁻¹ ≤
      ENNReal.ofReal (C.r ^ (-(C.ξ*C.Q)) *
        Real.exp (-(C.ξ*circleAvg g C.r 0))) *
        acrossDist D ((crossingShape 1 (3/2) (by norm_num) (by norm_num)).dilate C.r C.rPos))
    (h₂ : ENNReal.ofReal M₂⁻¹ ≤
      ENNReal.ofReal (C.r ^ (-(C.ξ*C.Q)) *
        Real.exp (-(C.ξ*circleAvg g C.r 0))) *
        acrossDist D ((crossingShape (5/2) 3 (by norm_num) (by norm_num)).dilate C.r C.rPos)) :
    Objects.CorrectedEvent.S1 C D g := by
  let n : ℝ≥0∞ := ENNReal.ofReal (C.r ^ (-(C.ξ*C.Q)) *
    Real.exp (-(C.ξ*circleAvg g C.r 0)))
  have hn : Objects.CorrectedEvent.normalizer C g C.r 0 * n = 1 := by
    change ENNReal.ofReal (C.r ^ (C.ξ*C.Q) * Real.exp (C.ξ*circleAvg g C.r 0)) * n = 1
    exact normalizer_mul C.ξ C.Q ⟨C.r, C.rPos⟩ (circleAvg g C.r 0)
  have hA₁' : ENNReal.ofReal C.A_across ≤ ENNReal.ofReal M₁⁻¹ :=
    ENNReal.ofReal_le_ofReal hA₁
  have hA₂' : ENNReal.ofReal C.A_across ≤ ENNReal.ofReal M₂⁻¹ :=
    ENNReal.ofReal_le_ofReal hA₂
  constructor
  · calc
      ENNReal.ofReal C.A_across * Objects.CorrectedEvent.normalizer C g C.r 0 ≤
          ENNReal.ofReal M₁⁻¹ * Objects.CorrectedEvent.normalizer C g C.r 0 := by gcongr
      _ ≤ acrossDist D ((crossingShape 1 (3/2) (by norm_num) (by norm_num)).dilate C.r C.rPos) :=
        lower_from_normed hn h₁
      _ = Objects.CorrectedEvent.ambientAcross D 0 C.r (1.5*C.r) := by
        simpa only [one_mul, show (3/2:ℝ) = 1.5 by norm_num] using
          acrossDist_shape_eq D 1 (3/2) C.r (by norm_num) (by norm_num) C.rPos
      _ ≤ Objects.CorrectedEvent.acr D 0 C.r (1.5*C.r) := ambientAcross_le_acr D 0 _ _
  · calc
      ENNReal.ofReal C.A_across * Objects.CorrectedEvent.normalizer C g C.r 0 ≤
          ENNReal.ofReal M₂⁻¹ * Objects.CorrectedEvent.normalizer C g C.r 0 := by gcongr
      _ ≤ acrossDist D ((crossingShape (5/2) 3 (by norm_num) (by norm_num)).dilate C.r C.rPos) :=
        lower_from_normed hn h₂
      _ = Objects.CorrectedEvent.ambientAcross D 0 (2.5*C.r) (3*C.r) := by
        simpa only [show (5/2:ℝ) = 2.5 by norm_num] using
          acrossDist_shape_eq D (5/2) 3 C.r (by norm_num) (by norm_num) C.rPos
      _ ≤ Objects.CorrectedEvent.acr D 0 (2.5*C.r) (3*C.r) := ambientAcross_le_acr D 0 _ _

 
theorem s2_of_normalized_test (C : Objects.CorrectedEvent.Constants) (D : LSCMetric) (g : DistC)
    (M : ℝ) (hA : M ≤ C.A_around)
    (h : ENNReal.ofReal (C.r ^ (-(C.ξ*C.Q)) *
      Real.exp (-(C.ξ*circleAvg g C.r 0))) *
      aroundDist D ((crossingShape 3 4 (by norm_num) (by norm_num)).dilate C.r C.rPos) ≤
        ENNReal.ofReal M) : Objects.CorrectedEvent.S2 C D g := by
  let n : ℝ≥0∞ := ENNReal.ofReal (C.r ^ (-(C.ξ*C.Q)) *
    Real.exp (-(C.ξ*circleAvg g C.r 0)))
  have hn : Objects.CorrectedEvent.normalizer C g C.r 0 * n = 1 := by
    change ENNReal.ofReal (C.r ^ (C.ξ*C.Q) * Real.exp (C.ξ*circleAvg g C.r 0)) * n = 1
    exact normalizer_mul C.ξ C.Q ⟨C.r, C.rPos⟩ (circleAvg g C.r 0)
  change Objects.CorrectedEvent.around D 0 (3*C.r) (4*C.r) ≤
    ENNReal.ofReal C.A_around * Objects.CorrectedEvent.normalizer C g C.r 0
  calc
    Objects.CorrectedEvent.around D 0 (3*C.r) (4*C.r) ≤
        aroundDist D ((crossingShape 3 4 (by norm_num) (by norm_num)).dilate C.r C.rPos) :=
      aroundDist_shape_ge D 3 4 C.r (by norm_num) (by norm_num) C.rPos
    _ ≤ ENNReal.ofReal M * Objects.CorrectedEvent.normalizer C g C.r 0 := upper_from_normed hn h
    _ ≤ ENNReal.ofReal C.A_around * Objects.CorrectedEvent.normalizer C g C.r 0 := by gcongr

 

theorem exists_s1_budget (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (pbar : Ioo (0 : ℝ) 1) :
    ∃ A : ℝ, 0 < A ∧ A < 1 ∧
      ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ξ → C.Q = Q → C.A_across ≤ A →
        μ {g | ¬ Objects.CorrectedEvent.S1 C (D g) g} ≤
          ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  let ε : ℝ := (1 - (pbar : ℝ)) / 20
  have hε : 0 < ε := by dsimp [ε]; linarith [pbar.2.2]
  let A₁ := crossingShape 1 (3/2) (by norm_num) (by norm_num)
  let A₂ := crossingShape (5/2) 3 (by norm_num) (by norm_num)
  let X₁ : Ioi (0 : ℝ) → DistC → ℝ≥0∞ := fun r g =>
    ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ)*Q)) *
      Real.exp (-((ξ : ℝ)*circleAvg g r 0))) * acrossDist (D g) (A₁.dilate r r.2)
  let X₂ : Ioi (0 : ℝ) → DistC → ℝ≥0∞ := fun r g =>
    ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ)*Q)) *
      Real.exp (-((ξ : ℝ)*circleAvg g r 0))) * acrossDist (D g) (A₂.dilate r r.2)
  have hV₁ : IsTwoSidedTight μ X₁ :=
    (hD.tightness μ id hμ (fun r g => circleAvg g r 0)
      (fun r => ae_isCircleAverage_old hμ.1 r 0) A₁).1
  have hV₂ : IsTwoSidedTight μ X₂ :=
    (hD.tightness μ id hμ (fun r g => circleAvg g r 0)
      (fun r => ae_isCircleAverage_old hμ.1 r 0) A₂).1
  obtain ⟨M₁, hM₁, ht₁⟩ := hV₁.2 ε hε
  obtain ⟨M₂, hM₂, ht₂⟩ := hV₂.2 ε hε
  let A : ℝ := min (1/2) (min M₁⁻¹ M₂⁻¹)
  have hApos : 0 < A := by
    dsimp [A]
    exact lt_min (by norm_num) (lt_min (inv_pos.mpr hM₁) (inv_pos.mpr hM₂))
  have hAlt : A < 1 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨A, hApos, hAlt, ?_⟩
  intro C hξ hQ hCA
  let r : Ioi (0 : ℝ) := ⟨C.r, C.rPos⟩
  let B₁ : Set DistC := {g | X₁ r g < ENNReal.ofReal M₁⁻¹}
  let B₂ : Set DistC := {g | X₂ r g < ENNReal.ofReal M₂⁻¹}
  have hsub : {g | ¬ Objects.CorrectedEvent.S1 C (D g) g} ⊆ B₁ ∪ B₂ := by
    intro g hg
    by_cases hb₁ : g ∈ B₁
    · exact Or.inl hb₁
    by_cases hb₂ : g ∈ B₂
    · exact Or.inr hb₂
    exfalso
    have h₁ : ENNReal.ofReal M₁⁻¹ ≤ X₁ r g := le_of_not_gt hb₁
    have h₂ : ENNReal.ofReal M₂⁻¹ ≤ X₂ r g := le_of_not_gt hb₂
    have hC₁ : C.A_across ≤ M₁⁻¹ := hCA.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hC₂ : C.A_across ≤ M₂⁻¹ := hCA.trans ((min_le_right _ _).trans (min_le_right _ _))
    apply hg
    apply s1_of_normalized_tests C (D g) g M₁ M₂ hC₁ hC₂
    · simpa only [X₁, A₁, r, hξ, hQ] using h₁
    · simpa only [X₂, A₂, r, hξ, hQ] using h₂
  calc
    μ {g | ¬ Objects.CorrectedEvent.S1 C (D g) g} ≤ μ (B₁ ∪ B₂) := measure_mono hsub
    _ ≤ μ B₁ + μ B₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε :=
      add_le_add (ht₁ r).2 (ht₂ r).2
    _ = ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
      rw [← ENNReal.ofReal_add hε.le hε.le]
      congr 1
      dsimp [ε]
      ring

 

theorem exists_s2_budget (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (pbar : Ioo (0 : ℝ) 1) :
    ∃ A : ℝ, 1 < A ∧
      ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ξ → C.Q = Q → A ≤ C.A_around →
        μ {g | ¬ Objects.CorrectedEvent.S2 C (D g) g} ≤
          ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  let ε : ℝ := (1 - (pbar : ℝ)) / 10
  have hε : 0 < ε := by dsimp [ε]; linarith [pbar.2.2]
  let A₀ := crossingShape 3 4 (by norm_num) (by norm_num)
  let X : Ioi (0 : ℝ) → DistC → ℝ≥0∞ := fun r g =>
    ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ)*Q)) *
      Real.exp (-((ξ : ℝ)*circleAvg g r 0))) * aroundDist (D g) (A₀.dilate r r.2)
  have hV : IsTwoSidedTight μ X :=
    (hD.tightness μ id hμ (fun r g => circleAvg g r 0)
      (fun r => ae_isCircleAverage_old hμ.1 r 0) A₀).2
  obtain ⟨M, hM, ht⟩ := hV.2 ε hε
  let A : ℝ := max 2 M
  have hA : 1 < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro C hξ hQ hCA
  let r : Ioi (0 : ℝ) := ⟨C.r, C.rPos⟩
  let B : Set DistC := {g | ENNReal.ofReal M < X r g}
  have hsub : {g | ¬ Objects.CorrectedEvent.S2 C (D g) g} ⊆ B := by
    intro g hg
    by_contra hbad
    have hX : X r g ≤ ENNReal.ofReal M := le_of_not_gt hbad
    have hMCA : M ≤ C.A_around := (le_max_right _ _).trans hCA
    apply hg
    apply s2_of_normalized_test C (D g) g M hMCA
    simpa only [X, A₀, r, hξ, hQ] using hX
  exact (measure_mono hsub).trans (ht r).1

 

theorem exists_s1_s2_joint_budget (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (pbar : Ioo (0 : ℝ) 1) :
    ∃ a A : ℝ, 0 < a ∧ a < 1 ∧ 1 < A ∧ a⁻¹ < A ∧
      ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ξ → C.Q = Q →
        C.A_across ≤ a → A ≤ C.A_around →
          μ {g | ¬ Objects.CorrectedEvent.S1 C (D g) g} ≤
              ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) ∧
          μ {g | ¬ Objects.CorrectedEvent.S2 C (D g) g} ≤
              ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  obtain ⟨a, ha0, ha1, hS1⟩ := exists_s1_budget μ hμ ξ Q D hD pbar
  obtain ⟨A₀, hA₀, hS2⟩ := exists_s2_budget μ hμ ξ Q D hD pbar
  let A := max A₀ (a⁻¹ + 1)
  have hA1 : 1 < A := hA₀.trans_le (le_max_left _ _)
  have hAinv : a⁻¹ < A := by
    calc
      a⁻¹ < a⁻¹ + 1 := by linarith
      _ ≤ A := le_max_right _ _
  refine ⟨a, A, ha0, ha1, hA1, hAinv, ?_⟩
  intro C hξ hQ hCa hCA
  exact ⟨hS1 C hξ hQ hCa,
    hS2 C hξ hQ ((le_max_left _ _).trans hCA)⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2
