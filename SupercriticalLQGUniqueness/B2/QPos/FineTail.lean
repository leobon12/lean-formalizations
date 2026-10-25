import SupercriticalLQGUniqueness.B2.QPos.CorridorScaling

 






set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

 
theorem fine_east_mrect_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ n : ℕ, 3 ≤ n → ∀ s : ℝ, 2 < s →
          P {ω | (2 : ℝ)⁻¹ ^ 3 *
                (Real.exp s * LambdaN ξ W P (n - 3) (ENNReal.ofReal p) *
                  ellN ξ W P (n - 3) (ENNReal.ofReal p)) ≤
              T20B.mrectLen ξ (fun x => phiMN W P 3 n x ω)
                3 1 eastShift 3 1} ≤
            ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) := by
  obtain ⟨p₀, hp₀, hp⟩ := dddf_prop18 (P := P) hW hξ
  refine ⟨p₀, hp₀, fun p hpos hpp => ?_⟩
  obtain ⟨C, c, hC, hc, htail⟩ := hp p hpos hpp
  refine ⟨C, c, hC, hc, fun n hn s hs => ?_⟩
  have hrect := T20B.law_mrectLen (ξ := ξ) hW hn 1 eastShift 3 1
    (S := Set.Ici ((2 : ℝ)⁻¹ ^ 3 *
      (Real.exp s * LambdaN ξ W P (n - 3) (ENNReal.ofReal p) *
        ellN ξ W P (n - 3) (ENNReal.ofReal p)))) measurableSet_Ici
  rw [show {ω | (2 : ℝ)⁻¹ ^ 3 *
      (Real.exp s * LambdaN ξ W P (n - 3) (ENNReal.ofReal p) *
        ellN ξ W P (n - 3) (ENNReal.ofReal p)) ≤
        T20B.mrectLen ξ (fun x => phiMN W P 3 n x ω) 3 1 eastShift 3 1} =
      {ω | T20B.mrectLen ξ (fun x => phiMN W P 3 n x ω) 3 1 eastShift 3 1 ∈
        Set.Ici ((2 : ℝ)⁻¹ ^ 3 *
          (Real.exp s * LambdaN ξ W P (n - 3) (ENNReal.ofReal p) *
            ellN ξ W P (n - 3) (ENNReal.ofReal p)))} by ext ω; simp]
  rw [hrect]
  simp only [mem_Ici]
  have hset : {ω | (2 : ℝ)⁻¹ ^ 3 *
      (Real.exp s * LambdaN ξ W P (n - 3) (ENNReal.ofReal p) *
        ellN ξ W P (n - 3) (ENNReal.ofReal p)) ≤
      (2 : ℝ)⁻¹ ^ 3 * lenObs ξ (phiMN W P 0 (n - 3)) (rectAB 3 1) ω} =
    {ω | Real.exp s * LambdaN ξ W P (n - 3) (ENNReal.ofReal p) *
      ellN ξ W P (n - 3) (ENNReal.ofReal p) ≤
      lenObs ξ (phiMN W P 0 (n - 3)) (rectAB 3 1) ω} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [mul_comm ((2 : ℝ)⁻¹ ^ 3)
      (Real.exp s * LambdaN ξ W P (n - 3) (ENNReal.ofReal p) *
        ellN ξ W P (n - 3) (ENNReal.ofReal p)),
      mul_comm ((2 : ℝ)⁻¹ ^ 3)
        (lenObs ξ (phiMN W P 0 (n - 3)) (rectAB 3 1) ω)]
    exact mul_le_mul_iff_left₀ (by positivity : 0 < (2 : ℝ)⁻¹ ^ 3)
  rw [hset]
  exact htail (n - 3) s hs

theorem fine_upper_annulus_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ n : ℕ, 3 ≤ n → ∀ s : ℝ, 2 < s →
          P {ω | (2 : ℝ)⁻¹ ^ 3 *
                (Real.exp s * LambdaN ξ W P (n - 3) (ENNReal.ofReal p) *
                  ellN ξ W P (n - 3) (ENNReal.ofReal p)) ≤
              (crossLenIn ξ (fun x => phiMN W P 3 n x ω)
                upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal} ≤
            ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) := by
  obtain ⟨p₀, hp₀, hp⟩ := dddf_prop18 (P := P) hW hξ
  refine ⟨p₀, hp₀, fun p hpos hpp => ?_⟩
  obtain ⟨C, c, hC, hc, htail⟩ := hp p hpos hpp
  refine ⟨C, c, hC, hc, fun n hn s hs => ?_⟩
  let r : ℝ := (2 : ℝ)⁻¹ ^ 3
  let a : ℝ := Real.exp s * LambdaN ξ W P (n - 3) (ENNReal.ofReal p) *
    ellN ξ W P (n - 3) (ENNReal.ofReal p)
  have hφ := isPhiVersion_phiMN hW hn
  have hsub : {ω | r * a ≤
      (crossLenIn ξ (fun x => phiMN W P 3 n x ω)
        upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal} ⊆
      {ω | r * a ≤ T20B.mrectLen ξ (fun x => phiMN W P 3 n x ω)
        3 1 eastShift 3 1} := by
    intro ω hω
    exact hω.trans (upperAnnulus_crossReal_le_mrectLen ξ (hφ.cont ω))
  have hrect : P {ω | r * a ≤
      T20B.mrectLen ξ (fun x => phiMN W P 3 n x ω) 3 1 eastShift 3 1} =
      P {ω | a ≤ lenObs ξ (phiMN W P 0 (n - 3)) (rectAB 3 1) ω} := by
    rw [show {ω | r * a ≤
      T20B.mrectLen ξ (fun x => phiMN W P 3 n x ω) 3 1 eastShift 3 1} =
      {ω | T20B.mrectLen ξ (fun x => phiMN W P 3 n x ω) 3 1 eastShift 3 1 ∈
        Set.Ici (r * a)} by ext ω; simp]
    rw [T20B.law_mrectLen hW hn 1 eastShift 3 1 measurableSet_Ici]
    congr 1
    ext ω
    simp only [mem_ofPred_eq, mem_Ici]
    change r * a ≤ r * lenObs ξ (phiMN W P 0 (n - 3)) (rectAB 3 1) ω ↔
      a ≤ lenObs ξ (phiMN W P 0 (n - 3)) (rectAB 3 1) ω
    rw [mul_comm r a, mul_comm r (lenObs ξ (phiMN W P 0 (n - 3)) (rectAB 3 1) ω)]
    exact mul_le_mul_iff_left₀ (by positivity : 0 < r)
  calc
    P {ω | r * a ≤
        (crossLenIn ξ (fun x => phiMN W P 3 n x ω)
          upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal}
        ≤ P {ω | r * a ≤
            T20B.mrectLen ξ (fun x => phiMN W P 3 n x ω) 3 1 eastShift 3 1} :=
          measure_mono hsub
    _ = P {ω | a ≤ lenObs ξ (phiMN W P 0 (n - 3)) (rectAB 3 1) ω} := hrect
    _ ≤ ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) :=
      htail (n - 3) s hs

end SupercriticalLQGUniqueness.B2.QPos
