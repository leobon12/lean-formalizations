import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover.E1eCover




 





set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover
open LQGMetric (DistC)
open LQGMetric.Blueprint

 
def e1eEps (n : ℕ) : ℝ := (1 / 10 : ℝ) ^ n
 
def e1eRadius (n j : ℕ) : ℝ := e1eEps n * (1 / 10 : ℝ) ^ j
 
def e1eReference (n k : ℕ) : ℝ := 50 * e1eEps n * (1 / 10 : ℝ) ^ k

 
theorem e1e_reference_succ (n j : ℕ) :
    e1eReference n (j + 1) = 5 * e1eRadius n j := by
  unfold e1eReference e1eRadius
  rw [pow_succ]
  ring

 

theorem e1e_iteration_annulus_eq_collar (n j : ℕ) :
    LQGMetric.Blueprint.annulus 0
      ((1 / 10) * e1eReference n (j + 1))
      ((4 / 5) * e1eReference n (j + 1)) =
    LQGMetric.Blueprint.annulus 0
      (e1eRadius n j / 2) (4 * e1eRadius n j) := by
  rw [e1e_reference_succ]
  congr 1 <;> ring

 
theorem e1e_radius_range (n j : ℕ) (hj : j ≤ n) :
    (10 : ℝ) ^ (-(2 * (n : ℤ))) ≤ e1eRadius n j ∧
    e1eRadius n j ≤ (10 : ℝ) ^ (-(n : ℤ)) := by
  have hε : 0 ≤ e1eEps n := by unfold e1eEps; positivity
  have hlow : (1 / 10 : ℝ) ^ n ≤ (1 / 10 : ℝ) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  have hhigh : (1 / 10 : ℝ) ^ j ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hεeq : (10 : ℝ) ^ (-(n : ℤ)) = e1eEps n := by
    unfold e1eEps
    rw [zpow_neg, zpow_natCast]
    simp [one_div, inv_pow]
  have hε2eq : (10 : ℝ) ^ (-(2 * (n : ℤ))) = e1eEps n * e1eEps n := by
    rw [show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast]
    unfold e1eEps
    rw [one_div_pow, pow_mul, pow_two]
    rw [mul_pow, mul_inv_rev]
    simp only [one_div]
  constructor
  · rw [hε2eq]
    unfold e1eRadius
    exact mul_le_mul_of_nonneg_left hlow hε
  · rw [hεeq]
    unfold e1eRadius
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hhigh hε

 
def e1ePadded {Ω : Type} (good : ℕ → ℂ → ℕ → Set Ω)
    (n : ℕ) (x : ℂ) (k : ℕ) : Set Ω :=
  if k ∈ Finset.Icc 1 (n + 1) then good n x (k - 1) else univ

 

theorem e1e_padded_no_success {Ω : Type} (good : ℕ → ℂ → ℕ → Set Ω)
    (n : ℕ) (x : ℂ) :
    {ω | ∀ j ≤ n, ω ∉ good n x j} =
      {ω | ∀ k ∈ Finset.Icc 1 (n + 1), ω ∉ e1ePadded good n x k} := by
  ext ω
  constructor
  · intro h k hk
    have hj : k - 1 ≤ n := by
      have hk' := Finset.mem_Icc.mp hk
      omega
    simpa [e1ePadded, hk] using h (k - 1) hj
  · intro h j hj
    have hk : j + 1 ∈ Finset.Icc 1 (n + 1) :=
      Finset.mem_Icc.mpr (by omega)
    have he := h (j + 1) hk
    simpa [e1ePadded, hk] using he

 
theorem e1e_exp_tail (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    c * Real.exp (-(8 * Real.log 10) * (n + 1)) ≤
      c * (1 / 100000000 : ℝ) ^ n := by
  have hbase : Real.exp (-(8 * Real.log 10)) = (1 / 100000000 : ℝ) := by
    rw [show -(8 * Real.log 10) = -((8 : ℕ) * Real.log 10) by norm_num,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have hexp : Real.exp (-(8 * Real.log 10) * (n + 1)) =
      (1 / 100000000 : ℝ) ^ (n + 1) := by
    rw [show -(8 * Real.log 10) * (n + 1) =
      ((n + 1 : ℕ) : ℝ) * (-(8 * Real.log 10)) by push_cast; ring,
      Real.exp_nat_mul, hbase]
  rw [hexp]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)) hc

 

theorem e1e_site_tail_constants :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hx : ℂ → Ω → DistC) (good : ℕ → ℂ → ℕ → Set Ω),
        (∀ x, LQGMetric.IsNormalizedWPGFF (hx x) P) →
        (∀ n x k, k ∈ Finset.Icc 1 (n + 1) →
          MeasurableSet[LQGMetric.Blueprint.fieldSigma
            (fun ω => LQGMetric.addConst (hx x ω)
              (-LQGMetric.circleAvg (hx x ω) (e1eReference n k) 0))
            (LQGMetric.Blueprint.annulus 0
              ((1 / 10) * e1eReference n k)
              ((4 / 5) * e1eReference n k))]
            (good n x (k - 1))) →
        (∀ n x j, j ≤ n → ENNReal.ofReal p ≤ P (good n x j)) →
        ∀ n x,
          P {ω | ∀ j ≤ n, ω ∉ good n x j} ≤
            ENNReal.ofReal (c * (1 / 100000000 : ℝ) ^ n) := by
  obtain ⟨p, c, hp0, hp1, hc, H⟩ := e1e_no_success_constants
  refine ⟨p, c, hp0, hp1, hc, ?_⟩
  intro Ω _ P _ hx good hnorm hlocal hmarg n x
  let R : ℕ → ℝ := e1eReference n
  let E : ℕ → Set Ω := e1ePadded good n x
  have hR0 : 0 < 50 * e1eEps n := by unfold e1eEps; positivity
  have hrad := e1e_radii (50 * e1eEps n) hR0
  have hiter : AnnulusIterHyp (hx x) (1 / 10) (4 / 5) R E := by
    refine ⟨hrad.1, hrad.2.1, hrad.2.2, ?_⟩
    intro k
    by_cases hk : k ∈ Finset.Icc 1 (n + 1)
    · simpa [E, e1ePadded, hk, R] using hlocal n x k hk
    · simpa [E, e1ePadded, hk] using
        (MeasurableSet.univ : MeasurableSet[LQGMetric.Blueprint.fieldSigma
          (fun ω => LQGMetric.addConst (hx x ω)
            (-LQGMetric.circleAvg (hx x ω) (R k) 0))
          (LQGMetric.Blueprint.annulus 0 ((1 / 10) * R k) ((4 / 5) * R k))] univ)
  have hprob : ∀ k, ENNReal.ofReal p ≤ P (E k) := by
    intro k
    by_cases hk : k ∈ Finset.Icc 1 (n + 1)
    · have hj : k - 1 ≤ n := by have := Finset.mem_Icc.mp hk; omega
      simpa [E, e1ePadded, hk] using hmarg n x (k - 1) hj
    · have heq : E k = univ := by simp [E, e1ePadded, hk]
      rw [heq, measure_univ]
      exact (ENNReal.ofReal_le_ofReal hp1.le).trans (by simp)
  have htail := H P (hx x) (hnorm x) R E hiter hprob (n + 1) (by omega)
  rw [← e1e_padded_no_success good n x] at htail
  have htail' : P {ω | ∀ j ≤ n, ω ∉ good n x j} ≤
      ENNReal.ofReal (c * Real.exp (-(8 * Real.log 10) * ((n : ℝ) + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using htail
  exact htail'.trans (ENNReal.ofReal_le_ofReal (e1e_exp_tail c hc.le n))

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover
