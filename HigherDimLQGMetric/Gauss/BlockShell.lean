import HigherDimLQGMetric.Gauss.BlockDecay
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

theorem shellRadius_le_pow (ρ : ℕ → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ i, ρ (i+1) ≤ q * ρ i) (i k : ℕ) :
    ρ (i+k) ≤ q^k * ρ i := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        ρ (i+(k+1)) = ρ ((i+k)+1) := by simp [Nat.add_assoc]
        _ ≤ q*ρ (i+k) := hstep (i+k)
        _ ≤ q*(q^k*ρ i) := mul_le_mul_of_nonneg_left ih hq
        _ = q^(k+1)*ρ i := by rw [pow_succ]; ring

theorem shellRadius_ratio_le_pow (ρ : ℕ → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hpos : ∀ i, 0 < ρ i) (hstep : ∀ i, ρ (i+1) ≤ q * ρ i)
    {i j : ℕ} (hij : i ≤ j) :
    ρ j / ρ i ≤ q^(j-i) := by
  have h := shellRadius_le_pow ρ hq hstep i (j-i)
  rw [Nat.add_sub_of_le hij] at h
  exact (div_le_iff₀ (hpos i)).2 h

theorem annularBlock_shell_corr {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ (q : ℝ) (_hq : 0 < q) (_hq1 : q < 1)
        (k₀ : ℕ) (_hk₀ : 1 ≤ k₀) (_hqk : q^k₀ ≤ ε₀)
        (ρ : ℕ → ℝ) (_hpos : ∀ i, 0 < ρ i)
        (_hstep : ∀ i, ρ (i+1) ≤ q*ρ i)
        (n : ℕ) (Y : Fin n → Lp ℝ 2 P)
        (_hY : ∀ i : Fin n, Y i ∈ annularBlock hh a b (ρ i))
        (i j : Fin n),
          |inner ℝ (Y i) (Y j)| ≤
            blockCorrCoeff C q k₀ (Nat.dist (i : ℕ) (j : ℕ)) *
              (‖Y i‖*‖Y j‖) := by
  obtain ⟨C,ε₀,hC,hε₀,hdecay⟩ := annularBlock_logCov_decay hd hh ha hab
  refine ⟨C,ε₀,hC,hε₀,?_⟩
  intro q hq hq1 k₀ hk₀ hqk ρ hpos hstep n Y hY i j
  by_cases hnear : Nat.dist (i:ℕ) (j:ℕ) < k₀
  · simp only [blockCorrCoeff, show Nat.dist (i:ℕ) (j:ℕ) < k₀ from hnear, ite_true, one_mul]
    exact abs_real_inner_le_norm (Y i) (Y j)
  have hfar (i j : Fin n) (hij : (i:ℕ) ≤ (j:ℕ))
      (hk : k₀ ≤ Nat.dist (i:ℕ) (j:ℕ)) :
      |inner ℝ (Y i) (Y j)| ≤
        blockCorrCoeff C q k₀ (Nat.dist (i:ℕ) (j:ℕ)) *
          (‖Y i‖*‖Y j‖) := by
    have hdist : Nat.dist (i:ℕ) (j:ℕ) = (j:ℕ)-(i:ℕ) :=
      Nat.dist_eq_sub_of_le hij
    have hratio := shellRadius_ratio_le_pow ρ hq.le hpos hstep hij
    have hsep : ρ j ≤ ε₀*ρ i := by
      have hpow : q^((j:ℕ)-(i:ℕ)) ≤ q^k₀ :=
        pow_le_pow_of_le_one hq.le hq1.le (by simpa [hdist] using hk)
      calc
        ρ j ≤ q^((j:ℕ)-(i:ℕ))*ρ i :=
          (div_le_iff₀ (hpos i)).1 hratio
        _ ≤ q^k₀*ρ i := mul_le_mul_of_nonneg_right hpow (hpos i).le
        _ ≤ ε₀*ρ i := mul_le_mul_of_nonneg_right hqk (hpos i).le
    have h := hdecay (ρ i) (ρ j) (hpos j) hsep (Y i) (hY i) (Y j) (hY j)
    rw [hdist] at hk ⊢
    simp [blockCorrCoeff, not_lt.mpr hk]
    calc
      |inner ℝ (Y i) (Y j)| ≤
        C*(ρ j/ρ i)*(‖Y i‖*‖Y j‖) := h
      _ ≤ C*q^((j:ℕ)-(i:ℕ))*(‖Y i‖*‖Y j‖) := by
        gcongr
  by_cases hij : (i:ℕ) ≤ (j:ℕ)
  · exact hfar i j hij (not_lt.mp hnear)
  · have hji : (j:ℕ) ≤ (i:ℕ) := le_of_not_ge hij
    have hdist : Nat.dist (j:ℕ) (i:ℕ) = Nat.dist (i:ℕ) (j:ℕ) := Nat.dist_comm _ _
    have h := hfar j i hji (by rw [hdist]; exact not_lt.mp hnear)
    simpa only [Nat.dist_comm, real_inner_comm, mul_comm] using h
end HigherDimLQGMetric
