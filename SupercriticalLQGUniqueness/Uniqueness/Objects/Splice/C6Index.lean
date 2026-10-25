import SupercriticalLQGUniqueness.Uniqueness.Objects.Splice.C6Numeric



 
set_option autoImplicit false
noncomputable section
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Splice
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent

 

theorem exists_narrow_index (C : Constants) {d : ℝ} (hd : 0 < d)
    (hwindow : d ≤ C.A_nar/C.lamConst*C.r) :
    ∃ n : ℕ, narrowStart C ≤ n ∧
      (2:ℝ)^(-(n:ℝ))*C.r < d ∧
      d ≤ (2:ℝ)^(-(n:ℝ)+1)*C.r := by
  have hqex : 0 ≤ (8*C.Q+12)/3 := by linarith [C.QPos]
  have hratio1 : 1 ≤ C.lamConst/C.A_nar :=
    (Real.one_le_rpow (by norm_num : (1:ℝ)≤2) hqex).trans C.narrowQScale
  have hratiod : C.lamConst/C.A_nar ≤ C.r/d := by
    apply (div_le_div_iff₀ C.narPos hd).2
    have h := mul_le_mul_of_nonneg_left hwindow C.lamPos.le
    have heq : C.lamConst*(C.A_nar/C.lamConst*C.r) = C.r*C.A_nar := by
      field_simp [C.lamPos.ne']
    linarith
  have hrd1 : 1 ≤ C.r/d := hratio1.trans hratiod
  obtain ⟨m, hmlo, hmhi⟩ := exists_nat_pow_near hrd1 (by norm_num : (1:ℝ)<2)
  have hlog : Real.logb 2 (C.lamConst/C.A_nar) < (m:ℝ)+1 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2)
      (div_pos C.lamPos C.narPos)]
    rw [Real.rpow_add_one (by norm_num : (2:ℝ)≠0), Real.rpow_natCast]
    simpa only [pow_succ] using lt_of_le_of_lt hratiod hmhi
  have hfloor : Nat.floor (Real.logb 2 (C.lamConst/C.A_nar)) ≤ m := by
    have hlt : Nat.floor (Real.logb 2 (C.lamConst/C.A_nar)) < m+1 :=
      (Nat.floor_lt' (Nat.succ_ne_zero m)).2 (by exact_mod_cast hlog)
    omega
  have hmpos : 0 < (2:ℝ)^m := pow_pos (by norm_num : (0:ℝ)<2) _
  have hmspos : 0 < (2:ℝ)^(m+1) := pow_pos (by norm_num : (0:ℝ)<2) _
  have hlo : (2:ℝ)^(-((m+1:ℕ):ℝ))*C.r < d := by
    have hdiv : C.r < d*(2:ℝ)^(m+1) := by
      simpa only [mul_comm] using (div_lt_iff₀ hd).mp hmhi
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2), Real.rpow_natCast]
    rw [inv_mul_eq_div]
    apply (div_lt_iff₀ hmspos).2
    exact hdiv
  have hhi : d ≤ (2:ℝ)^(-(m:ℝ))*C.r := by
    have hmul : d*(2:ℝ)^m ≤ C.r := by
      simpa only [mul_comm] using (le_div_iff₀ hd).mp hmlo
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2), Real.rpow_natCast]
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hmpos).2
    exact hmul
  refine ⟨m+1, ?_, ?_, ?_⟩
  · dsimp [narrowStart]
    omega
  · simpa only [Nat.cast_add, Nat.cast_one] using hlo
  · convert hhi using 1
    push_cast
    ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.Splice
