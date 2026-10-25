import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate
import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEventNumerics.Numeric



 
set_option autoImplicit false
open Real
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Splice
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent

 

theorem narrow_start_q (C : Constants) {n : ℕ}
    (hn : narrowStart C ≤ n) : (8*C.Q+12)/3 ≤ (n : ℝ) := by
  have hratio : 0 < C.lamConst / C.A_nar := div_pos C.lamPos C.narPos
  have hlog : (8*C.Q+12)/3 ≤ Real.logb 2 (C.lamConst/C.A_nar) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _) C.narrowQScale
    simpa only [Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)] using h
  have hfloor := Nat.lt_floor_add_one (Real.logb 2 (C.lamConst/C.A_nar))
  have hcast : ((narrowStart C : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  dsimp [narrowStart] at hcast
  push_cast at hcast
  linarith

 

theorem narrow_real_bound (C : Constants) {n : ℕ} (hn : narrowStart C ≤ n)
    {hs hr : ℝ}
    (hdiff : |hs - hr| ≤ (2 + zeta C) * (n : ℝ) * Real.log 2) :
    (2 : ℝ) ^ (-(((n : ℝ) - 1) * (C.ξ * (C.Q + 3)))) *
        (C.r ^ (C.ξ*C.Q) * Real.exp (C.ξ*hr)) ≤
      (2 : ℝ) ^ (-(zeta C) * (n : ℝ)) *
        (((2 : ℝ) ^ (-(n : ℝ)-1) * C.r) ^ (C.ξ*C.Q) *
          Real.exp (C.ξ*hs)) := by
  have hnum := Objects.CorrectedEventNumerics.narrow_exponent C.ξPos (narrow_start_q C hn)
  change zeta C * (n : ℝ) + ((n : ℝ)+1)*C.ξ*C.Q +
    C.ξ*(2+zeta C)*(n : ℝ) ≤ ((n : ℝ)-1)*(C.ξ*(C.Q+3)) at hnum
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hnumlog := mul_le_mul_of_nonneg_right hnum hlog
  have hdelta : hr - hs ≤ (2+zeta C)*(n:ℝ)*Real.log 2 := by
    have hh := (abs_le.mp hdiff).1
    linarith
  have hdeltaξ := mul_le_mul_of_nonneg_left hdelta C.ξPos.le
  have harg :
      Real.log 2 * (-(((n:ℝ)-1)*(C.ξ*(C.Q+3)))) + C.ξ*hr ≤
      Real.log 2 * (-(zeta C)*(n:ℝ)) +
        Real.log 2 * ((-(n:ℝ)-1)*(C.ξ*C.Q)) + C.ξ*hs := by
    nlinarith only [hnumlog, hdeltaξ]
  have hcore :
      (2:ℝ)^(-(((n:ℝ)-1)*(C.ξ*(C.Q+3)))) * Real.exp (C.ξ*hr) ≤
      (2:ℝ)^(-(zeta C)*(n:ℝ)) *
        (2:ℝ)^((-(n:ℝ)-1)*(C.ξ*C.Q)) * Real.exp (C.ξ*hs) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
      Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
      Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [harg]
  have hscale :
      (((2:ℝ)^(-(n:ℝ)-1))*C.r)^(C.ξ*C.Q) =
        (2:ℝ)^((-(n:ℝ)-1)*(C.ξ*C.Q))*C.r^(C.ξ*C.Q) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
      C.rPos.le]
    congr 1
    exact (Real.rpow_mul (by norm_num : (0:ℝ)≤2) (-(n:ℝ)-1) (C.ξ*C.Q)).symm
  rw [hscale]
  have hmul := mul_le_mul_of_nonneg_right hcore
    (Real.rpow_nonneg C.rPos.le (C.ξ*C.Q))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul

 

theorem narrow_test_lower (C : Constants) (D : LSCMetric)
    (g : LQGMetric.DistC) (hS6 : S6 C D g) {n : ℕ}
    (hn : narrowStart C ≤ n) {v : ℂ} (hv : v ∈ narrowSites C n) :
    ENNReal.ofReal
        ((2 : ℝ) ^ (-(((n : ℝ)-1)*(C.ξ*(C.Q+3))))) *
        normalizer C g C.r 0 ≤
      acr D v (narrowScale C n / 4) (narrowScale C n) := by
  obtain ⟨hacr, hdiff⟩ := hS6 n hn v hv
  have hreal := narrow_real_bound C hn hdiff
  have hcoeff : 0 ≤ (2 : ℝ) ^ (-(((n : ℝ)-1)*(C.ξ*(C.Q+3)))) :=
    Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _
  have hζcoeff : 0 ≤ (2:ℝ)^(-(zeta C)*(n:ℝ)) :=
    Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _
  calc
    ENNReal.ofReal ((2 : ℝ)^(-(((n:ℝ)-1)*(C.ξ*(C.Q+3))))) *
        normalizer C g C.r 0
      = ENNReal.ofReal
          ((2 : ℝ)^(-(((n:ℝ)-1)*(C.ξ*(C.Q+3)))) *
            (C.r^(C.ξ*C.Q) * Real.exp
              (C.ξ*LQGMetric.circleAvg g C.r 0))) := by
          rw [normalizer, ENNReal.ofReal_mul hcoeff]
    _ ≤ ENNReal.ofReal
          ((2:ℝ)^(-(zeta C)*(n:ℝ)) *
            (((2:ℝ)^(-(n:ℝ)-1)*C.r)^(C.ξ*C.Q) *
              Real.exp (C.ξ*LQGMetric.circleAvg g (narrowScale C n) v))) :=
          ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((2:ℝ)^(-(zeta C)*(n:ℝ))) *
          normalizer C g (narrowScale C n) v := by
          rw [ENNReal.ofReal_mul hζcoeff]
          rfl
    _ ≤ acr D v (narrowScale C n / 4) (narrowScale C n) := hacr


end SupercriticalLQGUniqueness.Uniqueness.Objects.Splice
