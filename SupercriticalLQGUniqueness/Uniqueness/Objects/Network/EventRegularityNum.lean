import SupercriticalLQGUniqueness.Uniqueness.Objects.Network.EventRegularityGrid
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapSequences.Gapc1Sequence




 
set_option autoImplicit false
noncomputable section
open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Network
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent

 

theorem regK_power_le (k : ℕ) (hk : 48 ≤ k) :
    4 * (4 : ℝ) ^ (regK k) ≤ (2 : ℝ) ^ ((k : ℝ) / 6) := by
  have hdiv : 1 ≤ k / 12 := by omega
  have hK : regK k + 1 = k / 12 := by
    unfold regK
    omega
  have hfloor : 2 * (k / 12) ≤ k / 6 := by omega
  have hfloorR : (2 : ℝ) * (k / 12 : ℕ) ≤ (k : ℝ) / 6 := by
    have hfloorR' : (2 : ℝ) * (k / 12 : ℕ) ≤ (k / 6 : ℕ) := by
      exact_mod_cast hfloor
    have hdivR : ((k / 6 : ℕ) : ℝ) * 6 ≤ (k : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self k 6
    linarith
  calc
    4 * (4 : ℝ) ^ (regK k) = (4 : ℝ) ^ (k / 12) := by
      rw [← hK, pow_succ]
      ring
    _ = (2 : ℝ) ^ ((2 : ℝ) * (k / 12 : ℕ)) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]
      rw [← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    _ ≤ (2 : ℝ) ^ ((k : ℝ) / 6) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloorR


 

theorem reg_radius_le_sqrt (k : ℕ) (hk : 48 ≤ k) (ε : ℝ)
    (hε : 0 < ε) (hεlam : ε ≤ lam k) (hlamε : lam k < 2*ε)
    (r : ℝ) (hr : 0 < r) :
    lam k * r / 4 + 2 * 4 ^ (regK k) * lam k * r ≤
      Real.sqrt ε * r := by
  have hLamPos : 0 < lam k := by unfold lam; positivity
  have hLamLe : lam k ≤ 1 := by
    unfold lam
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
  have hLamSmall : lam k ≤ (1:ℝ)/8 := by
    unfold lam
    have hk3 : (3 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (show 3 ≤ k by omega)
    calc
      (2 : ℝ) ^ (-(k : ℝ)) ≤ (2 : ℝ) ^ (-(3:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1/8 := by norm_num
  have hεsmall : ε ≤ (1:ℝ)/8 := hεlam.trans hLamSmall
  have hscale := TwoScale.GapSequences.scale_fact_one ε (lam k) hε hεsmall hεlam hlamε
  have hroot : ε ^ ((1:ℝ)/2) = Real.sqrt ε := (Real.sqrt_eq_rpow ε).symm
  rw [hroot] at hscale
  have hpowid : (2:ℝ) ^ ((k:ℝ)/6) * lam k =
      (lam k) ^ ((5:ℝ)/6) := by
    unfold lam
    rw [← Real.rpow_add (by norm_num)]
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hpow : 4 ^ (regK k) * lam k ≤ (lam k) ^ ((5:ℝ)/6) / 4 := by
    have h1 := regK_power_le k hk
    have h2 := mul_le_mul_of_nonneg_right h1 hLamPos.le
    rw [mul_assoc, hpowid] at h2
    linarith
  have h56 : (lam k) ^ ((5:ℝ)/6) ≤ (lam k) ^ ((3:ℝ)/4) :=
    Real.rpow_le_rpow_of_exponent_ge hLamPos hLamLe (by norm_num)
  have h1 : lam k ≤ (lam k) ^ ((3:ℝ)/4) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hLamPos hLamLe (by norm_num : (3:ℝ)/4 ≤ 1))
  have hcoeff : lam k / 4 + 2 * 4 ^ (regK k) * lam k ≤
      (lam k) ^ ((3:ℝ)/4) := by
    linarith
  have hcoeff2 := mul_le_mul_of_nonneg_right hcoeff hr.le
  nlinarith [hscale]


 


theorem event_reg_at_rounded_center {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g)
    (k : ℕ) (hk : C.k0 ≤ k) (ε : ℝ)
    (hε : 0 < ε) (hεlam : ε ≤ lam k) (hlamε : lam k < 2*ε)
    (z : ℂ)
    (hProtected : closedBall z (Real.sqrt ε*C.r) ⊆
      ann 0 C.r (4*C.r)) :
    let x := TwoScale.TwoSet.nearestGrid
      (lam k * C.r / 4) z
    (by
      classical
      exact 2 * ((Finset.Icc 1 (regK k)).filter
        (fun j => regGood C (D g) (4 ^ j * lam k * C.r) x)).card ≥
        regK k) := by
  classical
  have hk48 : 48 ≤ k := C.k0Large.trans hk
  have hRadius := reg_radius_le_sqrt k hk48 ε hε hεlam hlamε C.r C.rPos
  have hx := nearestGrid_reg_site_of_radius_bound C k ε z hProtected hRadius
  exact (event_reg h) k hk _ hx


end SupercriticalLQGUniqueness.Uniqueness.Objects.Network
