import Mathlib
import MatedCRTHarmonic.Frozen.MesoscopicControlWith
import MatedCRTHarmonic.Frozen.ScaledGridControl
import MatedCRTHarmonic.CellularFacts.Basic
import MatedCRTHarmonic.MesoGrid.Scale
import MatedCRTHarmonic.MesoGrid.Grid

/-!
# the mesoscopic-control construction deterministic core

Derives the frozen mesoscopic-control interface from the frozen scaled-grid estimates,
with the scale parameters and constants made explicit.
-/

set_option autoImplicit false
-- The scale conversion combines real logarithms, ceilings, and rpow identities.
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoGrid

open MatedCRTHarmonic.CellularEmbedding

def meshEpsilon (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℝ))

lemma logb_rpow_base {b x y : ℝ} (hx : 0 < x) :
    Real.logb b (x ^ y) = y * Real.logb b x := by
  simp only [Real.logb]
  rw [Real.log_rpow hx]
  ring

lemma log_meshMass {R : ℝ} {k : ℕ} {b : ℝ} (hR : 0 < R) :
    Real.logb 2 (R * (meshEpsilon k) ^ b) = Real.logb 2 R - b * (k : ℝ) := by
  have hpow : (meshEpsilon k) ^ b = (2 : ℝ) ^ (-b * (k : ℝ)) := by
    dsimp [meshEpsilon]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hpow, Real.logb_mul hR.ne' (Real.rpow_pos_of_pos (by norm_num) _).ne']
  rw [Real.logb_rpow (by norm_num) (by norm_num)]
  ring

lemma exists_large_scale_bounds {a rho sigma lam beta chi : ℝ} {R : ℕ → ℝ}
    (_ha : 0 < a) (hrho : 0 < rho) (hrhoOne : rho < 1) (hsigma : 0 < sigma) (hlam : 0 < lam)
    (hbeta : 0 < beta) (hchi : beta < chi) (hba : beta < a)
    (hR : ∀ k, 0 < R k)
    (hlim : Tendsto (fun k : ℕ => Real.logb 2 (R k) / (k : ℝ)) atTop (𝓝 a))
    (hLamLo : 1 < lam * a)
    (hLamHi : lam * (a - beta) < 1 - sigma)
    (K : ℕ) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      K ≤ scaleIndex lam D ∧
      5 * D < rho * R (scaleIndex lam D) ∧
      D < R (scaleIndex lam D) ∧
      R (scaleIndex lam D) * (meshEpsilon (scaleIndex lam D)) ^ beta ≤ D ^ (1 - sigma) ∧
      R (scaleIndex lam D) * (meshEpsilon (scaleIndex lam D)) ^ beta +
          R (scaleIndex lam D) * (meshEpsilon (scaleIndex lam D)) ^ chi < D / 100 ∧
      3 * (R (scaleIndex lam D) * (meshEpsilon (scaleIndex lam D)) ^ chi) < 2 * D := by
  let theta : ℝ := min ((a - 1 / lam) / 2)
    (((1 - sigma) / lam - (a - beta)) / 2)
  have hInvLt : 1 / lam < a := by
    rw [div_lt_iff₀ hlam]
    nlinarith [hLamLo]
  have htheta1 : 0 < (a - 1 / lam) / 2 := by linarith
  have hBetaLt : a - beta < (1 - sigma) / lam := by
    rw [lt_div_iff₀ hlam]
    nlinarith [hLamHi]
  have htheta2 : 0 < ((1 - sigma) / lam - (a - beta)) / 2 := by linarith
  have htheta : 0 < theta := by dsimp [theta]; exact lt_min htheta1 htheta2
  have hthetaA : theta < a := by
    dsimp [theta]
    have h1 : (a - 1 / lam) / 2 < a := by nlinarith [one_div_pos.mpr hlam]
    exact (min_le_left _ _).trans_lt h1
  have hthetaBoundR : theta ≤ (a - 1 / lam) / 2 := by
    dsimp [theta]; exact min_le_left _ _
  have hthetaBoundM : theta ≤ ((1 - sigma) / lam - (a - beta)) / 2 := by
    dsimp [theta]; exact min_le_right _ _
  have hlamThetaR := mul_le_mul_of_nonneg_left hthetaBoundR hlam.le
  have hlamThetaM := mul_le_mul_of_nonneg_left hthetaBoundM hlam.le
  have hthetaRcalc : lam * ((a - 1 / lam) / 2) = (lam * a - 1) / 2 := by
    field_simp
  have hthetaMcalc : lam * (((1 - sigma) / lam - (a - beta)) / 2) =
      (1 - sigma - lam * (a - beta)) / 2 := by
    field_simp
  have hcoeffR : 1 < lam * (a - theta) := by
    rw [show lam * (a - theta) = lam * a - lam * theta by ring]
    nlinarith [hLamLo, hlamThetaR, hthetaRcalc]
  have hcoeffM : lam * (a + theta - beta) < 1 - sigma := by
    rw [show lam * (a + theta - beta) = lam * (a - beta) + lam * theta by ring]
    nlinarith [hLamHi, hlamThetaM, hthetaMcalc]
  have hcoeffMpos : 0 < a + theta - beta := by linarith
  have hgapR : 0 < lam * (a - theta) - 1 := by linarith
  have hgapM : 0 < 1 - sigma - lam * (a + theta - beta) := by linarith
  obtain ⟨Krad, hRad⟩ := eventual_radius_rpow_bounds hR hlim htheta
  let Kneed : ℕ := max K (max Krad 1)
  have hidxEv : ∀ᶠ D : ℝ in atTop, Kneed ≤ scaleIndex lam D := by
    exact (scaleIndex_tendsto_atTop lam hlam).eventually (eventually_ge_atTop Kneed)
  obtain ⟨Didx, hIdx⟩ := Filter.eventually_atTop.mp hidxEv
  have hId : Tendsto (fun D : ℝ => D) atTop atTop :=
    Filter.tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨b, fun D hD => hD⟩
  have hlog : Tendsto (fun D : ℝ => Real.logb 2 D) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hId
  let LR : ℝ := (Real.logb 2 5 - Real.logb 2 rho) / (lam * (a - theta) - 1) + 1
  let LM : ℝ := (a + theta - beta) / (1 - sigma - lam * (a + theta - beta)) + 1
  let LP : ℝ := Real.logb 2 200 / sigma + 1
  let L₀ : ℝ := max 1 (max LR (max LM LP))
  have hL0Ev : ∀ᶠ D : ℝ in atTop, L₀ ≤ Real.logb 2 D :=
    hlog.eventually (eventually_ge_atTop L₀)
  obtain ⟨Dlog, hDlog⟩ := Filter.eventually_atTop.mp hL0Ev
  refine ⟨max 1 (max Didx Dlog), ?_⟩
  intro D hD
  have hD1 : 1 ≤ D := le_trans (le_max_left 1 _) hD
  have hDidx : Didx ≤ D := le_trans (le_max_left Didx Dlog)
    (le_trans (le_max_right 1 _) hD)
  have hDlog' : Dlog ≤ D := le_trans (le_max_right Didx Dlog)
    (le_trans (le_max_right 1 _) hD)
  have hkKneed : Kneed ≤ scaleIndex lam D := hIdx D hDidx
  have hkK : K ≤ scaleIndex lam D := le_trans (Nat.le_max_left K (max Krad 1)) hkKneed
  have hkRad : Krad ≤ scaleIndex lam D := le_trans
    (le_trans (Nat.le_max_left Krad 1) (Nat.le_max_right K (max Krad 1))) hkKneed
  have hkOne : 1 ≤ scaleIndex lam D := le_trans
    (le_trans (Nat.le_max_right Krad 1) (Nat.le_max_right K (max Krad 1))) hkKneed
  have hL : L₀ ≤ Real.logb 2 D := hDlog D hDlog'
  have hLR : LR ≤ Real.logb 2 D := le_trans (le_max_of_le_right (le_max_left _ _)) hL
  have hLM : LM ≤ Real.logb 2 D := le_trans (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))) hL
  have hLP : LP ≤ Real.logb 2 D := le_trans (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))) hL
  let k : ℕ := scaleIndex lam D
  have hkpos : 0 < (k : ℝ) := by
    have : 1 ≤ k := hkOne
    exact_mod_cast (Nat.zero_lt_of_lt this)
  have hkLower : lam * Real.logb 2 D ≤ (k : ℝ) := Nat.le_ceil _
  have hkUpper : (k : ℝ) < lam * Real.logb 2 D + 1 := scaleIndex_lt_add_one hlam hD1
  have hRad' := hRad k hkRad
  have hlogRlo : (a - theta) * (k : ℝ) < Real.logb 2 (R k) := by
    have h := (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2)
      (Real.rpow_pos_of_pos (by norm_num) _) (hR k)).2 hRad'.1
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at h
    exact h
  have hlogRhi : Real.logb 2 (R k) < (a + theta) * (k : ℝ) := by
    have h := (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2)
      (hR k) (Real.rpow_pos_of_pos (by norm_num) _)).2 hRad'.2
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at h
    exact h
  have hlogRprod : Real.logb 2 (5 * D) < Real.logb 2 (rho * R k) := by
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (hR k).ne']
    have hthr : Real.logb 2 5 - Real.logb 2 rho <
      (lam * (a - theta) - 1) * Real.logb 2 D := by
      have hdiv : (Real.logb 2 5 - Real.logb 2 rho) / (lam * (a - theta) - 1) < Real.logb 2 D := by
        have := hLR
        dsimp [LR] at this
        linarith
      have hmul := (div_lt_iff₀ hgapR).mp hdiv
      simpa [mul_comm] using hmul
    have hscale := mul_le_mul_of_nonneg_left hkLower (sub_nonneg.mpr hthetaA.le)
    nlinarith [hlogRlo, hgapR]
  have hDpos : 0 < D := by linarith [hD1]
  have h5Dpos : 0 < 5 * D := by positivity
  have hrhoRpos : 0 < rho * R k := mul_pos hrho (hR k)
  have hRbig : 5 * D < rho * R k :=
    (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2) h5Dpos hrhoRpos).mp hlogRprod
  have hDltR : D < R k := by
    have hrhoR : rho * R k < R k := by nlinarith [hrho, hrhoOne, hR k]
    linarith
  have hlogMass : Real.logb 2 (R k * (meshEpsilon k) ^ beta) < (a + theta - beta) * (k : ℝ) := by
    rw [log_meshMass (hR k)]
    linarith [hlogRhi]
  have hlogMassD : Real.logb 2 (R k * (meshEpsilon k) ^ beta) < (1 - sigma) * Real.logb 2 D := by
    have hthr : a + theta - beta <
      (1 - sigma - lam * (a + theta - beta)) * Real.logb 2 D := by
      have hdiv : (a + theta - beta) / (1 - sigma - lam * (a + theta - beta)) < Real.logb 2 D := by
        have := hLM
        dsimp [LM] at this
        linarith
      have hmul := (div_lt_iff₀ hgapM).mp hdiv
      simpa [mul_comm] using hmul
    have hprod : (a + theta - beta) * (k : ℝ) < (a + theta - beta) * (lam * Real.logb 2 D + 1) := by
      nlinarith [hcoeffMpos, hkUpper]
    nlinarith [hlogMass]
  have hepsPos : 0 < meshEpsilon k := by
    dsimp [meshEpsilon]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hmassPos : 0 < R k * (meshEpsilon k) ^ beta :=
    mul_pos (hR k) (Real.rpow_pos_of_pos hepsPos beta)
  have hDpowPos : 0 < D ^ (1 - sigma) := Real.rpow_pos_of_pos hDpos _
  have hmassLe : R k * (meshEpsilon k) ^ beta ≤ D ^ (1 - sigma) := by
    have hlogPow : Real.logb 2 (D ^ (1 - sigma)) = (1 - sigma) * Real.logb 2 D := by
      rw [logb_rpow_base (b := 2) (x := D) (y := 1 - sigma) hDpos]
    have hlogMassPow : Real.logb 2 (R k * (meshEpsilon k) ^ beta) < Real.logb 2 (D ^ (1 - sigma)) := by
      rw [hlogPow]
      exact hlogMassD
    exact ((Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2) hmassPos hDpowPos).mp hlogMassPow).le
  have hsmallPow : 200 * D ^ (1 - sigma) < D := by
    have hthr : Real.logb 2 200 < sigma * Real.logb 2 D := by
      have hLP' := hLP
      have hquot : Real.logb 2 200 / sigma < Real.logb 2 D := by
        dsimp [LP] at hLP'
        linarith
      have hmul := (div_lt_iff₀ hsigma).mp hquot
      simpa [mul_comm] using hmul
    have hlog : Real.logb 2 (200 * D ^ (1 - sigma)) < Real.logb 2 D := by
      rw [Real.logb_mul (by norm_num) (by positivity), logb_rpow_base (b := 2) (x := D) (y := 1 - sigma) hDpos]
      linarith [hthr]
    have hpos : 0 < 200 * D ^ (1 - sigma) := mul_pos (by norm_num) hDpowPos
    exact (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2) hpos (by linarith)).mp hlog
  have hepsLe : meshEpsilon k ≤ 1 := by
    dsimp [meshEpsilon]
    rw [← Real.rpow_zero (2 : ℝ)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    exact neg_nonpos.mpr (Nat.cast_nonneg k)
  have hchiLe : (meshEpsilon k) ^ chi ≤ (meshEpsilon k) ^ beta :=
    Real.rpow_le_rpow_of_exponent_ge hepsPos hepsLe hchi.le
  have hsum : R k * (meshEpsilon k) ^ beta + R k * (meshEpsilon k) ^ chi < D / 100 := by
    have hchiMass := mul_le_mul_of_nonneg_left hchiLe (hR k).le
    linarith [hchiMass, hmassLe, hsmallPow]
  have h3s : 3 * (R k * (meshEpsilon k) ^ chi) < 2 * D := by
    have : R k * (meshEpsilon k) ^ chi < D / 100 := by nlinarith [hsum]
    nlinarith
  exact ⟨hkK, hRbig, hDltR, hmassLe, hsum, h3s⟩

lemma gridBallFinset_mem_indices {s r : ℝ} {z : ℂ}
    (hz : z ∈ gridBallFinset s r) :
    ∃ m n : ℤ, m ∈ Finset.Icc (-gridBound r s) (gridBound r s) ∧
      n ∈ Finset.Icc (-gridBound r s) (gridBound r s) ∧ gridPoint s m n = z ∧
      z ∈ ball (0 : ℂ) r := by
  classical
  simp only [gridBallFinset, Finset.mem_filter, Finset.mem_image] at hz
  obtain ⟨⟨m,n⟩, hmn, rfl⟩ := hz.1
  exact ⟨m, n, (Finset.mem_product.mp hmn).1, (Finset.mem_product.mp hmn).2, rfl, hz.2⟩

lemma gridIntervalFinset_mem_index {s l u r : ℝ}
    (hr : r ∈ gridIntervalFinset s l u) :
    ∃ k : ℤ, k ∈ Finset.Icc (Int.floor (l / s)) (Int.ceil (u / s)) ∧
      s * (k : ℝ) = r ∧ r ∈ Set.Icc l u := by
  classical
  simp only [gridIntervalFinset, Finset.mem_filter, Finset.mem_image] at hr
  obtain ⟨k, hk, heq⟩ := hr.1
  exact ⟨k, hk, heq, hr.2⟩

end MatedCRTHarmonic.MesoGrid
