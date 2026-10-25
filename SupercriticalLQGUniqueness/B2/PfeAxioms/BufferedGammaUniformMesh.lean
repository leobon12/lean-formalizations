import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaSample

 








set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

def uniformTime (N : ℕ) (L : ℝ) (j : Fin (N + 2)) : ℝ :=
  L * (j : ℝ) / (N + 1 : ℝ)

theorem uniformTime_mem (N : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (j : Fin (N + 2)) : uniformTime N L j ∈ Icc 0 L := by
  have hden : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  have hjnonneg : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hjle : (j : ℝ) ≤ (N + 1 : ℝ) := by
    exact_mod_cast (show j.val ≤ N + 1 by omega)
  constructor
  · exact div_nonneg (mul_nonneg hL hjnonneg) hden.le
  · apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hjle hL]

theorem uniformTime_step (N : ℕ) (L : ℝ) (j : Fin (N + 1)) :
    uniformTime N L j.succ - uniformTime N L (Fin.castSucc j) =
      L / (N + 1 : ℝ) := by
  dsimp [uniformTime]
  push_cast
  ring

theorem uniformTime_mono (N : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (j : Fin (N + 1)) :
    uniformTime N L (Fin.castSucc j) ≤ uniformTime N L j.succ := by
  have hden : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  rw [← sub_nonneg, uniformTime_step]
  exact div_nonneg hL hden.le

theorem uniformTime_subarc_len (D : LSCMetric) {Q : ℝ → ℂ}
    {L : ℝ} (hL : 0 ≤ L)
    (hunit : HasUnitSpeedOn (D.pt ∘ Q) (Icc 0 L))
    (N : ℕ) (j : Fin (N + 1)) :
    D.len Q (uniformTime N L (Fin.castSucc j))
      (uniformTime N L j.succ) = ENNReal.ofReal (L / (N + 1 : ℝ)) := by
  have hlen := LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn
    hunit (uniformTime_mem N hL (Fin.castSucc j))
      (uniformTime_mem N hL j.succ)
  change D.len Q (uniformTime N L (Fin.castSucc j))
    (uniformTime N L j.succ) = _ at hlen
  rw [uniformTime_step] at hlen
  exact hlen

theorem uniformTime_first (N : ℕ) (L : ℝ) :
    uniformTime N L (0 : Fin (N + 2)) = 0 := by
  simp [uniformTime]

theorem uniformTime_last (N : ℕ) (L : ℝ) :
    uniformTime N L (Fin.last (N + 1)) = L := by
  have hden : (N + 1 : ℝ) ≠ 0 := by positivity
  simp [uniformTime, Fin.last, hden]

end SupercriticalLQGUniqueness.B2.PfeAxioms
