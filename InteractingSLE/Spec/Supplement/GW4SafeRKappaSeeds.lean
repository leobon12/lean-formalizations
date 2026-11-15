/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRZetaCollar
import InteractingSLE.Spec.Sec5.Prop59NodeTreeFlow

/-! # GW4: seed membership transported backwards along a real characteristic -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Complex
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW4Fix

open MartChar.RealFlow

/-- An alive restarted real characteristic ending to the left of the
current right seed started to the left of the old right seed. -/
theorem lt_right_seed_of_restart_terminal_lt {W : ℝ → ℝ} (hW : Continuous W)
    (_hW0 : W 0 = 0) {p q x : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    {a : ℝ → ℂ} (ha : QuantumZipper.IsForwardSol (shiftDrive W p) x (q - p) a)
    (hterm : (a (q - p)).re < rightImg W 0 q - W q) :
    x < rightImg W 0 p - W p := by
  have hΔ : 0 ≤ q - p := sub_nonneg.2 hpq
  have hV : Continuous (shiftDrive W p) := (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  have hV0 : shiftDrive W p 0 = 0 := by simp only [shiftDrive, add_zero, sub_self]
  by_contra hle
  have hle' : rightImg W 0 p - W p ≤ x := not_lt.1 hle
  have hseed : 0 ≤ rightImg W 0 p - W p := sub_nonneg.2 (le_rightImg hW 0 hp)
  have hx : 0 < x := by
    rcases Restart.FCAux79.isForwardSol_real_cases hV hV0 hΔ ha with h | h
    · exact h.1
    · linarith only [hle', hseed, h.1]
  have heq := Sec5.Prop59NodeTree.rightImg_shiftDrv hW hp hΔ 0
  change rightImg (shiftDrive W p) (rightImg W 0 p - W p) (q - p) =
    rightImg W 0 (p + (q - p)) - W p at heq
  rw [add_sub_cancel] at heq
  have hmon := rightImg_mono_index hV hΔ hle'
  have hright := WangWu.rightImg_sub_eq_re_fwdMap hV hV0 hΔ hx ha
  rw [fwdMap_eq_of_isForwardSol hV ha ⟨hΔ, le_rfl⟩] at hright
  have hVq : shiftDrive W p (q - p) = W q - W p := by simp only [shiftDrive, add_sub_cancel]
  rw [hVq] at hright
  rw [heq] at hmon
  linarith only [hmon, hright, hterm]

/-- Every surviving old real characteristic ending inside the current
seed interval starts inside the old seed interval. In particular the
recent collars of Zeta have old seed membership automatically. -/
theorem mem_seed_interval_of_restart_terminal {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {p q x : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    {a : ℝ → ℂ} (ha : QuantumZipper.IsForwardSol (shiftDrive W p) x (q - p) a)
    (hterm : (a (q - p)).re ∈ Ioo
      (-rightImg (fun r => -W r) 0 q - W q) (rightImg W 0 q - W q)) :
    x ∈ Ioo (-rightImg (fun r => -W r) 0 p - W p) (rightImg W 0 p - W p) := by
  refine ⟨?_, lt_right_seed_of_restart_terminal_lt hW hW0 hp hpq ha hterm.2⟩
  have hNeg : (fun r => -shiftDrive W p r) = shiftDrive (fun r => -W r) p := by
    funext r
    dsimp only [shiftDrive]
    ring
  have haNeg := QuantumZipper.RS.isForwardSol_neg ha
  rw [hNeg, ← ofReal_neg] at haNeg
  have htNeg : ((fun r => -a r) (q - p)).re < rightImg (fun r => -W r) 0 q - (-W q) := by
    simp only [neg_re]
    linarith only [hterm.1]
  have hxNeg := lt_right_seed_of_restart_terminal_lt hW.neg
    (by simp only [Pi.neg_apply, hW0, neg_zero]) hp hpq haNeg htNeg
  change -x < rightImg (fun r => -W r) 0 p - -W p at hxNeg
  linarith only [hxNeg]

end InteractingSLE.Theorem14.GW4Fix
