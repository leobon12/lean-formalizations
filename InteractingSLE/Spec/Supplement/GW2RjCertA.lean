/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjSched

/-!
# A window certificate from a sub-instance (decision D33)

PROVE-GW2-ROOTX round 9, deterministic. **`winCert_of_window`**: a window certificate `WinCert R b cf j` from

* a driver `R'` (the sub-instance's version) with a generating trace beyond a level `σ > b (j+1)`, equal to `R` up to
  `b (j+1)`;
* the test's stage-1 tip: `Gm.jointShiftTip R' σ (b 1)` is interior at `b (j+1) − b 1`;
* a stage driver `w = R'(b j + ·) − R'(b j)` (below `σ`) with no bad visit of its word's avoided set and no return
  before a cap `> b (j+1) − b j`, its word being the raised stage word of `pastOf cf R b j`.

The chain is `U = shiftDrive (frozenReal R' σ) (b 1)` with trace `jointShiftTip` (`stage1_spec`); the window traces
are its tips mapped out at `b j − b 1` (`traceAt_eq_shiftTip`), which inherit avoidance and no return
(`ne_of_noBad`, `ne_zero_of_noReturn`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW2Rj

open Restart Exist Exist.StagedLaw GW2TipSystem GW2Rq GW2Wm

/-- The window driver of the stage-1 chain of `R'` is the increment of `R'` after `b j`, below `σ`. -/
theorem shiftDrive_stage1_eq {R' : ℝ≥0 → ℝ} {σ A₀ bj : ℝ≥0} (hbj : bj ≤ σ) {u : ℝ} (hu : 0 ≤ u)
    (huσ : (bj : ℝ) + u ≤ σ) :
    shiftDrive (shiftDrive (Gm.frozenReal R' σ) A₀) ((bj : ℝ) - A₀) u = R' (bj + u.toNNReal) - R' bj := by
  rw [YuanCorollary13.shiftDrive_shiftDrive]
  have e : (A₀ : ℝ) + ((bj : ℝ) - A₀) = bj := by ring
  rw [e]
  exact shiftDrive_frozenReal_eq hbj hu huσ

/-- **A window certificate from a sub-instance.** -/
theorem winCert_of_window {R R' : ℝ≥0 → ℝ} {b : ℕ → ℝ≥0} (hb : Monotone b) (cf : RecData) {j : ℕ}
    (hj : 1 ≤ j) {B : ℝ≥0∞} {η' : ℝ≥0 → ℂ} (hgen : IsGeneratingTrace R' B η') (hR'c : Continuous R')
    (hR'0 : R' 0 = 0) {σ : ℝ≥0} (hσB : (σ : ℝ≥0∞) < B) (hjσ : b (j + 1) < σ)
    (hRR : ∀ u ≤ b (j + 1), R u = R' u)
    (htip : Gm.jointShiftTip R' σ (b 1) ((b (j + 1) : ℝ) - b 1) ∈ H)
    {w : ℝ≥0 → ℝ} (hw : ∀ u : ℝ≥0, b j + u ≤ σ → w u = R' (b j + u) - R' (b j))
    {κ θa : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (W₀ : RecData → BoundaryWord) (θ : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hθa : θa ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {β : BoundaryWord} (hβ : β = GW2Rd.upW (θa * chiC κ) (GW2JDetR5.stageWord (κ := κ) W₀ θ j (pastOf cf R b j)))
    {Vc : ℝ≥0∞} (hVc : ((b (j + 1) - b j : ℝ≥0) : ℝ≥0∞) < Vc)
    (hnb : ¬ BadQ κ 0 β (fun q => LP.traceAt q w) Vc) (hnr : ¬ ReturnQ (fun q => LP.traceAt q w) Vc) :
    WinCert R b cf j := by
  obtain ⟨hUc, hU0, hηL⟩ := stage1_spec hgen hR'c.continuousOn hR'0 hσB (b 1)
  have h1j : b 1 ≤ b j := hb hj
  have hjj : b j ≤ b (j + 1) := hb (Nat.le_succ j)
  have h1j1 : b 1 ≤ b (j + 1) := hb (by omega)
  have hA₀σ : b 1 ≤ σ := h1j1.trans hjσ.le
  have hjσ' : b j ≤ σ := hjj.trans hjσ.le
  -- the window chart
  have ha : (0 : ℝ) ≤ (b j : ℝ) - b 1 := by have := NNReal.coe_le_coe.2 h1j; linarith
  obtain ⟨hψ, -⟩ := hηL.isLoewnerTrace_shift_and_extendFrom hUc hU0 ha
  have hψc : Continuous fun t : ℝ≥0 => loewnerTip (shiftDrive (shiftDrive (Gm.frozenReal R' σ) (b 1))
      ((b j : ℝ) - b 1)) t :=
    hψ.2.1.comp_continuous NNReal.continuous_coe fun t => t.2
  have hΓ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < min Vc ((σ - b j : ℝ≥0) : ℝ≥0∞) → LP.traceAt t w =
      loewnerTip (shiftDrive (shiftDrive (Gm.frozenReal R' σ) (b 1)) ((b j : ℝ) - b 1)) t := by
    intro t ht
    have htb : t ≤ σ - b j := ENNReal.coe_le_coe.1 (ht.trans_le (min_le_right _ _)).le
    refine traceAt_eq_shiftTip hUc hU0 hηL ha (T := σ - b j) (fun u hu => ?_) htb
    have h1 : b j + u ≤ σ := (le_tsub_iff_left hjσ').1 hu
    have h2 : (b j : ℝ) + u ≤ σ := by exact_mod_cast h1
    rw [hw u h1, shiftDrive_stage1_eq (A₀ := b 1) hjσ' (NNReal.coe_nonneg u) h2, Real.toNNReal_coe]
  have hTsV : min Vc ((σ - b j : ℝ≥0) : ℝ≥0∞) ≤ Vc := min_le_left _ _
  have hlt : ∀ t : ℝ, 0 ≤ t → t ≤ (b (j + 1) : ℝ) - b j →
      (t.toNNReal : ℝ≥0∞) < min Vc ((σ - b j : ℝ≥0) : ℝ≥0∞) := by
    intro t ht htT
    have htT' : t.toNNReal ≤ b (j + 1) - b j := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht, NNReal.coe_sub hjj]
      exact htT
    refine lt_min (lt_of_le_of_lt (ENNReal.coe_le_coe.2 htT') hVc) (ENNReal.coe_lt_coe.2 ?_)
    exact lt_of_le_of_lt htT' (tsub_lt_tsub_right_of_le hjj hjσ)
  refine ⟨shiftDrive (Gm.frozenReal R' σ) (b 1), Gm.jointShiftTip R' σ (b 1), hUc, hU0, hηL, ?_, htip, ?_, ?_⟩
  · -- the chain is the stage-1 driver of `R`
    intro t ht htb
    have htσ : ((b 1 : ℝ≥0) : ℝ) + t ≤ σ := htb.trans (NNReal.coe_le_coe.2 hjσ.le)
    rw [shiftDrive_frozenReal_eq hA₀σ ht htσ]
    have hle : b 1 + t.toNNReal ≤ b (j + 1) := by
      rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ ht]
      exact htb
    rw [← hRR _ hle, ← hRR _ h1j1]
    show R (b 1 + t.toNNReal) - R (b 1) = R ((↑(b 1) + t).toNNReal) - R ((↑(b 1) : ℝ).toNNReal)
    rw [Real.toNNReal_coe, Real.toNNReal_add (NNReal.coe_nonneg _) ht, Real.toNNReal_coe]
  · -- avoidance
    intro t ht htT z hzL hzR hz0
    have h := ne_of_noBad hκ hκ4 W₀ θ hθ hθa j (pastOf cf R b j) hβ hnb hTsV hΓ hψc (hlt t ht htT) hzL hzR hz0
    rwa [Real.coe_toNNReal _ ht] at h
  · -- no return
    intro t ht htT
    have h := ne_zero_of_noReturn hnr hTsV hΓ hψc (Real.toNNReal_pos.2 ht) (hlt t ht.le htT)
    rwa [Real.coe_toNNReal _ ht.le] at h

end InteractingSLE.Theorem14.GW2Rj
