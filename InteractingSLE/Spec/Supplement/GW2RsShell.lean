/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RwDrift

/-!
# The canonical slow shell of a word: angle blocks, far block, exact presentation (decision D30)

PROVE-GW2-ROOTX round 7. SDE's slow word asks a shell whose angle words `angleWordL/R κ φ m ρ₀` PRESENT the stage
word (`GW2Sdf.PresentsO`, exact). This file builds the shell from the word itself, with no other input:

* `wLn`, `wRn`, `xLn`, `xRn`: the angle-`0` flow-line word, extended by `0`;
* `phiR`: the angles read from the right weights (`wR i = (χ/λ)(φ i − φ (i+1))`); `BandR`, `mRc`: the longest right
  block with separated angles;
* `phiLR`: the right angles on that block, continued from the left weights; `MatchL`, `mLc`: the longest left block
  read as the same angle changes with separated angles; `phiC`;
* **`canonShell κ β φ0 k start`**: positions `2^k` times the flow-line positions (the samples' frame of scale
  `rootScale k`), the two blocks, and the remaining weights as the far block;
* **`presentsO_canonShell`**: the canonical shell presents its word, by construction;
* **`canonShell_angles`**: the angle clause, once the right seed reads a separated angle change (`BandR … 0`).

With `GW2Ru.ae_startsU_of_presentsO`, the canonical shell of the instance's stage word, started at `histStart`, is in
`startsU`. Its far block is bounded only when neither side has merged angle marks (handoff, round 7).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset
open scoped NNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Rs

open Restart GW2Sde GW2Sdf GW2Sdy GW2TipSystem GW2TipSystem.RootL6 Sec5

variable (κ : ℝ) (β : BoundaryWord) (φ0 : ℝ)

/-! ### The flow-line word of a boundary word, extended by zero -/

/-- The left weights of the angle-`0` flow-line word, extended by `0`. -/
def wLn (i : ℕ) : ℝ :=
  if h : i < flowLineNL β.fn β.jumps 0 then flowLineRhoL κ β.fn β.jumps 0 0 ⟨i, h⟩ else 0

/-- The right weights of the angle-`0` flow-line word, extended by `0`. -/
def wRn (i : ℕ) : ℝ :=
  if h : i < flowLineNR β.fn β.jumps 0 then flowLineRhoR κ β.fn β.jumps 0 0 ⟨i, h⟩ else 0

/-- The left positions, extended by `0`. -/
def xLn (i : ℕ) : ℝ := if h : i < flowLineNL β.fn β.jumps 0 then flowLineXL β.fn β.jumps 0 ⟨i, h⟩ else 0

/-- The right positions, extended by `0`. -/
def xRn (i : ℕ) : ℝ := if h : i < flowLineNR β.fn β.jumps 0 then flowLineXR β.fn β.jumps 0 ⟨i, h⟩ else 0

/-! ### The canonical decomposition -/

/-- **The angles read from the right weights**: `wR i = (χ/λ)(φ i − φ (i+1))`. -/
def phiR : ℕ → ℝ
  | 0 => φ0
  | i + 1 => phiR i - sleLambda κ / chiC κ * wRn κ β i

/-- The right angles up to `m + 1` are separated. -/
def BandR (m : ℕ) : Prop := ∀ i ≤ m + 1, phiR κ β φ0 i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)

open Classical in
/-- **The right angle block**: the longest prefix of right marks read as separated angle changes. -/
def mRc : ℕ := Nat.findGreatest (BandR κ β φ0) (flowLineNR β.fn β.jumps 0 - 1)

/-- **The angles of both blocks**: the right angles on the right block, then continued from the left marks
(`wL i = −(χ/λ)(φ i − φ (i+1))`), so that a short right block does not truncate the left one. -/
def phiLR : ℕ → ℝ
  | 0 => φ0
  | i + 1 => if i + 1 ≤ mRc κ β φ0 + 1 then phiR κ β φ0 (i + 1) else phiLR i + sleLambda κ / chiC κ * wLn κ β i

/-- The left marks up to `m` are the angle changes of `phiLR`, with separated angles. -/
def MatchL (m : ℕ) : Prop :=
  (∀ i < m, wLn κ β i = -(chiC κ / sleLambda κ * (phiLR κ β φ0 i - phiLR κ β φ0 (i + 1)))) ∧
    ∀ i ≤ m, phiLR κ β φ0 i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)

open Classical in
/-- **The left angle block**: the longest prefix of left marks read as these angle changes. -/
def mLc : ℕ := Nat.findGreatest (MatchL κ β φ0) (flowLineNL β.fn β.jumps 0)

/-- The shell's angles: `phiLR` on both blocks, `0` beyond. -/
def phiC (i : ℕ) : ℝ := if i ≤ max (mRc κ β φ0 + 1) (mLc κ β φ0) then phiLR κ β φ0 i else 0

/-- **The canonical slow shell of a word** in the samples' frame of scale `rootScale k`: positions `2^k` times the
flow-line positions; the two angle blocks; the remaining weights as far block. -/
def canonShell (k : ℕ) (start : ℝ) : SlowShell where
  nL₀ := flowLineNL β.fn β.jumps 0 - mLc κ β φ0
  nR₀ := flowLineNR β.fn β.jumps 0 - 1 - mRc κ β φ0
  ρL₀ := fun j => wLn κ β (mLc κ β φ0 + j)
  ρR₀ := fun j => wRn κ β (1 + mRc κ β φ0 + j)
  mL := mLc κ β φ0
  mR := mRc κ β φ0
  φ := phiC κ β φ0
  xL := fun i => (2 : ℝ) ^ k * xLn β i
  xR := fun j => (2 : ℝ) ^ k * xRn β j
  start := start

open Classical in
theorem mRc_le : mRc κ β φ0 ≤ flowLineNR β.fn β.jumps 0 - 1 := Nat.findGreatest_le _

open Classical in
theorem mLc_le : mLc κ β φ0 ≤ flowLineNL β.fn β.jumps 0 := Nat.findGreatest_le _

open Classical in
/-- The left block's angle changes hold in every case (vacuously if the block is empty). -/
theorem matchL_eq_mLc : ∀ i < mLc κ β φ0,
    wLn κ β i = -(chiC κ / sleLambda κ * (phiLR κ β φ0 i - phiLR κ β φ0 (i + 1))) := by
  intro i hi
  have hne : mLc κ β φ0 ≠ 0 := by omega
  exact (Nat.findGreatest_of_ne_zero rfl hne).1 i hi

theorem phiLR_eq_phiR {i : ℕ} (hi : i ≤ mRc κ β φ0 + 1) : phiLR κ β φ0 i = phiR κ β φ0 i := by
  rcases i with _ | i
  · rfl
  · simp only [phiLR, hi, ↓reduceIte]

theorem one_le_flowLineNR : 1 ≤ flowLineNR β.fn β.jumps 0 := by unfold flowLineNR; omega


/-! ### The canonical shell presents its word -/

theorem sqrt_rootScale_mul (k : ℕ) : Real.sqrt (rootScale k) * (2 : ℝ) ^ k = 1 := by
  have h := sqrt_rootScale_inv k
  have hne : Real.sqrt (rootScale k) ≠ 0 := by
    intro h0
    rw [h0, inv_zero] at h
    exact absurd h.symm (by positivity)
  rw [← h, mul_inv_cancel₀ hne]

/-- **The canonical shell presents its word** in the samples' frame (scale `rootScale k`, no reflection): positions and
weights are the word's flow-line positions and weights, by construction. -/
theorem presentsO_canonShell (hκ : 0 < κ) (hκ4 : κ < 4) (k : ℕ) (start : ℝ) :
    PresentsO κ β (rootScale k) false (canonShell κ β φ0 k start).xL
      (angleWordL κ (canonShell κ β φ0 k start).φ (canonShell κ β φ0 k start).mL
        (canonShell κ β φ0 k start).ρL₀)
      (canonShell κ β φ0 k start).xR
      (angleWordR κ (canonShell κ β φ0 k start).φ (canonShell κ β φ0 k start).mR
        (canonShell κ β φ0 k start).ρR₀) := by
  have hχ : chiC κ ≠ 0 := (Sec4.chiC_pos hκ hκ4).ne'
  have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  have hmR := mRc_le κ β φ0
  have hmL := mLc_le κ β φ0
  have hnR := one_le_flowLineNR β
  have hmatch := matchL_eq_mLc κ β φ0
  have eL : flowLineNL β.fn β.jumps 0 = mLc κ β φ0 + (flowLineNL β.fn β.jumps 0 - mLc κ β φ0) := by omega
  have eR : flowLineNR β.fn β.jumps 0 = mRc κ β φ0 + (flowLineNR β.fn β.jumps 0 - 1 - mRc κ β φ0) + 1 := by omega
  have hsq := sqrt_rootScale_mul k
  refine ⟨eL, eR, ?_, ?_, ?_, ?_⟩
  · funext i
    change Real.sqrt (rootScale k) * ((2 : ℝ) ^ k * xLn β i) = _
    rw [← mul_assoc, hsq, one_mul]
    simp only [xLn, i.isLt, ↓reduceDIte]
  · funext j
    change Real.sqrt (rootScale k) * ((2 : ℝ) ^ k * xRn β j) = _
    rw [← mul_assoc, hsq, one_mul]
    simp only [xRn, j.isLt, ↓reduceDIte]
  · funext i
    have hw : wLn κ β i = flowLineRhoL κ β.fn β.jumps 0 0 i := by simp only [wLn, i.isLt, ↓reduceDIte]
    by_cases h : (i : ℕ) < mLc κ β φ0
    · have e : Fin.cast eL i = Fin.castAdd (flowLineNL β.fn β.jumps 0 - mLc κ β φ0) ⟨i, h⟩ := Fin.ext rfl
      change angleWordL κ (phiC κ β φ0) (mLc κ β φ0) (fun j => wLn κ β (mLc κ β φ0 + j)) (Fin.cast eL i) = _
      rw [e, angleWordL, Fin.append_left, ← hw, hmatch i h]
      have h1 : (i : ℕ) ≤ max (mRc κ β φ0 + 1) (mLc κ β φ0) := le_max_of_le_right h.le
      have h2 : (i : ℕ) + 1 ≤ max (mRc κ β φ0 + 1) (mLc κ β φ0) := le_max_of_le_right h
      simp only [angleChangeWeight, phiC, h1, h2, ↓reduceIte]
    · have e : Fin.cast eL i = Fin.natAdd (mLc κ β φ0) ⟨i - mLc κ β φ0, by omega⟩ := Fin.ext (by simp; omega)
      change angleWordL κ (phiC κ β φ0) (mLc κ β φ0) (fun j => wLn κ β (mLc κ β φ0 + j)) (Fin.cast eL i) = _
      rw [e, angleWordL, Fin.append_right, ← hw]
      congr 1
      simp only
      omega
  · funext j
    have hw : wRn κ β j = flowLineRhoR κ β.fn β.jumps 0 0 j := by simp only [wRn, j.isLt, ↓reduceDIte]
    have hphi : ∀ i ≤ mRc κ β φ0, angleChangeWeight κ (phiC κ β φ0) i = wRn κ β i := fun i hi => by
      have h1 : i ≤ mRc κ β φ0 + 1 := by omega
      have h2 : i + 1 ≤ mRc κ β φ0 + 1 := by omega
      have h1' : i ≤ max (mRc κ β φ0 + 1) (mLc κ β φ0) := le_max_of_le_left h1
      have h2' : i + 1 ≤ max (mRc κ β φ0 + 1) (mLc κ β φ0) := le_max_of_le_left h2
      simp only [angleChangeWeight, phiC, h1', h2', ↓reduceIte, phiLR_eq_phiR κ β φ0 h1,
        phiLR_eq_phiR κ β φ0 h2, phiR]
      field_simp
      ring
    change angleWordR κ (phiC κ β φ0) (mRc κ β φ0) (fun i => wRn κ β (1 + mRc κ β φ0 + i)) (Fin.cast eR j) = _
    rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
    · have e : Fin.cast eR j = 0 := Fin.ext h0
      rw [e, angleWordR, Fin.cons_zero, hphi 0 (Nat.zero_le _), ← hw, h0]
    · have e : Fin.cast eR j = Fin.succ ⟨(j : ℕ) - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [e, angleWordR, Fin.cons_succ, ← hw]
      by_cases h : (j : ℕ) - 1 < mRc κ β φ0
      · have e2 : (⟨(j : ℕ) - 1, by omega⟩ : Fin (mRc κ β φ0 + (flowLineNR β.fn β.jumps 0 - 1 - mRc κ β φ0))) =
            Fin.castAdd _ ⟨(j : ℕ) - 1, h⟩ := Fin.ext rfl
        rw [e2, Fin.append_left]
        change angleChangeWeight κ (phiC κ β φ0) ((j : ℕ) - 1 + 1) = _
        rw [hphi _ (by omega)]
        congr 1
        omega
      · have e2 : (⟨(j : ℕ) - 1, by omega⟩ : Fin (mRc κ β φ0 + (flowLineNR β.fn β.jumps 0 - 1 - mRc κ β φ0))) =
            Fin.natAdd (mRc κ β φ0) ⟨(j : ℕ) - 1 - mRc κ β φ0, by omega⟩ := Fin.ext (by simp; omega)
        rw [e2, Fin.append_right]
        simp only
        congr 1
        omega


open Classical in
/-- **The angle clause of the canonical shell**: if the right seed reads a separated angle change from `φ0`
(`BandR … 0`), every angle of the shell is in `[−π/2, π/2]`. -/
theorem canonShell_angles (hb : BandR κ β φ0 0) (k : ℕ) (start : ℝ) (i : ℕ) :
    (canonShell κ β φ0 k start).φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hB : BandR κ β φ0 (mRc κ β φ0) := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) hb
  change phiC κ β φ0 i ∈ _
  unfold phiC
  split_ifs with h
  · by_cases hR : i ≤ mRc κ β φ0 + 1
    · rw [phiLR_eq_phiR κ β φ0 hR]
      exact hB i hR
    · have hL : i ≤ mLc κ β φ0 := by
        rcases le_max_iff.1 h with h' | h'
        · exact absurd h' hR
        · exact h'
      have hne : mLc κ β φ0 ≠ 0 := by omega
      exact (Nat.findGreatest_of_ne_zero rfl hne).2 i hL
  · exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

end InteractingSLE.Theorem14.GW2Rs
