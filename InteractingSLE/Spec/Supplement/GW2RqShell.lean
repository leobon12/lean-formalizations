/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RsShell

/-!
# Slow shells with chosen block sizes and the drift-optimal shell (decision D33)

PROVE-GW2-ROOTX round 8. Round 7's `GW2Rs.canonShell` takes the LONGEST right angle block. After a piece hits the
root region on one side, that block can run into root heights and cut the left block short. This file fixes the block
sizes as parameters and then picks the valid pair with the least far block:

* `phiM κ β φ0 mR`: the right angles on a right block of size `mR`, then continued from the left marks; `MatchM`: a
  left block of size `m` read as the same angle changes, with separated angles;
* `Valid κ β φ0 (mR, mL)`: both blocks fit, the right angles up to `mR + 1` are separated (`GW2Rs.BandR`), and the
  left block matches;
* **`shellAt κ β φ0 mR mL k start`**, with **`presentsO_shellAt`** (exact presentation when the left block
  matches), **`shellAt_angles`** (the angle clause) and **`stageDriftBound_shellAt`** (`8M/3 + 4/3 · farD`);
* `farD`: the total far weight of a pair; **`optShell`**: the shell of a valid pair with the least `farD`
  (`optPair`). **`presentsO_optShell`**, **`optShell_angles`**, **`stageDriftBound_optShell_le`**: if some pair is
  valid, the optimal shell presents its word, has separated angles, and its drift is at most that of ANY valid pair.

Deterministic. The bound for a particular valid pair (the pair of the two angle regions) is in `GW2RqFar`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset
open scoped NNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Rq

open Restart GW2Sde GW2Sdf GW2Sdy GW2TipSystem GW2TipSystem.RootL6 Sec5 GW2Rs

variable (κ : ℝ) (β : BoundaryWord) (φ0 : ℝ)

/-! ### The angles and the left match for a right block of size `mR` -/

/-- **The angles of both blocks for a right block of size `mR`**: the right angles up to `mR + 1`, then continued
from the left marks (`wL i = −(χ/λ)(φ i − φ (i+1))`). -/
def phiM (mR : ℕ) : ℕ → ℝ
  | 0 => φ0
  | i + 1 => if i + 1 ≤ mR + 1 then phiR κ β φ0 (i + 1) else phiM mR i + sleLambda κ / chiC κ * wLn κ β i

/-- The left marks below `m` are the angle changes of `phiM … mR`, with separated angles up to `m`. -/
def MatchM (mR m : ℕ) : Prop :=
  (∀ i < m, wLn κ β i = -(chiC κ / sleLambda κ * (phiM κ β φ0 mR i - phiM κ β φ0 mR (i + 1)))) ∧
    ∀ i ≤ m, phiM κ β φ0 mR i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)

/-- **A valid pair of block sizes**: both blocks fit in the word, the right angles are separated, the left block
matches. -/
def Valid (p : ℕ × ℕ) : Prop :=
  p.1 ≤ flowLineNR β.fn β.jumps 0 - 1 ∧ p.2 ≤ flowLineNL β.fn β.jumps 0 ∧ BandR κ β φ0 p.1 ∧
    MatchM κ β φ0 p.1 p.2

/-- The shell's angles: `phiM` on both blocks, `0` beyond. -/
def phiS (mR mL : ℕ) (i : ℕ) : ℝ := if i ≤ max (mR + 1) mL then phiM κ β φ0 mR i else 0

/-- **The slow shell with block sizes `mR`, `mL`** in the samples' frame of scale `rootScale k`. -/
def shellAt (mR mL k : ℕ) (start : ℝ) : SlowShell where
  nL₀ := flowLineNL β.fn β.jumps 0 - mL
  nR₀ := flowLineNR β.fn β.jumps 0 - 1 - mR
  ρL₀ := fun j => wLn κ β (mL + j)
  ρR₀ := fun j => wRn κ β (1 + mR + j)
  mL := mL
  mR := mR
  φ := phiS κ β φ0 mR mL
  xL := fun i => (2 : ℝ) ^ k * xLn β i
  xR := fun j => (2 : ℝ) ^ k * xRn β j
  start := start

/-- **The far weight of a pair**: the absolute weights outside the two blocks. -/
def farD (p : ℕ × ℕ) : ℝ :=
  (∑ j ∈ range (flowLineNL β.fn β.jumps 0 - p.2), |wLn κ β (p.2 + j)|) +
    ∑ j ∈ range (flowLineNR β.fn β.jumps 0 - 1 - p.1), |wRn κ β (1 + p.1 + j)|

theorem phiM_eq_phiR {mR i : ℕ} (hi : i ≤ mR + 1) : phiM κ β φ0 mR i = phiR κ β φ0 i := by
  rcases i with _ | i
  · rfl
  · simp only [phiM, hi, ↓reduceIte]

/-- Beyond the right block, the left match is automatic. -/
theorem wLn_eq_of_lt {mR i : ℕ} (hκ : 0 < κ) (hκ4 : κ < 4) (hi : mR + 1 ≤ i) :
    wLn κ β i = -(chiC κ / sleLambda κ * (phiM κ β φ0 mR i - phiM κ β φ0 mR (i + 1))) := by
  have hχ : chiC κ ≠ 0 := (Sec4.chiC_pos hκ hκ4).ne'
  have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  have h : ¬ i + 1 ≤ mR + 1 := by omega
  have e : phiM κ β φ0 mR (i + 1) = phiM κ β φ0 mR i + sleLambda κ / chiC κ * wLn κ β i := by
    simp only [phiM, h, ↓reduceIte]
  rw [e]
  field_simp
  ring

/-! ### Presentation, angles, drift of `shellAt` -/

/-- **`shellAt` presents its word** in the samples' frame (scale `rootScale k`, no reflection) whenever the blocks
fit and the left block's weights are the angle changes. -/
theorem presentsO_shellAt (hκ : 0 < κ) (hκ4 : κ < 4) {mR mL : ℕ} (hmR : mR ≤ flowLineNR β.fn β.jumps 0 - 1)
    (hmL : mL ≤ flowLineNL β.fn β.jumps 0)
    (hmatch : ∀ i < mL, wLn κ β i = -(chiC κ / sleLambda κ * (phiM κ β φ0 mR i - phiM κ β φ0 mR (i + 1))))
    (k : ℕ) (start : ℝ) :
    PresentsO κ β (rootScale k) false (shellAt κ β φ0 mR mL k start).xL
      (angleWordL κ (shellAt κ β φ0 mR mL k start).φ (shellAt κ β φ0 mR mL k start).mL
        (shellAt κ β φ0 mR mL k start).ρL₀)
      (shellAt κ β φ0 mR mL k start).xR
      (angleWordR κ (shellAt κ β φ0 mR mL k start).φ (shellAt κ β φ0 mR mL k start).mR
        (shellAt κ β φ0 mR mL k start).ρR₀) := by
  have hχ : chiC κ ≠ 0 := (Sec4.chiC_pos hκ hκ4).ne'
  have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  have hnR := one_le_flowLineNR β
  have eL : flowLineNL β.fn β.jumps 0 = mL + (flowLineNL β.fn β.jumps 0 - mL) := by omega
  have eR : flowLineNR β.fn β.jumps 0 = mR + (flowLineNR β.fn β.jumps 0 - 1 - mR) + 1 := by omega
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
    by_cases h : (i : ℕ) < mL
    · have e : Fin.cast eL i = Fin.castAdd (flowLineNL β.fn β.jumps 0 - mL) ⟨i, h⟩ := Fin.ext rfl
      change angleWordL κ (phiS κ β φ0 mR mL) mL (fun j => wLn κ β (mL + j)) (Fin.cast eL i) = _
      rw [e, angleWordL, Fin.append_left, ← hw, hmatch i h]
      have h1 : (i : ℕ) ≤ max (mR + 1) mL := le_max_of_le_right h.le
      have h2 : (i : ℕ) + 1 ≤ max (mR + 1) mL := le_max_of_le_right h
      simp only [angleChangeWeight, phiS, h1, h2, ↓reduceIte]
    · have e : Fin.cast eL i = Fin.natAdd mL ⟨i - mL, by omega⟩ := Fin.ext (by simp; omega)
      change angleWordL κ (phiS κ β φ0 mR mL) mL (fun j => wLn κ β (mL + j)) (Fin.cast eL i) = _
      rw [e, angleWordL, Fin.append_right, ← hw]
      congr 1
      simp only
      omega
  · funext j
    have hw : wRn κ β j = flowLineRhoR κ β.fn β.jumps 0 0 j := by simp only [wRn, j.isLt, ↓reduceDIte]
    have hphi : ∀ i ≤ mR, angleChangeWeight κ (phiS κ β φ0 mR mL) i = wRn κ β i := fun i hi => by
      have h1 : i ≤ mR + 1 := by omega
      have h2 : i + 1 ≤ mR + 1 := by omega
      have h1' : i ≤ max (mR + 1) mL := le_max_of_le_left h1
      have h2' : i + 1 ≤ max (mR + 1) mL := le_max_of_le_left h2
      simp only [angleChangeWeight, phiS, h1', h2', ↓reduceIte, phiM_eq_phiR κ β φ0 h1,
        phiM_eq_phiR κ β φ0 h2, phiR]
      field_simp
      ring
    change angleWordR κ (phiS κ β φ0 mR mL) mR (fun i => wRn κ β (1 + mR + i)) (Fin.cast eR j) = _
    rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
    · have e : Fin.cast eR j = 0 := Fin.ext h0
      rw [e, angleWordR, Fin.cons_zero, hphi 0 (Nat.zero_le _), ← hw, h0]
    · have e : Fin.cast eR j = Fin.succ ⟨(j : ℕ) - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [e, angleWordR, Fin.cons_succ, ← hw]
      by_cases h : (j : ℕ) - 1 < mR
      · have e2 : (⟨(j : ℕ) - 1, by omega⟩ : Fin (mR + (flowLineNR β.fn β.jumps 0 - 1 - mR))) =
            Fin.castAdd _ ⟨(j : ℕ) - 1, h⟩ := Fin.ext rfl
        rw [e2, Fin.append_left]
        change angleChangeWeight κ (phiS κ β φ0 mR mL) ((j : ℕ) - 1 + 1) = _
        rw [hphi _ (by omega)]
        congr 1
        omega
      · have e2 : (⟨(j : ℕ) - 1, by omega⟩ : Fin (mR + (flowLineNR β.fn β.jumps 0 - 1 - mR))) =
            Fin.natAdd mR ⟨(j : ℕ) - 1 - mR, by omega⟩ := Fin.ext (by simp; omega)
        rw [e2, Fin.append_right]
        simp only
        congr 1
        omega

/-- **The angle clause of `shellAt`**: separated right angles up to `mR + 1` and separated block angles up to `mL`
give separated shell angles. -/
theorem shellAt_angles {mR mL : ℕ} (hB : BandR κ β φ0 mR)
    (hM : ∀ i ≤ mL, phiM κ β φ0 mR i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (k : ℕ) (start : ℝ) (i : ℕ) :
    (shellAt κ β φ0 mR mL k start).φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  change phiS κ β φ0 mR mL i ∈ _
  unfold phiS
  split_ifs with h
  · by_cases hR : i ≤ mR + 1
    · rw [phiM_eq_phiR κ β φ0 hR]
      exact hB i hR
    · have hL : i ≤ mL := by
        rcases le_max_iff.1 h with h' | h'
        · exact absurd h' hR
        · exact h'
      exact hM i hL
  · exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- **The drift of `shellAt`**: `8M/3 + 4/3 · farD`. -/
theorem stageDriftBound_shellAt (mR mL k : ℕ) (start : ℝ) :
    Prop59Stage.stageDriftBound κ (shellAt κ β φ0 mR mL k start).ρL₀ (shellAt κ β φ0 mR mL k start).ρR₀ =
      8 * angleWeightBound κ / 3 + 4 / 3 * farD κ β (mR, mL) := by
  unfold Prop59Stage.stageDriftBound farD
  congr 2
  change (∑ i : Fin (flowLineNL β.fn β.jumps 0 - mL), |wLn κ β (mL + i)|) +
      ∑ j : Fin (flowLineNR β.fn β.jumps 0 - 1 - mR), |wRn κ β (1 + mR + j)| = _
  rw [Fin.sum_univ_eq_sum_range (fun i => |wLn κ β (mL + i)|),
    Fin.sum_univ_eq_sum_range (fun j => |wRn κ β (1 + mR + j)|)]

/-! ### The optimal valid pair -/

/-- The candidate pairs: all pairs of block sizes that fit. -/
def pairs : Finset (ℕ × ℕ) := range (flowLineNR β.fn β.jumps 0) ×ˢ range (flowLineNL β.fn β.jumps 0 + 1)

open Classical in
/-- **The optimal pair**: a valid pair with the least far weight (`(0, 0)` if none is valid). -/
def optPair : ℕ × ℕ :=
  if h : ((pairs β).filter (Valid κ β φ0)).Nonempty then
    (Finset.exists_min_image _ (farD κ β) h).choose
  else (0, 0)

/-- **The drift-optimal slow shell.** -/
def optShell (k : ℕ) (start : ℝ) : SlowShell :=
  shellAt κ β φ0 (optPair κ β φ0).1 (optPair κ β φ0).2 k start

open Classical in
theorem mem_pairs {p : ℕ × ℕ} (h : Valid κ β φ0 p) : p ∈ (pairs β).filter (Valid κ β φ0) := by
  have hnR := one_le_flowLineNR β
  have h1 := h.1
  have h2 := h.2.1
  have h1' : p.1 < flowLineNR β.fn β.jumps 0 := by omega
  have h2' : p.2 < flowLineNL β.fn β.jumps 0 + 1 := by omega
  exact mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 h1', mem_range.2 h2'⟩, h⟩

open Classical in
theorem optPair_spec {p : ℕ × ℕ} (hp : Valid κ β φ0 p) :
    Valid κ β φ0 (optPair κ β φ0) ∧ farD κ β (optPair κ β φ0) ≤ farD κ β p := by
  have hne : ((pairs β).filter (Valid κ β φ0)).Nonempty := ⟨p, mem_pairs κ β φ0 hp⟩
  have hs := (Finset.exists_min_image _ (farD κ β) hne).choose_spec
  have e : optPair κ β φ0 = (Finset.exists_min_image _ (farD κ β) hne).choose := by
    simp only [optPair, hne, ↓reduceDIte]
  rw [e]
  exact ⟨(mem_filter.1 hs.1).2, hs.2 p (mem_pairs κ β φ0 hp)⟩

/-- **The optimal shell presents its word** once some pair is valid. -/
theorem presentsO_optShell (hκ : 0 < κ) (hκ4 : κ < 4) {p : ℕ × ℕ} (hp : Valid κ β φ0 p) (k : ℕ) (start : ℝ) :
    PresentsO κ β (rootScale k) false (optShell κ β φ0 k start).xL
      (angleWordL κ (optShell κ β φ0 k start).φ (optShell κ β φ0 k start).mL (optShell κ β φ0 k start).ρL₀)
      (optShell κ β φ0 k start).xR
      (angleWordR κ (optShell κ β φ0 k start).φ (optShell κ β φ0 k start).mR
        (optShell κ β φ0 k start).ρR₀) := by
  obtain ⟨hv, -⟩ := optPair_spec κ β φ0 hp
  exact presentsO_shellAt κ β φ0 hκ hκ4 hv.1 hv.2.1 hv.2.2.2.1 k start

/-- **The optimal shell has separated angles** once some pair is valid. -/
theorem optShell_angles {p : ℕ × ℕ} (hp : Valid κ β φ0 p) (k : ℕ) (start : ℝ) (i : ℕ) :
    (optShell κ β φ0 k start).φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  obtain ⟨hv, -⟩ := optPair_spec κ β φ0 hp
  exact shellAt_angles κ β φ0 hv.2.2.1 hv.2.2.2.2 k start i

/-- **The drift of the optimal shell is at most that of any valid pair.** -/
theorem stageDriftBound_optShell_le {p : ℕ × ℕ} (hp : Valid κ β φ0 p) (k : ℕ) (start : ℝ) :
    Prop59Stage.stageDriftBound κ (optShell κ β φ0 k start).ρL₀ (optShell κ β φ0 k start).ρR₀ ≤
      8 * angleWeightBound κ / 3 + 4 / 3 * farD κ β p := by
  obtain ⟨-, hle⟩ := optPair_spec κ β φ0 hp
  change Prop59Stage.stageDriftBound κ
      (shellAt κ β φ0 (optPair κ β φ0).1 (optPair κ β φ0).2 k start).ρL₀
      (shellAt κ β φ0 (optPair κ β φ0).1 (optPair κ β φ0).2 k start).ρR₀ ≤ _
  rw [stageDriftBound_shellAt]
  have hp' : ((optPair κ β φ0).1, (optPair κ β φ0).2) = optPair κ β φ0 := rfl
  rw [hp']
  linarith

/-- The start of the optimal shell. -/
theorem optShell_start (k : ℕ) (start : ℝ) : (optShell κ β φ0 k start).start = start := rfl

end InteractingSLE.Theorem14.GW2Rq
