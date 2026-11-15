/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveWord
import InteractingSLE.Spec.Supplement.LP3Flow
import InteractingSLE.Spec.Supplement.Q3ChainWord
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal

/-!
# The marks of the real Loewner flow along a shifted driver

Packet PROVE-SB2-CONDFIN, round 12 (decision D66, item (M)). The root's mean formula in the post-head chart reads B's
stop word through the driver shifted at the entrance time. The positions of the marks compose:

* **`markPos_shiftDrive`**: `markPos (shiftDrive W τ) s (markPos W τ x) = markPos W (τ + s) x` for `x ≥ 0`, and
  **`markPosL_shiftDrive`** for `x ≤ 0` (by reflection);
* **`flowedData_shiftDrive`**, **`flowedJumps_shiftDrive`**: the flowed force data of marks `x` under `W` up to
  `τ + s` are the flowed data of the marks read at `τ` under the shifted driver up to `s`.

The proof: a real point alive at `τ + s` is alive at `τ`, and its image is alive for the shifted driver at `s`, with
the same final value (restart, `QuantumZipper.isForwardSol_shift`); conversely (gluing). The image `y ↦ f_τ(y)` maps
the alive points right of `x` onto `(markPos W τ x, ∞)` (intermediate values along the alive half-line).

Deterministic; no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (IsForwardSol fwdMap)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.SB.Cx

open Exist.StagedLaw (markPos markPosL)

variable {W : ℝ → ℝ}

/-- **Restarting a real point at `τ`**: alive at `τ + s` gives alive at `τ`, the image alive for the shifted driver at
`s`, and the same final value. -/
theorem alive_shift (hW : Continuous W) {y τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s)
    (h : ∃ u, IsForwardSol W (y : ℂ) (τ + s) u) :
    (∃ u, IsForwardSol W (y : ℂ) τ u) ∧
      (∃ u, IsForwardSol (shiftDrive W τ) (((fwdMap W τ (y : ℂ)).re : ℝ) : ℂ) s u) ∧
      (fwdMap W (τ + s) (y : ℂ)).re = (fwdMap (shiftDrive W τ) s (((fwdMap W τ (y : ℂ)).re : ℝ) : ℂ)).re := by
  obtain ⟨u, hu⟩ := h
  have hτm : τ ∈ Icc (0 : ℝ) (τ + s) := ⟨hτ, by linarith⟩
  have hfτ : fwdMap W τ (y : ℂ) = u τ := fwdMap_eq_of_isForwardSol hW hu hτm
  have hre : (((fwdMap W τ (y : ℂ)).re : ℝ) : ℂ) = u τ := by
    rw [hfτ]
    exact (LP.LP3.eq_ofReal_re_of_isForwardSol hW hu hτm).symm
  have hsh : IsForwardSol (shiftDrive W τ) (u τ) s (fun r => u (τ + r)) :=
    QuantumZipper.isForwardSol_shift hu hτ hs
  refine ⟨⟨u, QuantumZipper.isForwardSol_restrict hu hτ (by linarith)⟩, ⟨_, hre ▸ hsh⟩, ?_⟩
  rw [hre, fwdMap_eq_of_isForwardSol hW hu ⟨by linarith, le_rfl⟩,
    fwdMap_eq_of_isForwardSol (QuantumZipper.RS.continuous_shiftDrive hW τ) hsh ⟨hs, le_rfl⟩]

/-- **Gluing a real point at `τ`**: alive at `τ` with image alive for the shifted driver at `s` gives alive at
`τ + s`. -/
theorem alive_glue (hW : Continuous W) {y τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s)
    (h₁ : ∃ u, IsForwardSol W (y : ℂ) τ u)
    (h₂ : ∃ v, IsForwardSol (shiftDrive W τ) (((fwdMap W τ (y : ℂ)).re : ℝ) : ℂ) s v) :
    ∃ u, IsForwardSol W (y : ℂ) (τ + s) u := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  have hτm : τ ∈ Icc (0 : ℝ) τ := ⟨hτ, le_rfl⟩
  have hre : (((fwdMap W τ (y : ℂ)).re : ℝ) : ℂ) = u τ := by
    rw [fwdMap_eq_of_isForwardSol hW hu hτm]
    exact (LP.LP3.eq_ofReal_re_of_isForwardSol hW hu hτm).symm
  rw [hre] at hv
  exact ⟨_, QuantumZipper.isForwardSol_glue hτ hs hu hv⟩

/-- **The right marks compose along a shifted driver.** -/
theorem markPos_shiftDrive (hW : Continuous W) (hW0 : W 0 = 0) {τ s x : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s)
    (hx : 0 ≤ x) : markPos (shiftDrive W τ) s (markPos W τ x) = markPos W (τ + s) x := by
  have hW' : Continuous (shiftDrive W τ) := QuantumZipper.RS.continuous_shiftDrive hW τ
  have hW'0 : shiftDrive W τ 0 = 0 := QuantumZipper.RS.shiftDrive_zero W τ
  have hτs : 0 ≤ τ + s := add_nonneg hτ hs
  have hHτ := Exist.StagedLaw.isRealHalf_fwd hW hW0 hτ
  set m := markPos W τ x with hmdef
  have hm : 0 ≤ m := GW1W.markPos_nonneg hW hW0 hτ hx
  refine le_antisymm ?_ ?_
  · -- every alive rational point right of `x` at `τ + s` bounds the shifted mark from above
    refine GW1W.le_markPos hW hW0 hτs fun q hxq hq => ?_
    obtain ⟨hqτ, hq', heq⟩ := alive_shift hW (y := (q : ℝ)) hτ hs hq
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt hx hxq
    have hp : 0 < (fwdMap W τ ((q : ℝ) : ℂ)).re := hHτ.2.2.2.1 _ hq0 hqτ
    rw [heq]
    exact (GW1W.markPos_le_iff hW' hW'0 hs hm hp hq').2 (GW1W.markPos_le_rat hW hW0 hτ hx hxq hqτ)
  · -- every alive rational point right of the mark is the image of an alive point right of `x`
    refine GW1W.le_markPos hW' hW'0 hs fun q' hmq' hq' => ?_
    have hex : ∃ q₀ : ℚ, x < q₀ ∧ (∃ u, IsForwardSol W (((q₀ : ℚ) : ℝ) : ℂ) τ u) ∧
        (fwdMap W τ (((q₀ : ℚ) : ℝ) : ℂ)).re < q' := by
      by_contra hno
      push Not at hno
      have hle : ((q' : ℚ) : ℝ) ≤ m := GW1W.le_markPos hW hW0 hτ fun q hxq hq => hno q hxq hq
      linarith
    obtain ⟨q₀, hxq₀, hq₀, hlt⟩ := hex
    have hq₀0 : (0 : ℝ) < q₀ := lt_of_le_of_lt hx hxq₀
    obtain ⟨N, hN⟩ := hHτ.2.2.2.2.2.2 q'
    obtain ⟨M₀, hM₀⟩ := hHτ.2.2.1
    set y₁ : ℝ := max (max N M₀) (q₀ : ℝ) with hy₁
    have hq₀y₁ : (q₀ : ℝ) ≤ y₁ := le_max_right _ _
    have hA : ∀ y ∈ Icc (q₀ : ℝ) y₁, ∃ u, IsForwardSol W (y : ℂ) τ u := fun y hy => by
      rcases hy.1.lt_or_eq with h | h
      · exact hHτ.2.1 _ y hq₀0 h hq₀
      · rw [← h]; exact hq₀
    have hy₁A : ∃ u, IsForwardSol W (y₁ : ℂ) τ u := hM₀ _ ((le_max_right _ _).trans (le_max_left _ _))
    have hy₁f : ((q' : ℚ) : ℝ) ≤ (fwdMap W τ (y₁ : ℂ)).re := hN _ ((le_max_left _ _).trans (le_max_left _ _)) hy₁A
    have hcont : ContinuousOn (fun y : ℝ => (fwdMap W τ (y : ℂ)).re) (Icc (q₀ : ℝ) y₁) := by
      intro y hy
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨η, hη, hηf⟩ := hHτ.2.2.2.2.2.1 y (hq₀0.trans_le hy.1) (hA y hy) ε hε
      exact ⟨η, hη, fun y' hy' hd => by
        rw [Real.dist_eq] at hd ⊢
        exact hηf y' (hA y' hy') hd⟩
    obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc hq₀y₁ hcont ⟨hlt.le, hy₁f⟩
    have hyA := hA y hy
    have hxy : x < y := lt_of_lt_of_le hxq₀ hy.1
    have hfy' : (((fwdMap W τ (y : ℂ)).re : ℝ) : ℂ) = (((q' : ℚ) : ℝ) : ℂ) := congrArg (fun r : ℝ => (r : ℂ)) hfy
    have hy2 : ∃ v, IsForwardSol (shiftDrive W τ) (((fwdMap W τ (y : ℂ)).re : ℝ) : ℂ) s v := by
      rw [hfy']; exact hq'
    have hys := alive_glue hW hτ hs hyA hy2
    have heq := (alive_shift hW hτ hs hys).2.2
    rw [hfy'] at heq
    rw [← heq]
    exact (GW1W.markPos_le_iff hW hW0 hτs hx (lt_of_le_of_lt hx hxy) hys).2 hxy.le

/-- **The left marks compose along a shifted driver** (reflection of `markPos_shiftDrive`). -/
theorem markPosL_shiftDrive (hW : Continuous W) (hW0 : W 0 = 0) {τ s x : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s)
    (hx : x ≤ 0) : markPosL (shiftDrive W τ) s (markPosL W τ x) = markPosL W (τ + s) x := by
  have hN : Continuous fun r => -W r := hW.neg
  have hN0 : (fun r => -W r) 0 = 0 := by simp [hW0]
  have e : (fun r => -shiftDrive W τ r) = shiftDrive (fun r => -W r) τ := by
    funext r; simp only [shiftDrive]; ring
  have h := markPos_shiftDrive hN hN0 hτ hs (neg_nonneg.2 hx)
  unfold markPosL
  rw [e, neg_neg, h]

variable {nL nR : ℕ}

/-- **The flowed force data compose along a shifted driver.** -/
theorem flowedData_shiftDrive (hW : Continuous W) (hW0 : W 0 = 0) {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s) (k : ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0)
    (hxR : ∀ j, 0 ≤ xR j) :
    Supp8.Q3Chain.flowedData k ρL ρR (fun i => markPosL W τ (xL i)) (fun j => markPos W τ (xR j))
        (shiftDrive W τ) s = Supp8.Q3Chain.flowedData k ρL ρR xL xR W (τ + s) := by
  unfold Supp8.Q3Chain.flowedData
  congr 1
  · funext i; exact markPosL_shiftDrive hW hW0 hτ hs (hxL i)
  · funext j; exact markPos_shiftDrive hW hW0 hτ hs (hxR j)

/-- **The flowed jump sets compose along a shifted driver.** -/
theorem flowedJumps_shiftDrive (hW : Continuous W) (hW0 : W 0 = 0) {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) :
    Supp8.Q3Chain.flowedJumps (fun i => markPosL W τ (xL i)) (fun j => markPos W τ (xR j)) (shiftDrive W τ) s =
      Supp8.Q3Chain.flowedJumps xL xR W (τ + s) := by
  unfold Supp8.Q3Chain.flowedJumps
  congr 1
  · funext i; exact markPosL_shiftDrive hW hW0 hτ hs (hxL i)
  · funext j; exact markPos_shiftDrive hW hW0 hτ hs (hxR j)

end InteractingSLE.Theorem14.SB.Cx
