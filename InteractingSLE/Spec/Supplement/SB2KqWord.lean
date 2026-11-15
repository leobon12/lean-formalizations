/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JxShift
import InteractingSLE.Spec.Supplement.Q3ChainRetLaw
import InteractingSLE.Spec.Supplement.GB6LMeanFinal
import InteractingSLE.Spec.Sec5.CrossCondGenCloseMarks

/-!
# SB2(1)'s late (S) line mean, part 5: FIN's flowed relative word is K2's coupling data

Packet PROVE-T14-SB2DRV (round 9), the word match of `SB2JxFinStatement`. FIN's configuration carries the relative
word flowed by the relative driver `Wr` to the relative time `s` (`Q3Chain.flowedData`, the marks moved by `markPos`,
`markPosL`); K2's canonical mean uses `bheProc` of the geometric force coordinates `geomLW`, `geomRW` of its relative
driver `W`. When `Wr` agrees with `W` on `[0, s]`:

* **`flowedData_eq_geom`**: the two boundary data are equal (`Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg`,
  `markPosL_eq_rightImg_of_nonpos`, `GB6LMean.markPos_congr_eqOn`);
* **`eqOn_bheProc_of_flowedData`**: every bounded harmonic extension of FIN's flowed word is `bheProc … s` on `ℍ`.

Deterministic; no source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)

namespace InteractingSLE.Theorem14.SB.Lv

open Restart.DomainMarkov Sec7.PocketTraversal

variable {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {Ω : Type*} {W : ℝ≥0 → Ω → ℝ}

/-- **FIN's flowed relative word is K2's geometric force data** (relative drivers agreeing on `[0, s]`). -/
theorem flowedData_eq_geom (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0) {xL : Ω → Fin nL → ℝ}
    {xR : Ω → Fin nR → ℝ} {ω : Ω} (hxL : ∀ i, xL ω i ≤ 0) (hxR : ∀ j, 0 ≤ xR ω j) {Wr : ℝ → ℝ}
    (hWrc : Continuous Wr) (hWr0 : Wr 0 = 0) {s : ℝ≥0} (hWr : EqOn Wr (fun r : ℝ => W r.toNNReal ω) (Icc 0 s)) :
    Supp8.Q3Chain.flowedData κ ρL ρR (xL ω) (xR ω) Wr s =
      forceBoundaryData κ ρL ρR (fun i => geomLW W xL i s ω - W s ω) (fun j => geomRW W xR j s ω - W s ω) := by
  have hpc : Continuous fun r : ℝ => W r.toNNReal ω := (hWc ω).comp continuous_real_toNNReal
  have hp0 : (fun r : ℝ => W r.toNNReal ω) 0 = 0 := by simp only [Real.toNNReal_zero, hW0]
  have hL : (fun i => Exist.StagedLaw.markPosL Wr s (xL ω i)) = fun i => geomLW W xL i s ω - W s ω := by
    funext i
    rw [Supp8.GB6LMean.markPosL_congr_eqOn hWrc hWr0 hpc hp0 s.coe_nonneg hWr (hxL i),
      Sec5.CrossCond.Gen.markPosL_eq_rightImg_of_nonpos hpc hp0 s.coe_nonneg (hxL i)]
    simp only [geomLW, Real.toNNReal_coe]
    rfl
  have hR : (fun j => Exist.StagedLaw.markPos Wr s (xR ω j)) = fun j => geomRW W xR j s ω - W s ω := by
    funext j
    rw [Supp8.GB6LMean.markPos_congr_eqOn hWrc hWr0 hpc hp0 s.coe_nonneg hWr (hxR j),
      Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg hpc hp0 s.coe_nonneg (hxR j)]
    simp only [geomRW, Real.toNNReal_coe]
    rfl
  show forceBoundaryData κ ρL ρR (fun i => Exist.StagedLaw.markPosL Wr s (xL ω i))
    (fun j => Exist.StagedLaw.markPos Wr s (xR ω j)) = _
  rw [hL, hR]

/-- **Every bounded harmonic extension of FIN's flowed relative word is K2's `bheProc`.** -/
theorem eqOn_bheProc_of_flowedData (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {ω : Ω} (hxL : ∀ i, xL ω i ≤ 0) (hxR : ∀ j, 0 ≤ xR ω j)
    {Wr : ℝ → ℝ} (hWrc : Continuous Wr) (hWr0 : Wr 0 = 0) {s : ℝ≥0}
    (hWr : EqOn Wr (fun r : ℝ => W r.toNNReal ω) (Icc 0 s)) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension (Supp8.Q3Chain.flowedData κ ρL ρR (xL ω) (xR ω) Wr s)
      (Supp8.Q3Chain.flowedJumps (xL ω) (xR ω) Wr s) G) :
    EqOn G (bheProc κ ρL ρR W (geomLW W xL) (geomRW W xR) ω s) H := by
  rw [flowedData_eq_geom ρL ρR hWc hW0 hxL hxR hWrc hWr0 hWr] at hG
  have h2 := isBoundedHarmonicExtension_bheProc (κ := κ) (ρL := ρL) (ρR := ρR) (W := W) (VL := geomLW W xL)
    (VR := geomRW W xR) ω s
  set S' : Set ℝ := (Supp8.Q3Chain.flowedJumps (xL ω) (xR ω) Wr s : Set ℝ) ∪
    forceJumpSet (fun i => geomLW W xL i s ω - W s ω) (fun j => geomRW W xR j s ω - W s ω) with hS'
  have hS : S'.Finite := (Finset.finite_toSet _).union
    (((Set.finite_range _).union (Set.finite_range _)).insert 0)
  exact Impl.eqOn_of_isBoundedHarmonicExtension hS (LocalExt.IsBoundedHarmonicExtension.mono_set h2
    subset_union_right) (LocalExt.IsBoundedHarmonicExtension.mono_set hG subset_union_left)

end InteractingSLE.Theorem14.SB.Lv
