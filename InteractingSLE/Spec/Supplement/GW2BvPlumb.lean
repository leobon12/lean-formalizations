/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvInst
import InteractingSLE.Spec.Supplement.GW2BtClause

/-!
# The near frame of `VNearImgOn` is the cell-exit frame

Packet PROVE-GW2-BUF (round 19). `VNearImgOn` reads the near variable in the frame
`s ↦ (−1)^{|l|} 2^k λ R(s / (4^k λ²))` with the time factor `4^k λ²`. Round 18's cell-exit clauses
(`nearClauses_of_good'`) are stated for `scaledPath A B w` with `A = c₂²`, `B = ± c₂`.

* `nearSign_flipOf`, `four_pow_mul_lamL_sq`, **`nearFrame_eq_scaledPath`**, **`coe_four_pow_mul_lam_sq`**;
* **`pkgF_nearVar_stop`**: at a good root, the final package's near stop is the minimum of the lower-cap stop
  `V_{m−1} − S` (on the good records) and the exit rule on the killed stage path; `pkgF_nearVar_R`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx
  GW2Sdy

theorem nearSign_flipOf (n : ℕ) : nearSign (GW2Sdf.flipOf n) = (-1 : ℝ) ^ n := by
  unfold nearSign GW2Sdf.flipOf
  rcases Nat.even_or_odd n with h | h
  · have hn : ¬ Odd n := Nat.not_odd_iff_even.2 h
    simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (h.neg_one_pow).symm
  · simp only [h, decide_true, ↓reduceIte]
    exact (h.neg_one_pow).symm

theorem four_pow_mul_lamL_sq {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q)) :
    (4 : ℝ≥0) ^ r.2 * lamL l ^ 2 = c2L r l ^ 2 := by
  unfold c2L
  rw [mul_pow, ← pow_mul, mul_comm r.2 2, pow_mul]
  norm_num

/-- **`VNearImgOn`'s near frame is the cell-exit frame** `scaledPath (c₂²) (± c₂)`. -/
theorem nearFrame_eq_scaledPath {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q))
    (w : ℝ≥0 → ℝ) :
    (fun s => (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * (lamL l : ℝ) * w (s / ((4 : ℝ≥0) ^ r.2 * lamL l ^ 2)))) =
      scaledPath (c2L r l ^ 2) (nearSign (GW2Sdf.flipOf l.length) * c2L r l) w := by
  funext s
  unfold scaledPath
  rw [four_pow_mul_lamL_sq, nearSign_flipOf]
  unfold c2L
  push_cast
  ring

theorem coe_four_pow_mul_lam_sq {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q)) :
    (4 : ℝ≥0∞) ^ r.2 * ((lamL l : ℝ≥0) : ℝ≥0∞) ^ 2 = ((c2L r l ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [← four_pow_mul_lamL_sq]
  push_cast
  rfl

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u}) (K₀ : PkgFamily.{u})
  (kSel : NearSelB.{u})

/-- **The final package's near stop** at a good root (`m = m' + 1`). -/
theorem pkgF_nearVar_stop {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hg : GoodRoot c r) (l : List (EntryIdx c.Θ c.Q)) (k n m' a : ℕ) (ξ : Ω) :
    (((pkgF h13 h12 K₀ kSel k).at 0 Ω c r).nearVar l n (m' + 1) a).stop ξ =
      min ((lowCapStopX c l (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a (m' + 1) hg.1) (rootPt r.1)
          ((pkgVerF h13 h12 Ω c r l a).V m') ((pkgVerF h13 h12 Ω c r l a).isA hg.1 m').1.2.choose).stop ξ)
        (exitB.{u} Ω c r l n a
          ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a (m' + 1) hg.1).srecX c r l (rootPt r.1) ξ,
            killPath ((fun t => (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a (m' + 1) hg.1).drvX c
              (rootPt r.1) t ξ),
              (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a (m' + 1) hg.1).capX c (rootPt r.1) ξ))) := by
  change ((pkgX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) (pkgKbF h13 h12 K₀) Ω c r).nearVar l n (m' + 1)
    a).stop ξ = _
  rw [pkgNearVar_eq h13 h12 (psiGoodFam h13 h12) cwSrc exitB K₀ c r hg l n (m' + 1) a]
  change ((pkgKbF h13 h12 K₀ Ω c r).nearStop l n (m' + 1) a).stop ξ = _
  simp only [pkgKbF, pkgKb, nearStopPkgX, hg, ↓reduceDIte, Nat.add_sub_cancel]
  rfl

/-- The final package's near driver at a good root is the instance's stage driver. -/
theorem pkgF_nearVar_R {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hg : GoodRoot c r) (l : List (EntryIdx c.Θ c.Q)) (k n m a : ℕ) :
    (((pkgF h13 h12 K₀ kSel k).at 0 Ω c r).nearVar l n m a).R =
      (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hg.1).drvX c (rootPt r.1) := by
  change ((pkgX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) (pkgKbF h13 h12 K₀) Ω c r).nearVar l n m a).R = _
  rw [pkgNearVar_eq h13 h12 (psiGoodFam h13 h12) cwSrc exitB K₀ c r hg l n m a]
  rfl

end InteractingSLE.Theorem14.GW2Bh
