/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvPlumb

/-!
# The near clauses of one sample in `VNearImgOn`'s frame

Packet PROVE-GW2-BUF (round 19). Round 18's `nearClauses_of_good'` gives the three clauses for the cell exit
`exitB` in the frame `scaledPath (c₂²) (± c₂)`. Here they are restated for a near variable `v` whose driver is the
stage path `w` and whose stop is `min (lower cap, exitB on the killed path)`. They are read in `VNearImgOn`'s frame
`s ↦ (−1)^{|l|} 2^k λ v.R (s / (4^k λ²))` with the factor `4^k λ²` (`nearFrame_eq_scaledPath`,
`coe_four_pow_mul_lam_sq`).

* **`vnearClauses_of_good`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootN4 GW2TipSystem.RootC24 GW2JDetR11
  GW2Sde GW2Sdy

/-- **The near clauses of one sample in `VNearImgOn`'s frame.** -/
theorem vnearClauses_of_good {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (f : NearCrossingFamily.{u} c.κ) (n : ℕ) (v : StageVar Ω) (ξ : Ω) {y : RecData}
    {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (hvR : ∀ t, v.R t ξ = w t) {Lst cap : ℝ≥0∞}
    (hLcap : Lst ≤ cap)
    (hstop : v.stop ξ = min Lst (cellStop (cellOf n (shapeD c r l) (posLD c r l) (posRD c r l)) (posLD c r l)
      (posRD c r l) (c2L r l ^ 2) (nearSign (GW2Sdf.flipOf l.length) * c2L r l) (((n : ℝ≥0) + 1) / c2L r l ^ 2)
      (y, killPath (w, cap))))
    (hsh : famShapeB f = shapeD c r l y) (hL : ∀ i : Fin f.nL, f.xL i = posLD c r l y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posRD c r l y j)
    (hgood : cellStop (cellOf n (shapeD c r l) (posLD c r l) (posRD c r l)) (posLD c r l) (posRD c r l)
      (c2L r l ^ 2) (nearSign (GW2Sdf.flipOf l.length) * c2L r l) (((n : ℝ≥0) + 1) / c2L r l ^ 2) (y, w) < Lst)
    {P : Prop}
    (hreach : ∀ t : ℝ≥0, t < (n : ℝ≥0) →
      (t : ℝ≥0∞) < ((c2L r l ^ 2 : ℝ≥0) : ℝ≥0∞) * v.stop ξ →
      GW2Sdg.imgState f.xL f.xR (scaledPath (c2L r l ^ 2) (nearSign (GW2Sdf.flipOf l.length) * c2L r l) w) t ∈
        nearTarget f → P) :
    0 < (4 : ℝ≥0∞) ^ r.2 * ((lamL l : ℝ≥0) : ℝ≥0∞) ^ 2 * v.stop ξ ∧
      (∀ v' : ℝ≥0, (v' : ℝ≥0∞) = (4 : ℝ≥0∞) ^ r.2 * ((lamL l : ℝ≥0) : ℝ≥0∞) ^ 2 * v.stop ξ → v' < (n : ℝ≥0) →
        GW2Sdg.imgState f.xL f.xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * (lamL l : ℝ) * v.R (s / ((4 : ℝ≥0) ^ r.2 * lamL l ^ 2)) ξ)) v' ∉ nearBuffer f n) ∧
      ∀ t : ℝ≥0, t < (n : ℝ≥0) → (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * ((lamL l : ℝ≥0) : ℝ≥0∞) ^ 2 * v.stop ξ →
        GW2Sdg.imgState f.xL f.xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * (lamL l : ℝ) * v.R (s / ((4 : ℝ≥0) ^ r.2 * lamL l ^ 2)) ξ)) t ∈ nearTarget f → P := by
  have hfr : (fun s => (-1 : ℝ) ^ l.length *
      ((2 : ℝ) ^ r.2 * (lamL l : ℝ) * v.R (s / ((4 : ℝ≥0) ^ r.2 * lamL l ^ 2)) ξ)) =
      scaledPath (c2L r l ^ 2) (nearSign (GW2Sdf.flipOf l.length) * c2L r l) w := by
    rw [← nearFrame_eq_scaledPath r l w]
    funext s
    rw [hvR]
  rw [coe_four_pow_mul_lam_sq, hfr]
  have hreach' : ∀ t : ℝ≥0, t < (n : ℝ≥0) →
      (t : ℝ≥0∞) < ((c2L r l ^ 2 : ℝ≥0) : ℝ≥0∞) * min Lst (cellStop (cellOf n (shapeD c r l) (posLD c r l)
        (posRD c r l)) (posLD c r l) (posRD c r l) (c2L r l ^ 2) (nearSign (GW2Sdf.flipOf l.length) * c2L r l)
        (((n : ℝ≥0) + 1) / c2L r l ^ 2) (y, killPath (w, cap))) →
      GW2Sdg.imgState f.xL f.xR (scaledPath (c2L r l ^ 2) (nearSign (GW2Sdf.flipOf l.length) * c2L r l) w) t ∈
        nearTarget f → P := fun t ht htv => hreach t ht (by rw [hstop]; exact htv)
  rw [hstop]
  exact nearClauses_of_good' f n hsh hL hR (pow_pos (c2L_pos r l) 2) _ hw hw0 hLcap hgood hreach'

end InteractingSLE.Theorem14.GW2Bh
