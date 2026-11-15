/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BqSpec
import InteractingSLE.Spec.Supplement.GW2BoStop

/-!
# nearImg's clauses at one sample of the good event

Packet PROVE-GW2-BUF (round 15). At one sample `ξ`:
* the near stop is `min (L, E)`: the lower-cap stop `L` and the cell exit `E` read on the killed stage path;
* the record `y` carries the near family `f`'s shape and labels (D16's decoder);
* the stage path `w` is continuous from `0`;
* the exit on the unkilled path comes before the lower cap, which is itself at most the cap.

Then the stop is the exit, and the three clauses of `VNearImgOn` hold in its exact form. The comparison path is
`s ↦ B · w (s / A)` with `A = 4^k λ²` and `B = (−1)^len 2^k λ`, and the stop scale is `A`. Clause (iii) is the reach
implication, supplied as a hypothesis.

* **`nearClauses_of_good`**.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootN4 GW2JDetR11

/-- **The clauses of `VNearImgOn` at one sample of the good event.** -/
theorem nearClauses_of_good {κ : ℝ} (f : NearCrossingFamily.{u} κ) (n : ℕ) {shape : RecData → NearShape}
    {posL posR : RecData → ℕ → ℝ} {y : RecData} (hsh : famShapeB f = shape y)
    (hL : ∀ i : Fin f.nL, f.xL i = posL y i) (hR : ∀ j : Fin f.nR, f.xR j = posR y j)
    {A : ℝ≥0} (hA : 0 < A) (B : ℝ) {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {Lst cap : ℝ≥0∞} (hLcap : Lst ≤ cap)
    (hgood : cellStop (cellOf n shape posL posR) posL posR A B ((n : ℝ≥0) / A) (y, w) < Lst)
    {P : Prop}
    (hreach : ∀ t : ℝ≥0, t < (n : ℝ≥0) →
      (t : ℝ≥0∞) < (A : ℝ≥0∞) * min Lst (cellStop (cellOf n shape posL posR) posL posR A B ((n : ℝ≥0) / A)
        (y, killPath (w, cap))) →
      GW2Sdg.imgState f.xL f.xR (scaledPath A B w) t ∈ nearTarget f → P)
    (hn : 0 < n) :
    0 < (A : ℝ≥0∞) * min Lst (cellStop (cellOf n shape posL posR) posL posR A B ((n : ℝ≥0) / A)
        (y, killPath (w, cap))) ∧
      (∀ v : ℝ≥0, (v : ℝ≥0∞) = (A : ℝ≥0∞) * min Lst (cellStop (cellOf n shape posL posR) posL posR A B
          ((n : ℝ≥0) / A) (y, killPath (w, cap))) → v < (n : ℝ≥0) →
        GW2Sdg.imgState f.xL f.xR (scaledPath A B w) v ∉ nearBuffer f n) ∧
      ∀ t : ℝ≥0, t < (n : ℝ≥0) →
        (t : ℝ≥0∞) < (A : ℝ≥0∞) * min Lst (cellStop (cellOf n shape posL posR) posL posR A B ((n : ℝ≥0) / A)
          (y, killPath (w, cap))) →
        GW2Sdg.imgState f.xL f.xR (scaledPath A B w) t ∈ nearTarget f → P := by
  set E := cellStop (cellOf n shape posL posR) posL posR A B ((n : ℝ≥0) / A) with hEdef
  have hc : (0 : ℝ≥0) < (n : ℝ≥0) / A := div_pos (by exact_mod_cast hn) hA
  obtain ⟨hsub, h0⟩ := cellOf_spec f n hsh hL hR
  have hlabL : ∀ i, f.xL i ≤ 0 := fun i => by
    by_cases h : f.xL i = 0
    · exact h.le
    · exact (f.hxL i h).trans (neg_nonpos.2 f.hη.le)
  have hlabR : ∀ j, 0 ≤ f.xR j := fun j => by
    by_cases h : f.xR j = 0
    · exact h.ge
    · exact f.hη.le.trans (f.hxR j h)
  have hsw0 : scaledPath A B w 0 = 0 := by simp [scaledPath, hw0]
  have h0' : GW2Sdg.imgState f.xL f.xR (scaledPath A B w) 0 ∈
      cellBuf (famShapeB f, (cellOf n shape posL posR y).2.1, (cellOf n shape posL posR y).2.2) := by
    rw [imgState_zero f.xL f.xR hlabL hlabR hsw0]
    exact h0
  obtain ⟨τ, hτ, hτ0, -, hout⟩ := exit_spec_cell f n (cellOf n shape posL posR) posL posR y hsh hL hR hsub A B hc hw h0'
  -- the exit on the killed path is the exit on the path
  have hEcap : E (y, w) < cap := hgood.trans_le hLcap
  have hkill : E (y, killPath (w, cap)) = E (y, w) :=
    rule_killPath_eq (isPathRule_cellStop _ posL posR hA B _) y (w, cap) hEcap
  have hmin : min Lst (E (y, killPath (w, cap))) = (τ : ℝ≥0∞) := by
    rw [hkill, min_eq_right hgood.le]
    exact hτ
  rw [hmin]
  refine ⟨ENNReal.mul_pos (by exact_mod_cast hA.ne') (by exact_mod_cast hτ0.ne'), fun v hv hvn => ?_, ?_⟩
  · have hv' : v = A * τ := by exact_mod_cast hv
    rw [hv']
    refine hout ?_
    rw [hv'] at hvn
    rw [lt_div_iff₀ hA, mul_comm]
    exact hvn
  · intro t ht htv htar
    exact hreach t ht (by rw [hmin]; exact htv) htar

end InteractingSLE.Theorem14.GW2Bh
