/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BmTip
import InteractingSLE.Spec.Supplement.GW2BlCol

/-!
# Exit before death without an open zero gap (D12 item 1)

Packet PROVE-GW2-BUF (round 10). Round 9's `GW2BlCol.rightImg_eq_of_real_tip` (a real physical tip before contact
collides every relative label left of its chart image) asked the relative zero gap to stay open before the tip. As at
the contact (`GW2BmTip`), the right condition is that the tip lies beyond the earlier real visits. This file proves
that form.

* **`rightImg_eq_of_real_tip_off`**: if the physical tip at `τ` is real and the relative trace avoids `[x₀, ∞)`
  before `a τ`, for some `0 < x₀ ≤ Re relBdry (γ τ)`, then every relative label `x ≤ Re relBdry (γ τ)` collides
  with the relative driver at `a τ`.
* **`rightImg_neg_eq_of_real_tip_off`**: the mirror form, for left labels and the negated driver.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Bh

open MartChar.RealFlow Supp8.GB6.CoordB Restart

variable {U : ℝ → ℝ} {s : ℝ} {γ : ℝ≥0 → ℂ} {a : ℝ≥0 → ℝ} {τ : ℝ≥0}

/-- The chart image of a real safe tip is real. -/
theorem im_relBdry_tip (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (hsafe : MapsTo γ (Iic τ) (relSafe U s))
    (him : (γ τ).im = 0) : (relBdry U s (γ τ)).im = 0 := by
  have hmem : γ τ ∈ relSafe U s := hsafe (le_refl τ)
  have hreal : γ τ = (((γ τ).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hreal]
  refine im_relBdry_of_real hU hU0 hs ?_
  rw [← hreal]
  exact hmem.2

/-- **A real physical tip beyond the earlier real visits collides every relative label left of it.** -/
theorem rightImg_eq_of_real_tip_off (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (ha : IsClockOn a τ)
    (hγc : ContinuousOn γ (Iic τ)) (hγ0 : γ 0 = 0) (hsafe : MapsTo γ (Iic τ) (relSafe U s)) {R : ℝ → ℝ}
    (hRc : Continuous R) (hR0 : R 0 = 0) (hK : ∀ t ≤ τ, fwdHull R (a t) = fillH (relBdry U s '' (γ '' Icc 0 t)))
    (hσ : 0 < a τ) (him : (γ τ).im = 0) {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀le : x₀ ≤ (relBdry U s (γ τ)).re)
    (hoff : ∀ u ∈ Ico 0 (a τ), ∀ r : ℝ, x₀ ≤ r → relTrace U s γ a τ u ≠ r) {x : ℝ}
    (hxle : x ≤ (relBdry U s (γ τ)).re) : rightImg R x (a τ) = R (a τ) := by
  have hη := isLoewnerTraceLT_relTrace hU hU0 hs ha hγc hγ0 hsafe hK
  have hc := continuousOn_relTrace hU hU0 hs ha hγc hsafe
  have hend := relTrace_end (U := U) (s := s) (γ := γ) ha
  have halive : ∀ t ∈ Ico 0 (a τ), Alive R x₀ t := fun t ht =>
    alive_of_traceLT_off hRc hR0 hη ht.1 ht.2 hx₀ fun u hu => hoff u ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩
  refine rightImg_eq_of_alive_tip hRc hR0 hσ hη hc ?_ hx₀ ?_ halive ?_
  · rw [hend]; exact im_relBdry_tip hU hU0 hs hsafe him
  · rw [hend]; exact hx₀le
  · rw [hend]; exact hxle

/-- **The mirror form**: a real physical tip left of the earlier real visits collides every relative left label
right of it (read as right labels `−x` of the negated driver). -/
theorem rightImg_neg_eq_of_real_tip_off (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (ha : IsClockOn a τ)
    (hγc : ContinuousOn γ (Iic τ)) (hγ0 : γ 0 = 0) (hsafe : MapsTo γ (Iic τ) (relSafe U s)) {R : ℝ → ℝ}
    (hRc : Continuous R) (hR0 : R 0 = 0) (hK : ∀ t ≤ τ, fwdHull R (a t) = fillH (relBdry U s '' (γ '' Icc 0 t)))
    (hσ : 0 < a τ) (him : (γ τ).im = 0) {x₀ : ℝ} (hx₀ : x₀ < 0) (hx₀le : (relBdry U s (γ τ)).re ≤ x₀)
    (hoff : ∀ u ∈ Ico 0 (a τ), ∀ r : ℝ, r ≤ x₀ → relTrace U s γ a τ u ≠ r) {x : ℝ}
    (hxle : (relBdry U s (γ τ)).re ≤ x) : rightImg (-R) (-x) (a τ) = (-R) (a τ) := by
  have hη := isLoewnerTraceLT_relTrace hU hU0 hs ha hγc hγ0 hsafe hK
  have hc := continuousOn_relTrace hU hU0 hs ha hγc hsafe
  have hend := relTrace_end (U := U) (s := s) (γ := γ) ha
  have hη' := SB.Vo.isLoewnerTraceLT_reflect hη
  have hc' : ContinuousOn (fun t => LP.reflectC (relTrace U s γ a τ t)) (Icc 0 (a τ)) :=
    LP.continuous_reflectC.comp_continuousOn hc
  have hre : ∀ z : ℂ, (LP.reflectC z).re = -z.re ∧ (LP.reflectC z).im = z.im := fun z => by
    simp [LP.reflectC]
  have hR' : Continuous (-R) := hRc.neg
  have hR0' : (-R) 0 = 0 := by simp [hR0]
  have halive : ∀ t ∈ Ico 0 (a τ), Alive (-R) (-x₀) t := fun t ht =>
    alive_of_traceLT_off hR' hR0' hη' ht.1 ht.2 (neg_pos.2 hx₀) fun u hu r hr h => by
      apply hoff u ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩ (-r) (by linarith)
      have h2 := congrArg LP.reflectC h
      rw [LP.reflectC_reflectC] at h2
      rw [h2]
      apply Complex.ext <;> simp [LP.reflectC]
  have himR := im_relBdry_tip hU hU0 hs hsafe him
  refine rightImg_eq_of_alive_tip hR' hR0' hσ hη' hc' ?_ (neg_pos.2 hx₀) ?_ halive ?_
  · rw [(hre _).2, hend]; exact himR
  · rw [(hre _).1, hend]; linarith
  · rw [(hre _).1, hend]; linarith

end InteractingSLE.Theorem14.GW2Bh
