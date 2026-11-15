/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptLandTest

/-! # Rational witnesses for the landing test

A neighborhood with uniform transition bounds and positive boundary
clearances contains a rational landing interval about its center.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric MeasureTheory
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61GWindow20
open WangWu Aux61SlitW Aux61GWindow17 Aux61GInst Aux61Cpt LawUnique
universe u

/-- Shrink uniform local bounds to a rational landing parameter. -/
theorem exists_landParam_of_bounds (S : SourceSetting.{u}) (t : GoodTime S)
    (r : SourceRecord S.nL S.nR) {y ε M d : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (hupper : ∀ z ∈ H ∩ ball (y : ℂ) ε,
      ‖revChart (recDrv S r) (rationalTime S.s) (recPhys S t r z)‖ ≤ M ∧
      d ≤ (revChart (recDrv S r) (rationalTime S.s) (recPhys S t r z)).re)
    (hreal : ∀ a : ℝ, |a - y| < ε →
      d ≤ ‖boundedInverse (recordChart S t r) (a : ℂ) - 1‖ ∧
      d ≤ (recPhys S t r (a : ℂ)).im ∧
      d ≤ infDist (recPhys S t r (a : ℂ)) (recPrefix S t r)) :
    ∃ L : LandParam, |y - L.1.1| < L.1.2.1 ∧
      ball ((L.1.1 : ℝ) : ℂ) (L.1.2.1 : ℝ) ⊆ ball (y : ℂ) ε ∧ landTest S t L r := by
  obtain ⟨v, hv₁, hv₂⟩ := exists_rat_btwn (show y - ε / 8 < y + ε / 8 by linarith)
  obtain ⟨e, he₁, he₂⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
  obtain ⟨m, hm⟩ := exists_rat_gt M
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hd
  have he : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℝ) < e by linarith)
  have hq : (0 : ℚ) < q := by exact_mod_cast hq₁
  let L : LandParam := ⟨(v, e, m, q), he, hq⟩
  have hv : |(v : ℝ) - y| < ε / 8 := abs_lt.2 ⟨by linarith, by linarith⟩
  have hsub : ball ((v : ℝ) : ℂ) (e : ℝ) ⊆ ball (y : ℂ) ε := by
    intro z hz
    have hdist : dist ((v : ℝ) : ℂ) (y : ℂ) < ε / 8 := by
      simpa only [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hv
    exact mem_ball.2 ((dist_triangle z ((v : ℝ) : ℂ) (y : ℂ)).trans_lt
      (by have := mem_ball.1 hz; linarith))
  refine ⟨L, ?_, hsub, ?_, ?_⟩
  · change |y - (v : ℝ)| < (e : ℝ)
    rw [abs_sub_comm]
    linarith
  · intro a b hb hz
    have hH : ratPt a b ∈ H := by
      change (0 : ℝ) < (ratPt a b).im
      simp only [ratPt]
      exact_mod_cast hb
    obtain ⟨hM, hd'⟩ := hupper _ ⟨hH, hsub hz⟩
    exact ⟨hM.trans hm.le, hq₂.le.trans hd'⟩
  · intro a ha
    have ha' : |(a : ℝ) - y| < ε := by
      have htri := abs_sub_le (a : ℝ) (v : ℝ) y
      change |(a : ℝ) - (v : ℝ)| ≤ (e : ℝ) at ha
      linarith
    obtain ⟨h₁, h₂, h₃⟩ := hreal (a : ℝ) ha'
    exact ⟨hq₂.le.trans h₁, hq₂.le.trans h₂, hq₂.le.trans h₃⟩

end InteractingSLE.Sec5.Aux61GWindow20
