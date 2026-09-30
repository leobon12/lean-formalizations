import QuantumZipper.Proofs.Zipper.SWCoreB7bFlowWin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b-FLOW (5): choice of the rational window

`b7bf_setup`: around `s₀ ∈ [q,T]` there are rational `a < b` and margins `η, ε > 0` such that for
`|s - s₀| ≤ ε` the moving images of `u, u', v', v` under `F_{T-s}` stay `η/2` away from `a, b`
on the correct sides, and `|W s - W s₀| < η/4`. Own bookkeeping (continuity in time of the carrier,
`b7bf_continuousOn_time`, and strict monotonicity in space, `b7bf_strictMonoOn`).
-/

noncomputable section

open Complex Filter MeasureTheory Set Metric
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace SWCore

open RevMapExtension B2

variable {W : ℝ → ℝ}

theorem b7bf_near (hW : Continuous W) {T q x : ℝ} (hqT : q ≤ T)
    (hx : ENNReal.ofReal (T - q) < realHitTime (vrev W T) x) {s₀ : ℝ} (hs₀ : s₀ ∈ Icc q T)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ s ∈ Icc q T, |s - s₀| < δ →
      |realRevMap (vrev W T) (T - s) x - realRevMap (vrev W T) (T - s₀) x| < η := by
  have hc := b7bf_continuousOn_time (continuous_vrev hW T) hx
  obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.1
    (hc (T - s₀) ⟨by linarith [hs₀.2], by linarith [hs₀.1]⟩) η hη
  refine ⟨δ, hδ, fun s hs hss => ?_⟩
  have h1 := h (x := T - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ (by
    rw [Real.dist_eq, show T - s - (T - s₀) = -(s - s₀) by ring, abs_neg]; exact hss)
  rwa [Real.dist_eq] at h1

theorem b7bf_setup (hW : Continuous W) {T q : ℝ} (hqT : q ≤ T) {u v u' v' : ℝ}
    (huu' : u < u') (hu'v' : u' < v') (hv'v : v' < v)
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal (T - q) < realHitTime (vrev W T) x) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc q T) :
    ∃ a b : ℚ, ∃ η ε : ℝ, 0 < η ∧ 0 < ε ∧ ε ≤ η / 8 ∧ ∀ s ∈ Icc q T, |s - s₀| ≤ ε →
      realRevMap (vrev W T) (T - s) u < a - η / 2 ∧
      (a : ℝ) + η / 2 < realRevMap (vrev W T) (T - s) u' ∧
      realRevMap (vrev W T) (T - s) v' < b - η / 2 ∧
      (b : ℝ) + η / 2 < realRevMap (vrev W T) (T - s) v ∧ |W s - W s₀| < η / 4 := by
  set V := vrev W T with hVdef
  have hV : Continuous V := continuous_vrev hW T
  have hσ₀ : T - s₀ ∈ Icc (0 : ℝ) (T - q) := ⟨by linarith [hs₀.2], by linarith [hs₀.1]⟩
  have hmono := b7bf_strictMonoOn hV hLive hσ₀
  have hu : u ∈ Icc u v := ⟨le_rfl, by linarith⟩
  have hu' : u' ∈ Icc u v := ⟨huu'.le, by linarith⟩
  have hv' : v' ∈ Icc u v := ⟨by linarith, hv'v.le⟩
  have hv : v ∈ Icc u v := ⟨by linarith, le_rfl⟩
  have h1 := hmono hu hu' huu'
  have h3 := hmono hv' hv hv'v
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn h1
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn h3
  set η := min (min ((a : ℝ) - realRevMap V (T - s₀) u) (realRevMap V (T - s₀) u' - a))
    (min ((b : ℝ) - realRevMap V (T - s₀) v') (realRevMap V (T - s₀) v - b)) with hηdef
  have hη : 0 < η := lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith)
    (by linarith))
  have e1 : η ≤ (a : ℝ) - realRevMap V (T - s₀) u := (min_le_left _ _).trans (min_le_left _ _)
  have e2 : η ≤ realRevMap V (T - s₀) u' - a := (min_le_left _ _).trans (min_le_right _ _)
  have e3 : η ≤ (b : ℝ) - realRevMap V (T - s₀) v' := (min_le_right _ _).trans (min_le_left _ _)
  have e4 : η ≤ realRevMap V (T - s₀) v - b := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δ₁, hδ₁, n₁⟩ := b7bf_near hW hqT (hLive u hu) hs₀ (half_pos hη)
  obtain ⟨δ₂, hδ₂, n₂⟩ := b7bf_near hW hqT (hLive u' hu') hs₀ (half_pos hη)
  obtain ⟨δ₃, hδ₃, n₃⟩ := b7bf_near hW hqT (hLive v' hv') hs₀ (half_pos hη)
  obtain ⟨δ₄, hδ₄, n₄⟩ := b7bf_near hW hqT (hLive v hv) hs₀ (half_pos hη)
  obtain ⟨δW, hδW, nW⟩ := Metric.continuous_iff.1 hW s₀ (η / 4) (by positivity)
  set ε := min (min (min δ₁ δ₂) (min δ₃ δ₄)) (min δW (η / 8)) / 2 with hεdef
  have hm1 : min (min (min δ₁ δ₂) (min δ₃ δ₄)) (min δW (η / 8)) ≤ δ₁ :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hm2 : min (min (min δ₁ δ₂) (min δ₃ δ₄)) (min δW (η / 8)) ≤ δ₂ :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hm3 : min (min (min δ₁ δ₂) (min δ₃ δ₄)) (min δW (η / 8)) ≤ δ₃ :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm4 : min (min (min δ₁ δ₂) (min δ₃ δ₄)) (min δW (η / 8)) ≤ δ₄ :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hm5 : min (min (min δ₁ δ₂) (min δ₃ δ₄)) (min δW (η / 8)) ≤ δW :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hm6 : min (min (min δ₁ δ₂) (min δ₃ δ₄)) (min δW (η / 8)) ≤ η / 8 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hmpos : 0 < min (min (min δ₁ δ₂) (min δ₃ δ₄)) (min δW (η / 8)) :=
    lt_min (lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδ₄)) (lt_min hδW (by positivity))
  refine ⟨a, b, η, ε, hη, by positivity, by linarith, fun s hs hss => ?_⟩
  have g1 := abs_lt.1 (n₁ s hs (by linarith))
  have g2 := abs_lt.1 (n₂ s hs (by linarith))
  have g3 := abs_lt.1 (n₃ s hs (by linarith))
  have g4 := abs_lt.1 (n₄ s hs (by linarith))
  have gW := nW s (by rw [Real.dist_eq]; linarith)
  rw [Real.dist_eq] at gW
  refine ⟨by linarith [g1.2], by linarith [g2.1], by linarith [g3.2], by linarith [g4.1], gW⟩

end SWCore
end QuantumZipper
