import HigherDimLQGMetric.Determ.NearPath

/-! First and last cell hits control the cell part of a near-geodesic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {d : ℕ}

theorem determ_piece_le {D : ContMetric d} {n : ℕ} {r κ : ℝ}
    (hr : ∀ (a b : ℝ) (P : ℝ → (Rd d)), ContinuousOn P (Icc a b) →
      MapsTo P (Icc a b) (Metric.closedBall 0 (n : ℝ)) →
      ∀ ε' : ℝ≥0∞, D.len P a b ≤ D.internal (Metric.ball 0 (n : ℝ)) (P a) (P b) + ε' →
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ b → ‖P s - P u‖ < r →
        D.len P s u + D.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) (P a) (P b) ≤
          D.internal (Metric.ball 0 (n : ℝ)) (P a) (P b) + ε' + ENNReal.ofReal κ)
    {P : ℝ → (Rd d)} (hP : Continuous P) (hfin : D.len P 0 1 ≠ ⊤)
    (hPn : MapsTo P (Icc 0 1) (Metric.closedBall 0 (n : ℝ))) {e : ℝ} (he : 0 ≤ e)
    (hnear : D.len P 0 1 ≤ D.internal (Metric.ball 0 (n : ℝ)) (P 0) (P 1) + ENNReal.ofReal e)
    (hF0 : D.internal (Metric.ball 0 (n : ℝ)) (P 0) (P 1) ≠ ⊤) (hκ : 0 ≤ κ)
    {ε : ℝ} (hε : 0 < ε) (hεr : Real.sqrt d * ε < r)
    (θ : Fin d → ℝ) (k : Fin d → ℤ) :
    determPiece D P 0 1 ε θ k ≤
      (D.internal (Metric.ball 0 (n : ℝ)) (P 0) (P 1)).toReal + e + κ -
        (D.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) (P 0) (P 1)).toReal := by
  set I₀ := D.internal (Metric.ball 0 (n : ℝ)) (P 0) (P 1)
  set I₁ := D.internal (Metric.ball 0 ((n + 1 : ℕ) : ℝ)) (P 0) (P 1)
  have hI : I₁ ≤ I₀ := internalEDist_anti (image_mono (Metric.ball_subset_ball (by
    push_cast; linarith))) _ _
  have hI₁ : I₁ ≠ ⊤ := ne_top_of_le_ne_top hF0 hI
  have hrhs : 0 ≤ I₀.toReal + e + κ - I₁.toReal := by
    have := ENNReal.toReal_mono hF0 hI; linarith
  have hcurve : LQGMetric.LM.T17Curve (D.pt ∘ P) 0 1 := ⟨zero_le_one, D.continuous_pt.comp_continuousOn
    hP.continuousOn, hfin⟩
  by_cases hex : ∃ t ∈ Icc (0 : ℝ) 1, P t ∈ closure (determCube ε θ k)
  · obtain ⟨t₀, ht₀, hPt₀⟩ := hex
    obtain ⟨s, u, hs, hsu, hu, hPs, hPu, hall⟩ :=
      determ_first_last_hit hP.continuousOn isClosed_closure ht₀ hPt₀
    have hsub : Icc (0 : ℝ) 1 ∩ P ⁻¹' determCube ε θ k ⊆ Icc s u := fun t ⟨ht, hPt⟩ =>
      hall t ht (subset_closure hPt)
    have h1 := LQGMetric.LM.t17LenMeas_le_of_subset hcurve hs hsu hu hsub
    have hnorm : ‖P s - P u‖ < r := (determ_closure_cube_norm (le_of_lt hε) hPs hPu).trans_lt hεr
    have h2 := hr 0 1 P hP.continuousOn hPn (ENNReal.ofReal e) hnear s u hs hsu hu hnorm
    have hlsu : D.len P s u ≠ ⊤ := ne_top_of_le_ne_top hfin
      (eVariationOn.mono _ (Icc_subset_Icc hs hu))
    have h3 := ENNReal.toReal_mono (by finiteness) h2
    rw [ENNReal.toReal_add hlsu hI₁, ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
      ENNReal.toReal_add hF0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal he,
      ENNReal.toReal_ofReal hκ] at h3
    have h4 : determPiece D P 0 1 ε θ k ≤ (D.len P s u).toReal :=
      ENNReal.toReal_mono hlsu h1
    linarith
  · push Not at hex
    have : Icc (0 : ℝ) 1 ∩ P ⁻¹' determCube ε θ k = ∅ :=
      eq_empty_of_forall_notMem fun t ⟨ht, hPt⟩ => hex t ht (subset_closure hPt)
    rw [determPiece, this, measure_empty, ENNReal.toReal_zero]
    exact hrhs

end HigherDimLQGMetric
