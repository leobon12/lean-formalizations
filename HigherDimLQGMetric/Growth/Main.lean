import HigherDimLQGMetric.Growth.Compact

/-!
# Growth of sphere averages

Packet L2a. This is the exact MA5 Details (c) proposition for Lemma 2.13, including
the cited thick-point input I8. Lemma 2.14 is in LargeLimit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- **L2a** (= [1] Lemma 2.13, including thick-point bound I8):
logarithmic growth at small radii and subpower growth at large radii. -/
def L2a_sphereAvgGrowth : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ R ζ : ℝ, 0 < R → 0 < ζ →
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : Rd d) R, ∀ r : ℝ, 0 < r →
      |sphereAvg (h ω) r z| ≤
        C * max (Real.log r⁻¹) (max ((max (Real.log r) 0) ^ (1 / 2 + ζ)) 1)

/-- The exact MA5 surface, proved from the small-radius grid bound, Lemma 2.14,
and continuity on the remaining compact interval. -/
theorem l2a_sphereAvgGrowth : L2a_sphereAvgGrowth := by
  intro d hd Ω _ P _ h hh R ζ hR hζ
  obtain ⟨A, hA, hsmall⟩ := l2a_small_radius_log_bound hd hh hR
  have hlarge := l2a_large_radius_littleO hd hh hR hζ
  have hcont := hh.1.ae_continuousOn_sphereAvg hd
  filter_upwards [hsmall, hlarge, hcont] with ω hsmall hlarge hcont
  obtain ⟨r₀, hr₀, hsmall⟩ := hsmall
  have hnear : ∀ᶠ r : ℝ in atTop,
      (⨆ z : closedBall (0 : Rd d) R, |sphereAvg (h ω) r z|) /
        Real.log r ^ (1 / 2 + ζ) < 1 :=
    (tendsto_order.1 hlarge).2 1 one_pos
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 hnear
  set b : ℝ := max R₁ (max 2 r₀) with hb
  have hr₀b : r₀ ≤ b := (le_max_right 2 r₀).trans (le_max_right R₁ _)
  have hb₂ : 2 ≤ b := (le_max_left 2 r₀).trans (le_max_right R₁ _)
  obtain ⟨M, hM, hmid⟩ := l2a_compact_sphereAvg_bound (h ω) hcont.2 hr₀ hr₀b hR.le
  set C : ℝ := A + M + 1 with hC
  have hCA : A ≤ C := by dsimp [C]; linarith
  have hCM : M ≤ C := by dsimp [C]; linarith
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, fun z hz r hr => ?_⟩
  let W : ℝ := max (Real.log r⁻¹)
    (max ((max (Real.log r) 0) ^ (1 / 2 + ζ)) 1)
  have hW1 : 1 ≤ W := (le_max_right _ _).trans (le_max_right _ _)
  have hW0 : 0 ≤ W := by linarith
  have hWinv : Real.log r⁻¹ ≤ W := le_max_left _ _
  have hWpow : (max (Real.log r) 0) ^ (1 / 2 + ζ) ≤ W :=
    (le_max_left _ _).trans (le_max_right _ _)
  change |sphereAvg (h ω) r z| ≤ C * W
  by_cases hsr : r ≤ r₀
  · have hs := hsmall r hr hsr z hz
    calc |sphereAvg (h ω) r z| ≤ A * Real.log r⁻¹ := hs
      _ ≤ A * W := mul_le_mul_of_nonneg_left hWinv hA.le
      _ ≤ C * W := mul_le_mul_of_nonneg_right hCA hW0
  by_cases hmr : r ≤ b
  · have hm := hmid r (le_of_not_ge hsr) hmr z hz
    calc |sphereAvg (h ω) r z| ≤ M := hm
      _ ≤ M * W := by nlinarith [hW1, hM]
      _ ≤ C * W := mul_le_mul_of_nonneg_right hCM hW0
  have hrb : b < r := lt_of_not_ge hmr
  have hr₂ : 2 < r := hb₂.trans_lt hrb
  have hlog : 0 < Real.log r := Real.log_pos (by linarith)
  have hden : 0 < Real.log r ^ (1 / 2 + ζ) := Real.rpow_pos_of_pos hlog _
  have hq := hR₁ r (le_trans (le_max_left _ _) hrb.le)
  have hsup : (⨆ z : closedBall (0 : Rd d) R, |sphereAvg (h ω) r z|) ≤
      Real.log r ^ (1 / 2 + ζ) := (div_lt_one hden).1 hq |>.le
  have hp := l2a_sphereAvg_le_iSup (h ω) hcont.2 hr hz
  have hpow : Real.log r ^ (1 / 2 + ζ) =
      (max (Real.log r) 0) ^ (1 / 2 + ζ) := by rw [max_eq_left hlog.le]
  calc |sphereAvg (h ω) r z|
      ≤ ⨆ z : closedBall (0 : Rd d) R, |sphereAvg (h ω) r z| := hp
    _ ≤ Real.log r ^ (1 / 2 + ζ) := hsup
    _ ≤ W := hpow ▸ hWpow
    _ ≤ C * W := by nlinarith [hC1, hW0]

end HigherDimLQGMetric
