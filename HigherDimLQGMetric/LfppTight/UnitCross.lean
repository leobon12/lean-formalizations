import HigherDimLQGMetric.Events.TightCore
import HigherDimLQGMetric.B3.Interfaces

/-! A8 at unit scale from tightness and positivity of the limiting metrics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_tightFamily_to_tightOver {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ → Ω → C(Rd d × Rd d, ℝ)} {S : Set ℝ}
    (hT : TightFamily P X S) : TightOver P X S := by
  refine ⟨hT.1, hT.2.1, ?_⟩
  intro μ hμ
  filter_upwards [hT.2.2 μ hμ] with D hD
  exact hD.1

theorem l6a_unitCross_of_tightOver {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ → Ω → C(Rd d × Rd d, ℝ)} {S : Set ℝ}
    (hT : TightOver P X S) {p C : ℝ} (hp : p < 1) (hC : 0 < C) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 4 ∧ ∀ ε ∈ S,
      ENNReal.ofReal p ≤ P {ω |
        supPairs (X ε ω) (ball (0 : Rd d) b) ≤
          ENNReal.ofReal C⁻¹ *
            infPairs (X ε ω) (sphere (0 : Rd d) b) (sphere 0 1)} := by
  by_cases hp0 : p ≤ 0
  · refine ⟨1 / 4, by norm_num, le_rfl, fun ε hε => ?_⟩
    simp only [ENNReal.ofReal_eq_zero.mpr hp0]
    exact bot_le
  have hp0' : 0 < p := lt_of_not_ge hp0
  let q : ℝ := (1 - p) / 4
  have hq : 0 < q := by dsimp [q]; linarith
  let K : Set (Rd d × Rd d) :=
    closedBall (0 : Rd d) (1 / 2) ×ˢ sphere (0 : Rd d) 1
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKd : ∀ z ∈ K, z.1 ≠ z.2 := by
    intro z hz he
    have h1 : ‖z.1‖ ≤ 1 / 2 := by
      simpa only [mem_closedBall, dist_zero_right] using hz.1
    have h2 : ‖z.2‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hz.2
    rw [he] at h1
    linarith
  obtain ⟨a, ha, hlow⟩ := tightLowerOffDiag hT hK hKd
    (show (0 : ℝ≥0∞) < ENNReal.ofReal q by simp [hq])
  obtain ⟨δ, hδ, hmod⟩ := tightModulus hT
    (isCompact_closedBall (0 : Rd d) (1 / 2))
    (show 0 < a / (2 * C) by positivity)
    (show (0 : ℝ≥0∞) < ENNReal.ofReal q by simp [hq])
  let b : ℝ := min (δ / 2) (1 / 4)
  have hb : 0 < b := by dsimp [b]; positivity
  have hb4 : b ≤ 1 / 4 := min_le_right _ _
  have hbδ : 2 * b ≤ δ := by
    dsimp [b]
    have := min_le_left (δ / 2) (1 / 4)
    linarith
  refine ⟨b, hb, hb4, ?_⟩
  intro ε hε
  let B₁ : Set Ω := {ω | ¬ ∀ z ∈ K, a < X ε ω z}
  let B₂ : Set Ω := {ω | ¬ ∀ u ∈ closedBall (0 : Rd d) (1 / 2),
    ∀ v ∈ closedBall (0 : Rd d) (1 / 2),
      ‖u - v‖ ≤ δ → X ε ω (u, v) < a / (2 * C)}
  let E : Set Ω := {ω | supPairs (X ε ω) (ball (0 : Rd d) b) ≤
    ENNReal.ofReal C⁻¹ *
      infPairs (X ε ω) (sphere (0 : Rd d) b) (sphere 0 1)}
  have hgood : (B₁ ∪ B₂)ᶜ ⊆ E := by
    intro ω hω
    have h₁ : ∀ z ∈ K, a < X ε ω z := by
      intro z hz
      by_contra hn
      exact hω (Or.inl (fun hp => hn (hp z hz)))
    have h₂ : ∀ u ∈ closedBall (0 : Rd d) (1 / 2),
        ∀ v ∈ closedBall (0 : Rd d) (1 / 2),
          ‖u - v‖ ≤ δ → X ε ω (u, v) < a / (2 * C) := by
      intro u hu v hv huv
      by_contra hn
      exact hω (Or.inr (fun hp => hn (hp u hu v hv huv)))
    have hupper : supPairs (X ε ω) (ball (0 : Rd d) b) ≤
        ENNReal.ofReal (a / (2 * C)) := by
      unfold supPairs
      apply iSup_le
      intro u
      apply iSup_le
      intro hu
      apply iSup_le
      intro v
      apply iSup_le
      intro hv
      have hu' : u ∈ closedBall (0 : Rd d) (1 / 2) := by
        apply mem_closedBall.mpr
        have := mem_ball.mp hu
        linarith [hb4]
      have hv' : v ∈ closedBall (0 : Rd d) (1 / 2) := by
        apply mem_closedBall.mpr
        have := mem_ball.mp hv
        linarith [hb4]
      have huv : ‖u - v‖ ≤ δ := by
        calc
          ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le u v
          _ ≤ 2 * b := by
            have hu'' : ‖u‖ < b := by simpa only [mem_ball, dist_zero_right] using hu
            have hv'' : ‖v‖ < b := by simpa only [mem_ball, dist_zero_right] using hv
            linarith
          _ ≤ δ := hbδ
      exact ENNReal.ofReal_le_ofReal (h₂ u hu' v hv' huv).le
    have hlower : ENNReal.ofReal a ≤
        infPairs (X ε ω) (sphere (0 : Rd d) b) (sphere 0 1) := by
      unfold infPairs
      apply le_iInf
      intro u
      apply le_iInf
      intro hu
      apply le_iInf
      intro v
      apply le_iInf
      intro hv
      have hu' : u ∈ closedBall (0 : Rd d) (1 / 2) := by
        apply mem_closedBall.mpr
        have : ‖u‖ = b := by simpa only [mem_sphere, dist_zero_right] using hu
        simpa only [dist_zero_right, this] using le_trans hb4 (by norm_num)
      exact ENNReal.ofReal_le_ofReal (h₁ (u, v) ⟨hu', hv⟩).le
    calc
      supPairs (X ε ω) (ball (0 : Rd d) b) ≤
          ENNReal.ofReal (a / (2 * C)) := hupper
      _ ≤ ENNReal.ofReal C⁻¹ * ENNReal.ofReal a := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C⁻¹)]
        apply ENNReal.ofReal_le_ofReal
        have : C⁻¹ * a = a / C := by ring
        rw [this]
        rw [div_le_div_iff₀ (mul_pos (by norm_num) hC) hC]
        nlinarith [ha, hC]
      _ ≤ ENNReal.ofReal C⁻¹ *
          infPairs (X ε ω) (sphere (0 : Rd d) b) (sphere 0 1) := by gcongr
  have hbad : P (B₁ ∪ B₂) ≤ ENNReal.ofReal q + ENNReal.ofReal q :=
    (measure_union_le _ _).trans (add_le_add (hlow ε hε).le (hmod ε hε).le)
  have hcover : (B₁ ∪ B₂)ᶜ ∪ (B₁ ∪ B₂) = (univ : Set Ω) := compl_union_self _
  have hsum : (1 : ℝ≥0∞) ≤ P E + ENNReal.ofReal q + ENNReal.ofReal q := by
    calc
      (1 : ℝ≥0∞) = P ((B₁ ∪ B₂)ᶜ ∪ (B₁ ∪ B₂)) := by rw [hcover, measure_univ]
      _ ≤ P (B₁ ∪ B₂)ᶜ + P (B₁ ∪ B₂) := measure_union_le _ _
      _ ≤ P E + (ENNReal.ofReal q + ENNReal.ofReal q) := by gcongr
      _ = _ := by ac_rfl
  have hqsum : ENNReal.ofReal p + ENNReal.ofReal q + ENNReal.ofReal q ≤ 1 := by
    rw [← ENNReal.ofReal_add hp0'.le hq.le,
      ← ENNReal.ofReal_add (add_nonneg hp0'.le hq.le) hq.le,
      ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    dsimp [q]
    linarith
  exact (ENNReal.add_le_add_iff_right (show
    ENNReal.ofReal q + ENNReal.ofReal q ≠ ⊤ by simp)).mp
      (show ENNReal.ofReal p + (ENNReal.ofReal q + ENNReal.ofReal q) ≤
        P E + (ENNReal.ofReal q + ENNReal.ofReal q) by
        calc
          _ = ENNReal.ofReal p + ENNReal.ofReal q + ENNReal.ofReal q := by ac_rfl
          _ ≤ 1 := hqsum
          _ ≤ P E + ENNReal.ofReal q + ENNReal.ofReal q := hsum
          _ = _ := by ac_rfl)

end HigherDimLQGMetric
