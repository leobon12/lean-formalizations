import HigherDimLQGMetric.DGZ.AdapterMedianUpper
import HigherDimLQGMetric.DGZ.Crossing

/-!
# Lower comparison for the real-scale whole-space median

A path from `0` to the rescaled point `s⁻¹ e₁` crosses the fixed `ℓ^∞` shell. Its crossing
distance is stable under the bounded upper band, giving the lower median comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W W' : WN d → Ω → ℝ} {κ : Rd d → ℝ} {G : ℝ → Rd d → Ω → ℝ}
  {H : ℕ → Rd d → Ω → ℝ} {B : Rd d → Ω → ℝ}

/-- The lower median bound for a coupled real band `G ε(s·) = H N + B`. -/
theorem adapter_median_lower_aux (hd : 0 < d) (hW : IsWhiteNoise P W)
    (hH : IsDyadicRealization κ P W' H) {ε s ξ δ L : ℝ} {N : ℕ}
    (hG : IsBandVersion P W κ ε 1 (G ε)) (hs : 1 / 2 < s) (hs1 : s ≤ 1)
    (hξ : 0 < ξ) (hδ : 0 < δ)
    (heq : ∀ z ω, G ε (s • z) ω = H N z ω + B z ω)
    (hBbad : P {ω | ∃ z ∈ cbox (0 : Rd d) 1, L < |B z ω|} ≤ 8⁻¹)
    (hNbad : P {ω | acrossDist ξ (fun z => H N z ω) 0 1 (1 / 2) ≤
      δ * aQ P H ξ N 2⁻¹} ≤ 8⁻¹) :
    (1 / 2 : ℝ) * Real.exp (-(ξ * L)) * δ * aQ P H ξ N 2⁻¹ < aHat P G ξ ε := by
  have hP := hW.isProbabilityMeasure
  have hs0 : 0 < s := by linarith
  let p : Rd d := s⁻¹ • e₁ d
  have hp0 : p ⟨0, hd⟩ = s⁻¹ := by
    simp only [p, PiLp.smul_apply, smul_eq_mul, e₁_ofLp]
    norm_num
  have hpout : p ∉ obox (0 : Rd d) 1 := by
    intro hp
    have h := hp ⟨0, hd⟩
    have hInv : 1 ≤ s⁻¹ := by
      rw [← one_div]
      exact (one_le_div hs0).2 hs1
    rw [hp0] at h
    simp only [PiLp.zero_apply, sub_zero, abs_of_pos (inv_pos.mpr hs0)] at h
    linarith
  have h0in : (0 : Rd d) ∈ cbox (0 : Rd d) (1 / 2) := by
    intro i
    simp only [PiLp.zero_apply, sub_self, abs_zero]
    norm_num
  let t : ℝ := (1 / 2 : ℝ) * Real.exp (-(ξ * L)) * δ * aQ P H ξ N 2⁻¹
  have haQpos : 0 < aQ P H ξ N 2⁻¹ := by
    unfold aQ
    exact (hH.band N).lowerQuantile_lfppDistance_pos hd hH.whiteNoise ξ
      (by norm_num) (by norm_num)
  have hgood : ∀ ω, (¬ ∃ z ∈ cbox (0 : Rd d) 1, L < |B z ω|) →
      ¬ acrossDist ξ (fun z => H N z ω) 0 1 (1 / 2) ≤ δ * aQ P H ξ N 2⁻¹ →
      t < lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) := by
    intro ω hBg hNg
    have hBc : ∀ z ∈ cbox (0 : Rd d) 1 \ obox 0 (1 / 2),
        |H N z ω - G ε (s • z) ω| ≤ L := by
      intro z hz
      rw [heq]
      have h := le_of_not_gt (fun h => hBg ⟨z, hz.1, h⟩)
      simpa only [sub_add_cancel_left, abs_neg] using h
    have hXc : Continuous (fun z => G ε (s • z) ω) :=
      (hG.continuous ω).comp (continuous_id.const_smul s)
    have hcomp : acrossDist ξ (fun z => H N z ω) 0 1 (1 / 2) ≤
        Real.exp (ξ * L) * acrossDist ξ (fun z => G ε (s • z) ω) 0 1 (1 / 2) := by
      have h := acrossDist_le_exp_mul (ξ := ξ) (c := (0 : Rd d)) (r₁ := 1)
        (r₂ := (1 / 2 : ℝ)) ((hH.band N).continuous ω) hXc (by norm_num) hBc
      rwa [abs_of_pos hξ] at h
    have hcross : δ * aQ P H ξ N 2⁻¹ <
        Real.exp (ξ * L) * lfppMetric ξ (fun z => G ε (s • z) ω) 0 p := by
      exact lt_of_lt_of_le (lt_of_not_ge hNg)
        (hcomp.trans (mul_le_mul_of_nonneg_left
          (acrossDist_le_lfppMetric_of_mem hXc (by norm_num) h0in hpout)
          (Real.exp_pos _).le))
    have hscaled : Real.exp (-(ξ * L)) * (δ * aQ P H ξ N 2⁻¹) <
        lfppMetric ξ (fun z => G ε (s • z) ω) 0 p := by
      have hcross' : δ * aQ P H ξ N 2⁻¹ <
          lfppMetric ξ (fun z => G ε (s • z) ω) 0 p * Real.exp (ξ * L) := by
        simpa only [mul_comm] using hcross
      have h := (div_lt_iff₀ (Real.exp_pos (ξ * L))).2 hcross'
      rwa [div_eq_mul_inv, ← Real.exp_neg, mul_comm] at h
    have hscale : lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) =
        s * lfppMetric ξ (fun z => G ε (s • z) ω) 0 p := by
      have h := lfppMetric_sim (LinearIsometryEquiv.refl ℝ (Rd d)) 0 ξ
        (fun z => G ε z ω) hs0 0 p
      have hsp : s • p = e₁ d := by
        simp only [p, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
      simpa only [zero_add, smul_zero, LinearIsometryEquiv.coe_refl, id, hsp] using h
    rw [hscale]
    have hpos : 0 < Real.exp (-(ξ * L)) * (δ * aQ P H ξ N 2⁻¹) := by
      positivity
    calc
      t = (1 / 2 : ℝ) * (Real.exp (-(ξ * L)) * (δ * aQ P H ξ N 2⁻¹)) := by
        dsimp [t]
        ring
      _ < s * (Real.exp (-(ξ * L)) * (δ * aQ P H ξ N 2⁻¹)) :=
        mul_lt_mul_of_pos_right hs hpos
      _ ≤ s * lfppMetric ξ (fun z => G ε (s • z) ω) 0 p :=
        mul_le_mul_of_nonneg_left hscaled.le hs0.le
  have hbad : P {ω | lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) ≤ t} ≤ 4⁻¹ := by
    have hsub : {ω | lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) ≤ t} ⊆
        {ω | ∃ z ∈ cbox (0 : Rd d) 1, L < |B z ω|} ∪
        {ω | acrossDist ξ (fun z => H N z ω) 0 1 (1 / 2) ≤
          δ * aQ P H ξ N 2⁻¹} := by
      intro ω hω
      by_cases hBω : ∃ z ∈ cbox (0 : Rd d) 1, L < |B z ω|
      · exact Or.inl hBω
      · right
        by_contra hNω
        exact (not_le_of_gt (hgood ω hBω hNω)) hω
    calc
      P {ω | lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) ≤ t}
          ≤ P ({ω | ∃ z ∈ cbox (0 : Rd d) 1, L < |B z ω|} ∪
              {ω | acrossDist ξ (fun z => H N z ω) 0 1 (1 / 2) ≤
                δ * aQ P H ξ N 2⁻¹}) := measure_mono hsub
      _ ≤ 8⁻¹ + 8⁻¹ := (measure_union_le _ _).trans (add_le_add hBbad hNbad)
      _ = 4⁻¹ := by
        rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
          ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num
  have hhalf : P {ω | lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) ≤ t} <
      (2⁻¹ : ℝ≥0∞) := hbad.trans_lt (by norm_num)
  exact adapter_lt_lowerMedian_of_measure_lt
    (measurable_lfppMetric hG.continuous hG.measurable ξ 0 (e₁ d)).aemeasurable hhalf

end HigherDimLQGMetric.DGZ
