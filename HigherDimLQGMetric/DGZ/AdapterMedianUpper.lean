import HigherDimLQGMetric.DGZ.AdapterBasics
import HigherDimLQGMetric.DGZ.FunctionalsLaw
import HigherDimLFPP.Exist.Lemma33

/-!
# Upper comparison for the real-scale whole-space median

The deterministic part of the adapter's median comparison, together with the lower-quantile
argument. All probabilistic inputs are the precise events supplied by the dyadic Hölder export
and the bounded upper-band supremum.
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

/-- The upper median bound for a coupled real band `G ε(s·) = H N + B`. -/
theorem adapter_median_upper_aux (hd : 0 < d) (hW : IsWhiteNoise P W)
    (hH : IsDyadicRealization κ P W' H) {ε s ξ β M L : ℝ} {N : ℕ}
    (hG : IsBandVersion P W κ ε 1 (G ε)) (hs : 1 / 2 < s) (hs1 : s ≤ 1)
    (hξ : 0 < ξ) (hβ : 0 < β) (hM : 0 ≤ M)
    (heq : ∀ z ω, G ε (s • z) ω = H N z ω + B z ω)
    (hBbad : P {ω | ∃ z ∈ cbox (0 : Rd d) 4, L < |B z ω|} ≤ 8⁻¹)
    (hHbad : P {ω | ∃ x ∈ obox (0 : Rd d) 3, ∃ y ∈ obox (0 : Rd d) 3,
      M * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
        lfppDistOn ξ (fun z => H N z ω) (obox 0 4) x y} ≤ 8⁻¹) :
    aHat P G ξ ε ≤ Real.exp (ξ * L) * M * (2 : ℝ) ^ β * aQ P H ξ N 2⁻¹ := by
  have hP := hW.isProbabilityMeasure
  have hs0 : 0 < s := by linarith
  let p : Rd d := s⁻¹ • e₁ d
  have hpNorm : ‖p‖ = s⁻¹ := by
    simp only [p, norm_smul, norm_e₁ hd, mul_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hs0)]
  have hpNorm2 : ‖p‖ < 2 := by
    rw [hpNorm]
    rw [← one_div]
    apply (div_lt_iff₀ hs0).2
    linarith
  have hp3 : p ∈ obox (0 : Rd d) 3 := by
    intro i
    simpa only [PiLp.zero_apply, sub_zero] using
      (HigherDimLFPP.DGZ.abs_apply_le_norm p i).trans_lt (by linarith : ‖p‖ < 3)
  have h03 : (0 : Rd d) ∈ obox (0 : Rd d) 3 := by
    intro i
    simp only [PiLp.zero_apply, sub_self, abs_zero]
    norm_num
  have h04 : (0 : Rd d) ∈ obox (0 : Rd d) 4 :=
    (cbox_subset_obox (by norm_num : (3 : ℝ) < 4))
      ((HigherDimLFPP.DGZ.obox_subset_cbox 0 3) h03)
  have hp4 : p ∈ obox (0 : Rd d) 4 :=
    (cbox_subset_obox (by norm_num : (3 : ℝ) < 4))
      ((HigherDimLFPP.DGZ.obox_subset_cbox 0 3) hp3)
  have hpow : ‖(0 : Rd d) - p‖ ^ β ≤ (2 : ℝ) ^ β := by
    rw [zero_sub, norm_neg]
    exact Real.rpow_le_rpow (norm_nonneg _) hpNorm2.le hβ.le
  let t : ℝ := Real.exp (ξ * L) * M * (2 : ℝ) ^ β * aQ P H ξ N 2⁻¹
  have haQpos : 0 < aQ P H ξ N 2⁻¹ := by
    unfold aQ
    exact (hH.band N).lowerQuantile_lfppDistance_pos hd hH.whiteNoise ξ
      (by norm_num) (by norm_num)
  have hgood : ∀ ω, (¬ ∃ z ∈ cbox (0 : Rd d) 4, L < |B z ω|) →
      (¬ ∃ x ∈ obox (0 : Rd d) 3, ∃ y ∈ obox (0 : Rd d) 3,
        M * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
          lfppDistOn ξ (fun z => H N z ω) (obox 0 4) x y) →
      lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) ≤ t := by
    intro ω hBg hHg
    have hBc : ∀ z ∈ obox (0 : Rd d) 4,
        |G ε (s • z) ω - H N z ω| ≤ L := by
      intro z hz
      rw [heq]
      have hzb : z ∈ cbox (0 : Rd d) 4 :=
        HigherDimLFPP.DGZ.obox_subset_cbox 0 4 hz
      simpa only [add_sub_cancel_left] using le_of_not_gt (fun h => hBg ⟨z, hzb, h⟩)
    have hXc : Continuous (fun z => G ε (s • z) ω) :=
      (hG.continuous ω).comp (continuous_id.const_smul s)
    have hcomp := lfppDistOn_le_exp_mul (ζ := ξ) (V := obox 0 4) (x := 0) (y := p)
      hXc ((hH.band N).continuous ω) hBc
    have hjoin : PcwJoined (obox (0 : Rd d) 4) 0 p :=
      PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 4) h04 hp4
    have hHbound : lfppDistOn ξ (fun z => H N z ω) (obox 0 4) 0 p ≤
        M * aQ P H ξ N 2⁻¹ * ‖(0 : Rd d) - p‖ ^ β :=
      le_of_not_gt (fun h => hHg ⟨0, h03, p, hp3, h⟩)
    have hscale : lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) =
        s * lfppMetric ξ (fun z => G ε (s • z) ω) 0 p := by
      have h := lfppMetric_sim (LinearIsometryEquiv.refl ℝ (Rd d)) 0 ξ
        (fun z => G ε z ω) hs0 0 p
      have hsp : s • p = e₁ d := by
        simp only [p, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
      simpa only [zero_add, smul_zero, LinearIsometryEquiv.coe_refl, id, hsp] using h
    rw [hscale]
    have hD : lfppMetric ξ (fun z => G ε (s • z) ω) 0 p ≤
        Real.exp (ξ * L) * (M * aQ P H ξ N 2⁻¹ * ‖(0 : Rd d) - p‖ ^ β) := by
      calc
        lfppMetric ξ (fun z => G ε (s • z) ω) 0 p
            ≤ lfppDistOn ξ (fun z => G ε (s • z) ω) (obox 0 4) 0 p :=
              lfppMetric_le_lfppDistOn hjoin
        _ ≤ Real.exp (|ξ| * L) * lfppDistOn ξ (fun z => H N z ω) (obox 0 4) 0 p :=
              hcomp
        _ ≤ Real.exp (ξ * L) * (M * aQ P H ξ N 2⁻¹ * ‖(0 : Rd d) - p‖ ^ β) := by
              rw [abs_of_pos hξ]
              exact mul_le_mul_of_nonneg_left hHbound (Real.exp_pos _).le
    have hD' : lfppMetric ξ (fun z => G ε (s • z) ω) 0 p ≤ t := by
      calc
        lfppMetric ξ (fun z => G ε (s • z) ω) 0 p
            ≤ Real.exp (ξ * L) * (M * aQ P H ξ N 2⁻¹ * ‖(0 : Rd d) - p‖ ^ β) := hD
        _ ≤ Real.exp (ξ * L) * (M * aQ P H ξ N 2⁻¹ * (2 : ℝ) ^ β) := by
              gcongr
        _ = t := by dsimp [t]; ring
    calc
      s * lfppMetric ξ (fun z => G ε (s • z) ω) 0 p ≤
          lfppMetric ξ (fun z => G ε (s • z) ω) 0 p :=
        mul_le_of_le_one_left (lfppMetric_nonneg ξ _ _ _) hs1
      _ ≤ t := hD'
  have hbad : P {ω | ¬ lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) ≤ t} ≤ 4⁻¹ := by
    have hsub : {ω | ¬ lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) ≤ t} ⊆
        {ω | ∃ z ∈ cbox (0 : Rd d) 4, L < |B z ω|} ∪
        {ω | ∃ x ∈ obox (0 : Rd d) 3, ∃ y ∈ obox (0 : Rd d) 3,
          M * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
            lfppDistOn ξ (fun z => H N z ω) (obox 0 4) x y} := by
      intro ω hω
      by_cases hBω : ∃ z ∈ cbox (0 : Rd d) 4, L < |B z ω|
      · exact Or.inl hBω
      · right
        by_contra hHω
        exact hω (hgood ω hBω hHω)
    calc
      P {ω | ¬ lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) ≤ t}
          ≤ P ({ω | ∃ z ∈ cbox (0 : Rd d) 4, L < |B z ω|} ∪
              {ω | ∃ x ∈ obox (0 : Rd d) 3, ∃ y ∈ obox (0 : Rd d) 3,
                M * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
                  lfppDistOn ξ (fun z => H N z ω) (obox 0 4) x y}) := measure_mono hsub
      _ ≤ 8⁻¹ + 8⁻¹ := (measure_union_le _ _).trans (add_le_add hBbad hHbad)
      _ = 4⁻¹ := by
        rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
          ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num
  have hhalf : (2⁻¹ : ℝ≥0∞) ≤
      P {ω | lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) ≤ t} :=
    adapter_half_le_measure_of_compl_le (P := P) hbad
  exact adapter_lowerMedian_le_of_half_le
    (measurable_lfppMetric hG.continuous hG.measurable ξ 0 (e₁ d)).aemeasurable hhalf

end HigherDimLQGMetric.DGZ
