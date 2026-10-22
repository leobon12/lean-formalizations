import HigherDimLQGMetric.DGZ.AdapterMedianLower

/-!
# Uniform inputs for the real-scale adapter

The dyadic Hölder shape is specialized to fixed nested boxes. Constants are enlarged to be
positive, which makes their later multiplicative use stable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (obox)

variable {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}

/-- The dyadic Hölder estimate on the nested boxes used to compare medians. -/
theorem adapter_holder_box3 (h : DGZHyp d κ ξ Q) (hHolder : HolderTightShape d κ ξ Q)
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d))) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ N : ℕ,
          P {ω | ∃ x ∈ obox (0 : Rd d) 3, ∃ y ∈ obox (0 : Rd d) 3,
              M * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
                lfppDistOn ξ (fun z => H N z ω) (obox 0 4) x y} ≤ 8⁻¹ := by
  obtain ⟨M₀, hM₀⟩ := hHolder h β hβ0 hβ (obox 0 4) (obox 0 3)
    (HigherDimLFPP.DGZ.isOpen_obox 0 4) (HigherDimLFPP.DGZ.isOpen_obox 0 3)
    ((HigherDimLFPP.DGZ.convex_obox 0 3).isConnected
      ⟨0, fun i => by simp only [PiLp.zero_apply, sub_self, abs_zero]; norm_num⟩)
    (isBounded_obox 0 3)
    (adapter_closure_obox_subset (by norm_num : (3 : ℝ) < 4)) (8⁻¹ : ℝ)
    (by norm_num : (0 : ℝ) < 8⁻¹)
  refine ⟨max 1 M₀, le_max_left _ _, ?_⟩
  intro Ω _ P W H hH N
  have hd0 : 0 < d := by have := h.dim; omega
  have hq : 0 ≤ aQ P H ξ N 2⁻¹ := by
    unfold aQ
    exact ((hH.band N).lowerQuantile_lfppDistance_pos hd0
      hH.whiteNoise ξ (by norm_num) (by norm_num)).le
  have hsub : {ω | ∃ x ∈ obox (0 : Rd d) 3, ∃ y ∈ obox (0 : Rd d) 3,
      max 1 M₀ * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
        lfppDistOn ξ (fun z => H N z ω) (obox 0 4) x y} ⊆
      {ω | ∃ x ∈ obox (0 : Rd d) 3, ∃ y ∈ obox (0 : Rd d) 3,
        M₀ * aQ P H ξ N 2⁻¹ * ‖x - y‖ ^ β <
          lfppDistOn ξ (fun z => H N z ω) (obox 0 4) x y} := by
    rintro ω ⟨x, hx, y, hy, hxy⟩
    refine ⟨x, hx, y, hy, lt_of_le_of_lt ?_ hxy⟩
    have hpow : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 M₀) hq) hpow
  refine (measure_mono hsub).trans ?_
  simpa only [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
    ENNReal.ofReal_ofNat] using hM₀ (Ω := Ω) P W H hH N

/-- The fixed shell lower-tail estimate used in the lower median comparison. -/
theorem adapter_nondeg_box1 (h : DGZHyp d κ ξ Q) (hNondeg : NondegShape d κ ξ Q) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ,
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ N : ℕ, N₀ ≤ N →
          P {ω | acrossDist ξ (fun z => H N z ω) 0 1 (1 / 2) ≤
            δ * aQ P H ξ N 2⁻¹} ≤ 8⁻¹ := by
  obtain ⟨δ, hδ, N₀, hN₀⟩ := hNondeg h 0 1 (1 / 2) (by norm_num) (by norm_num)
    (8⁻¹ : ℝ) (by norm_num)
  refine ⟨δ, hδ, N₀, ?_⟩
  intro Ω _ P W H hH N hN
  simpa only [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
    ENNReal.ofReal_ofNat] using hN₀ (Ω := Ω) P W H hH N hN

/-- Uniform comparison of the whole-space real-scale median to the dyadic internal median,
in any pointwise coupling produced by `adapter_realScale_coupling`. -/
theorem adapter_median_bounds_coupled (h : DGZHyp d κ ξ Q)
    (hHolder : HolderTightShape d κ ξ Q) (hNondeg : NondegShape d κ ξ Q)
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d))) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ M : ℝ, 1 ≤ M ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ,
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W W' : WN d → Ω → ℝ}
        {G : ℝ → Rd d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ} {B : Rd d → Ω → ℝ}
        {ε s : ℝ} {N : ℕ},
        IsWhiteNoise P W → IsBandVersion P W κ ε 1 (G ε) →
        IsDyadicRealization κ P W' H → IsBandVersion P W' κ 1 (1 / s) B →
        1 / 2 < s → s ≤ 1 → N₀ ≤ N →
        (∀ z ω, G ε (s • z) ω = H N z ω + B z ω) →
        (1 / 2 : ℝ) * Real.exp (-(ξ * L)) * δ * aQ P H ξ N 2⁻¹ < aHat P G ξ ε ∧
          aHat P G ξ ε ≤ Real.exp (ξ * L) * M * (2 : ℝ) ^ β * aQ P H ξ N 2⁻¹ := by
  have hd0 : 0 < d := by have := h.dim; omega
  obtain ⟨L, hL, hLB⟩ := adapter_exists_upperBand_sup_bound hd0 h.kernel
    (R := 4) (θ := 8⁻¹) (by norm_num) (by norm_num)
  obtain ⟨M, hM, hMH⟩ := adapter_holder_box3 h hHolder hβ0 hβ
  obtain ⟨δ, hδ, N₀, hN⟩ := adapter_nondeg_box1 h hNondeg
  refine ⟨L, hL, M, hM, δ, hδ, N₀, ?_⟩
  intro Ω _ P W W' G H B ε s N hW hG hH hB hs hs1 hN₀ heq
  have hs0 : 0 < s := by linarith
  have hb1 : 1 ≤ 1 / s := (one_le_div hs0).2 hs1
  have hb2 : 1 / s ≤ 2 := (div_le_iff₀ hs0).2 (by linarith)
  have hB4 : P {ω | ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) 4,
      L < |B z ω|} ≤ 8⁻¹ := by
    have h := hLB hH.whiteNoise hb1 hb2 hB
    simpa only [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
      ENNReal.ofReal_ofNat] using h
  have hB1 : P {ω | ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) 1,
      L < |B z ω|} ≤ 8⁻¹ := by
    refine (measure_mono ?_).trans hB4
    rintro ω ⟨z, hz, hzt⟩
    exact ⟨z, fun i => (hz i).trans (by norm_num), hzt⟩
  constructor
  · exact adapter_median_lower_aux hd0 hW hH hG hs hs1 h.xi_pos hδ heq hB1
      (hN hH N hN₀)
  · exact adapter_median_upper_aux hd0 hW hH hG hs hs1 h.xi_pos hβ0 (by linarith)
      heq hB4 (hMH hH N)

end HigherDimLQGMetric.DGZ
