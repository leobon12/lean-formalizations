import HigherDimLQGContinuity.ConvTransfer.Corr
import HigherDimLQGMetric.DGZ.AdapterMedianLower

/-!
# Deterministic point-distance comparisons for the real-cutoff model
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)
open HigherDimLQGMetric.DGZ

/-- A bounded field difference on the unit cube shell transfers a dyadic
crossing lower bound to the rescaled convolution point distance. -/
theorem convModel_point_lower_det {d : ℕ} (hd : 0 < d)
    {ξ r L : ℝ} (hr : 1 / 2 < r) (hr1 : r ≤ 1)
    {φ ψ : Rd d → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hB : ∀ z ∈ cbox (0 : Rd d) 1, |φ (r • z) - ψ z| ≤ L) :
    r * Real.exp (-(|ξ| * L)) * acrossDist ξ ψ 0 1 (1 / 2) ≤
      lfppMetric ξ φ 0 (e₁ d) := by
  have hr0 : 0 < r := by linarith
  let p : Rd d := r⁻¹ • e₁ d
  have hp0 : p ⟨0, hd⟩ = r⁻¹ := by
    simp only [p, PiLp.smul_apply, smul_eq_mul, e₁_ofLp]
    norm_num
  have hpout : p ∉ obox (0 : Rd d) 1 := by
    intro hp
    have h := hp ⟨0, hd⟩
    have hInv : 1 ≤ r⁻¹ := by
      rw [← one_div]
      exact (one_le_div hr0).2 hr1
    rw [hp0] at h
    simp only [PiLp.zero_apply, sub_zero, abs_of_pos (inv_pos.mpr hr0)] at h
    linarith
  have h0in : (0 : Rd d) ∈ cbox (0 : Rd d) (1 / 2) := by
    intro i
    simp only [PiLp.zero_apply, sub_self, abs_zero]
    norm_num
  have hscaledCont : Continuous fun z => φ (r • z) :=
    hφ.comp (continuous_id.const_smul r)
  have hcomp : acrossDist ξ ψ 0 1 (1 / 2) ≤
      Real.exp (|ξ| * L) * acrossDist ξ (fun z => φ (r • z)) 0 1 (1 / 2) := by
    exact acrossDist_le_exp_mul (ξ := ξ) (c := (0 : Rd d)) (r₁ := 1)
      (r₂ := (1 / 2 : ℝ)) hψ hscaledCont (by norm_num)
      (fun z hz => by
        have := hB z hz.1
        simpa only [abs_sub_comm] using this)
  have hcross : acrossDist ξ ψ 0 1 (1 / 2) ≤
      Real.exp (|ξ| * L) * lfppMetric ξ (fun z => φ (r • z)) 0 p :=
    hcomp.trans (mul_le_mul_of_nonneg_left
      (acrossDist_le_lfppMetric_of_mem hscaledCont (by norm_num) h0in hpout)
      (Real.exp_pos _).le)
  have hscaled : Real.exp (-(|ξ| * L)) * acrossDist ξ ψ 0 1 (1 / 2) ≤
      lfppMetric ξ (fun z => φ (r • z)) 0 p := by
    have h' : acrossDist ξ ψ 0 1 (1 / 2) ≤
        lfppMetric ξ (fun z => φ (r • z)) 0 p * Real.exp (|ξ| * L) := by
      simpa only [mul_comm] using hcross
    have := (div_le_iff₀ (Real.exp_pos (|ξ| * L))).2 h'
    rwa [div_eq_mul_inv, ← Real.exp_neg, mul_comm] at this
  have hscale : lfppMetric ξ φ 0 (e₁ d) =
      r * lfppMetric ξ (fun z => φ (r • z)) 0 p := by
    have h := lfppMetric_sim (LinearIsometryEquiv.refl ℝ (Rd d)) 0 ξ φ hr0 0 p
    have hsp : r • p = e₁ d := by
      simp only [p, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    simpa only [zero_add, smul_zero, LinearIsometryEquiv.coe_refl, id, hsp] using h
  rw [hscale]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscaled hr0.le

/-- A bounded field difference on the radius-four cube transfers a dyadic
confined point-distance upper bound to the convolution point distance. -/
theorem convModel_point_upper_det {d : ℕ} (hd : 0 < d)
    {ξ r L K : ℝ} (hr : 1 / 2 < r) (_hr1 : r ≤ 1)
    {φ ψ : Rd d → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hB : ∀ z ∈ cbox (0 : Rd d) 4, |φ (r • z) - ψ z| ≤ L)
    (hK : lfppDistOn ξ ψ (obox (0 : Rd d) 4) 0 (r⁻¹ • e₁ d) ≤ K) :
    lfppMetric ξ φ 0 (e₁ d) ≤ r * Real.exp (|ξ| * L) * K := by
  have hr0 : 0 < r := by linarith
  let p : Rd d := r⁻¹ • e₁ d
  have hpNorm : ‖p‖ = r⁻¹ := by
    simp only [p, norm_smul, norm_e₁ hd, mul_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr0)]
  have hpNorm2 : ‖p‖ < 2 := by
    rw [hpNorm, ← one_div]
    apply (div_lt_iff₀ hr0).2
    linarith
  have hp4 : p ∈ obox (0 : Rd d) 4 := by
    intro i
    simpa only [PiLp.zero_apply, sub_zero] using
      (HigherDimLFPP.DGZ.abs_apply_le_norm p i).trans_lt (by linarith : ‖p‖ < 4)
  have h04 : (0 : Rd d) ∈ obox (0 : Rd d) 4 := by
    intro i
    simp only [PiLp.zero_apply, sub_self, abs_zero]
    norm_num
  have hscaledCont : Continuous fun z => φ (r • z) :=
    hφ.comp (continuous_id.const_smul r)
  have hcmp : lfppDistOn ξ (fun z => φ (r • z)) (obox (0 : Rd d) 4) 0 p ≤
      Real.exp (|ξ| * L) * lfppDistOn ξ ψ (obox 0 4) 0 p := by
    exact lfppDistOn_le_exp_mul hscaledCont hψ
      (fun z hz => hB z (HigherDimLFPP.DGZ.obox_subset_cbox 0 4 hz))
  have hjoin : PcwJoined (obox (0 : Rd d) 4) 0 p :=
    PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 4) h04 hp4
  have hpoint : lfppMetric ξ (fun z => φ (r • z)) 0 p ≤
      Real.exp (|ξ| * L) * K := by
    calc
      lfppMetric ξ (fun z => φ (r • z)) 0 p ≤
          lfppDistOn ξ (fun z => φ (r • z)) (obox 0 4) 0 p :=
            lfppMetric_le_lfppDistOn hjoin
      _ ≤ Real.exp (|ξ| * L) * lfppDistOn ξ ψ (obox 0 4) 0 p := hcmp
      _ ≤ Real.exp (|ξ| * L) * K :=
        mul_le_mul_of_nonneg_left (by simpa only [p] using hK) (Real.exp_pos _).le
  have hscale : lfppMetric ξ φ 0 (e₁ d) =
      r * lfppMetric ξ (fun z => φ (r • z)) 0 p := by
    have h := lfppMetric_sim (LinearIsometryEquiv.refl ℝ (Rd d)) 0 ξ φ hr0 0 p
    have hsp : r • p = e₁ d := by
      simp only [p, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    simpa only [zero_add, smul_zero, LinearIsometryEquiv.coe_refl, id, hsp] using h
  rw [hscale]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpoint hr0.le

/-- The model correction bound covers the radius-four cube once its box
radius is chosen from the dimension. -/
theorem convModelGamma_cbox4_bound {d : ℕ} {Ω : Type*}
    {R r : ℝ} (hR : 0 ≤ R) (hS : 4 * √(d : ℝ) ≤ 2 * R + 12)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {T I : Rd d → Ω → ℝ} (hTc : ∀ ω, Continuous fun z => T z ω)
    (hIc : ∀ ω, Continuous fun z => I z ω) (m : Ω → ℝ)
    (ω : Ω) {z : Rd d} (hz : z ∈ cbox (0 : Rd d) 4) :
    |T z ω + I (r • z) ω - m ω| ≤ convModelGamma R T I m ω := by
  have hbox : z ∈ HigherDimLFPP.Osc.box (0 : Rd d) 4 := hz
  have hnorm : ‖z‖ ≤ √(d : ℝ) * 4 := by
    simpa only [sub_zero] using HigherDimLFPP.Osc.norm_sub_le_of_mem_box
      (by norm_num : (0 : ℝ) ≤ 4) hbox
  have hball : z ∈ Metric.closedBall (0 : Rd d) (2 * R + 12) := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    nlinarith
  exact convModelGamma_bound hR hr hr1 hTc hIc m ω hball

/-- Good dyadic crossing and Hölder events give two-sided point bounds after
the real-cutoff similarity. -/
theorem convModel_point_good_bounds {d : ℕ} (hd : 0 < d)
    {ξ b r L δ a M β : ℝ} (hξ : 0 < ξ) (hξb : ξ ≤ b)
    (hr : 1 / 2 < r) (hr1 : r ≤ 1) (hL : 0 ≤ L)
    (hδ : 0 < δ) (ha : 0 < a) (hM : 0 ≤ M) (hβ : 0 < β)
    {φ ψ : Rd d → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hCorr : ∀ z ∈ cbox (0 : Rd d) 4, |φ (r • z) - ψ z| ≤ L)
    (hN : δ * a < acrossDist ξ ψ 0 1 (1 / 2))
    (hHolder : ∀ x ∈ obox (0 : Rd d) 3, ∀ y ∈ obox (0 : Rd d) 3,
      lfppDistOn ξ ψ (obox (0 : Rd d) 4) x y ≤ M * a * ‖x - y‖ ^ β) :
    r * Real.exp (-(b * L)) * δ * a < lfppMetric ξ φ 0 (e₁ d) ∧
      lfppMetric ξ φ 0 (e₁ d) ≤
        r * Real.exp (b * L) * M * a * (2 : ℝ) ^ β := by
  have hr0 : 0 < r := by linarith
  let p : Rd d := r⁻¹ • e₁ d
  have hpNorm : ‖p‖ = r⁻¹ := by
    simp only [p, norm_smul, norm_e₁ hd, mul_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr0)]
  have hpNorm2 : ‖p‖ < 2 := by
    rw [hpNorm, ← one_div]
    apply (div_lt_iff₀ hr0).2
    linarith
  have hp3 : p ∈ obox (0 : Rd d) 3 := by
    intro i
    simpa only [PiLp.zero_apply, sub_zero] using
      (HigherDimLFPP.DGZ.abs_apply_le_norm p i).trans_lt (by linarith : ‖p‖ < 3)
  have h03 : (0 : Rd d) ∈ obox (0 : Rd d) 3 := by
    intro i
    simp only [PiLp.zero_apply, sub_self, abs_zero]
    norm_num
  have hK : lfppDistOn ξ ψ (obox (0 : Rd d) 4) 0 p ≤
      M * a * (2 : ℝ) ^ β := by
    have hpow : ‖(0 : Rd d) - p‖ ^ β ≤ (2 : ℝ) ^ β := by
      rw [zero_sub, norm_neg]
      exact Real.rpow_le_rpow (norm_nonneg _) hpNorm2.le hβ.le
    exact (hHolder 0 h03 p hp3).trans
      (mul_le_mul_of_nonneg_left hpow (mul_nonneg hM ha.le))
  have hcross : r * Real.exp (-(ξ * L)) * acrossDist ξ ψ 0 1 (1 / 2) ≤
      lfppMetric ξ φ 0 (e₁ d) := by
    simpa only [abs_of_pos hξ] using
      (convModel_point_lower_det hd hr hr1 hφ hψ
        (fun z hz => hCorr z (fun i => (hz i).trans (by norm_num))) :
        r * Real.exp (-(|ξ| * L)) * acrossDist ξ ψ 0 1 (1 / 2) ≤
          lfppMetric ξ φ 0 (e₁ d))
  have hpoint : lfppMetric ξ φ 0 (e₁ d) ≤
      r * Real.exp (|ξ| * L) * (M * a * (2 : ℝ) ^ β) :=
    convModel_point_upper_det hd hr hr1 hφ hψ hCorr hK
  have hElo : Real.exp (-(b * L)) ≤ Real.exp (-(ξ * L)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.2 hξb) hL])
  have hEhi : Real.exp (|ξ| * L) ≤ Real.exp (b * L) := by
    rw [abs_of_pos hξ]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hξb hL)
  constructor
  · have hδa : 0 < δ * a := mul_pos hδ ha
    calc
      r * Real.exp (-(b * L)) * δ * a ≤
          r * Real.exp (-(ξ * L)) * δ * a := by gcongr
      _ < r * Real.exp (-(ξ * L)) * acrossDist ξ ψ 0 1 (1 / 2) := by
        simpa only [mul_assoc] using
          (mul_lt_mul_of_pos_left hN (mul_pos hr0 (Real.exp_pos (-(ξ * L)))))
      _ ≤ lfppMetric ξ φ 0 (e₁ d) := hcross
  · calc
      lfppMetric ξ φ 0 (e₁ d) ≤
          r * Real.exp (|ξ| * L) * (M * a * (2 : ℝ) ^ β) := hpoint
      _ ≤ r * Real.exp (b * L) * (M * a * (2 : ℝ) ^ β) := by
        gcongr
      _ = r * Real.exp (b * L) * M * a * (2 : ℝ) ^ β := by ring

end HigherDimLQGContinuity
