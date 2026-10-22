import HigherDimLQGContinuity.ConvTransfer.LowerDet

/-! Model crossing bound after the real-cutoff field decomposition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (cbox obox)
open HigherDimLQGMetric.DGZ

/-- A fixed box containing every shell of the finite cover also lies in the
box controlled by `convModelGamma`. -/
theorem convCross_shell_mem_gamma_box {d : ℕ} {c v w : Rd d}
    {a ρ R : ℝ} (ha : 0 < a) (hρ : 0 < ρ)
    (hY : v ∈ closedBall (0 : Rd d) (2 * (‖c‖ + a)))
    (hR : R = 2 * (‖c‖ + a) + Real.sqrt d * (2 * ρ + 1) + 1)
    (hw : w ∈ cbox v (2 * ρ)) :
    w ∈ closedBall (0 : Rd d) (2 * R + 12) := by
  have hwo : w ∈ obox v (2 * ρ + 1) :=
    cbox_subset_obox (by linarith) hw
  have hwv : ‖w - v‖ ≤ Real.sqrt d * (2 * ρ + 1) := by
    simpa only [norm_sub_rev] using (tn_norm_sub_le hwo)
  have hv : ‖v‖ ≤ 2 * (‖c‖ + a) := by
    simpa only [mem_closedBall, dist_zero_right] using hY
  have ht := norm_add_le (w-v) v
  rw [sub_add_cancel] at ht
  change dist w 0 ≤ 2 * R + 12
  rw [dist_zero_right]
  rw [hR]
  have hbase : 0 ≤ 2 * (‖c‖ + a) := by positivity
  have hprod : 0 ≤ Real.sqrt d * (2 * ρ + 1) := by positivity
  linarith

/-- Pointwise lower bound for the centered convolution field crossing in its
white-noise model. -/
theorem convCross_model_infPairs_lower {d : ℕ} {κ : Rd d → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : HigherDimLFPP.WN d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H)
    (N : ℕ) {T I Φ : Rd d → Ω → ℝ} (m : Ω → ℝ)
    (hTc : ∀ ω, Continuous fun z => T z ω)
    (hIc : ∀ ω, Continuous fun z => I z ω)
    (hΦc : ∀ ω, Continuous fun z => Φ z ω)
    {r ξ b a c' ρ R : ℝ} {c : Rd d}
    (hr : 1 / 2 < r) (hr1 : r ≤ 1)
    (hξ : 0 < ξ) (hξb : ξ ≤ b)
    (ha : 0 < a) (hac : a < c')
    (hρ : ρ = (c' - a) / (8 * (Real.sqrt d + 1)))
    (hR : R = 2 * (‖c‖ + a) + Real.sqrt d * (2 * ρ + 1) + 1)
    (hΦeq : ∀ z ω, Φ (r • z) ω = H N z ω + T z ω - m ω + I (r • z) ω)
    (Y : Finset (Rd d)) (hYne : Y.Nonempty)
    (hY : ∀ v ∈ Y, v ∈ closedBall (0 : Rd d) (2 * (‖c‖ + a)))
    (hcover : ∀ {s : ℝ}, 1 / 2 < s → ∀ {x : Rd d}, x ∈ sphere c a →
      ∃ v ∈ Y, s⁻¹ • x ∈ obox v ρ)
    (ω : Ω) :
    ENNReal.ofReal (r * Real.exp (-(b * convModelGamma R T I m ω)) *
      Y.inf' hYne (fun v => acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ)) ≤
      infPairs (fun p : Rd d × Rd d => lfppMetric ξ (fun z => Φ z ω) p.1 p.2)
        (sphere c a) (sphere c c') := by
  have hr0 : 0 < r := by linarith
  have hρ0 : 0 < ρ := by rw [hρ]; exact div_pos (by linarith) (by positivity)
  have hΓ0 : 0 ≤ convModelGamma R T I m ω := by
    have hR0 : 0 ≤ R := by rw [hR]; positivity
    have h0 : (0 : Rd d) ∈ closedBall 0 (2 * R + 12) :=
      mem_closedBall_self (by linarith)
    exact (abs_nonneg _).trans
      (convModelGamma_bound hR0 hr0.le hr1 hTc hIc m ω h0)
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hpair : ∀ x ∈ sphere c a, ∀ y ∈ sphere c c',
      r * Real.exp (-(b * convModelGamma R T I m ω)) *
        Y.inf' hYne (fun v => acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ) ≤
      lfppMetric ξ (fun z => Φ z ω) x y := by
    intro x hx y hy
    obtain ⟨v, hv, hvx⟩ := hcover hr hx
    have hDiff : ∀ z ∈ cbox v (2 * ρ) \ obox v ρ,
        |H N z ω - Φ (r • z) ω| ≤ convModelGamma R T I m ω := by
      intro z hz
      have hzR : z ∈ closedBall (0 : Rd d) (2 * R + 12) :=
        convCross_shell_mem_gamma_box ha hρ0 (hY v hv) hR hz.1
      have hh := convModelGamma_bound hR0 hr0.le hr1 hTc hIc m ω hzR
      rw [hΦeq]
      calc
        |H N z ω - (H N z ω + T z ω - m ω + I (r • z) ω)| =
            |-(T z ω + I (r • z) ω - m ω)| := by congr 1; ring
        _ = |T z ω + I (r • z) ω - m ω| := abs_neg _
        _ ≤ _ := hh
    have hbox := convCross_box_le_pair hξ.le hr hr1 hac hρ
      (hΦc ω) ((hH.band N).continuous ω) hx hy hvx hDiff
    have hmin : Y.inf' hYne
        (fun v => acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ) ≤
        Real.exp (ξ * convModelGamma R T I m ω) *
          lfppMetric ξ (fun z => Φ (r • z) ω) (r⁻¹ • x) (r⁻¹ • y) :=
      (Finset.inf'_le _ hv).trans hbox
    have hExp : Real.exp (-(b * convModelGamma R T I m ω)) ≤
        Real.exp (-(ξ * convModelGamma R T I m ω)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.2 hξb) hΓ0]
    have hM0 : 0 ≤ Y.inf' hYne
        (fun v => acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ) := by
      apply Finset.le_inf' hYne
      intro v hv
      exact acrossDist_nonneg _ _ _ _ _
    have hscale : lfppMetric ξ (fun z => Φ z ω) x y =
        r * lfppMetric ξ (fun z => Φ (r • z) ω) (r⁻¹ • x) (r⁻¹ • y) := by
      have hh := lfppMetric_sim (LinearIsometryEquiv.refl ℝ (Rd d)) 0 ξ
        (fun z => Φ z ω) hr0 (r⁻¹ • x) (r⁻¹ • y)
      simpa only [zero_add, LinearIsometryEquiv.coe_refl, id, smul_smul,
        mul_inv_cancel₀ hr0.ne', one_smul] using hh
    rw [hscale]
    calc
      r * Real.exp (-(b * convModelGamma R T I m ω)) *
          Y.inf' hYne (fun v => acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ) ≤
        r * Real.exp (-(ξ * convModelGamma R T I m ω)) *
          Y.inf' hYne (fun v => acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ) := by
            gcongr
      _ ≤ r * (Real.exp (-(ξ * convModelGamma R T I m ω)) *
          (Real.exp (ξ * convModelGamma R T I m ω) *
            lfppMetric ξ (fun z => Φ (r • z) ω) (r⁻¹ • x) (r⁻¹ • y))) := by
              calc
                _ = r * (Real.exp (-(ξ * convModelGamma R T I m ω)) *
                    Y.inf' hYne
                      (fun v => acrossDist ξ (fun z => H N z ω) v (2 * ρ) ρ)) := by ring
                _ ≤ _ := by gcongr
      _ = r * lfppMetric ξ (fun z => Φ (r • z) ω) (r⁻¹ • x) (r⁻¹ • y) := by
        rw [← mul_assoc (Real.exp _) (Real.exp _), ← Real.exp_add]
        simp
  unfold infPairs
  apply le_iInf
  intro x
  apply le_iInf
  intro hx
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  exact ENNReal.ofReal_le_ofReal (hpair x hx y hy)

end HigherDimLQGContinuity
