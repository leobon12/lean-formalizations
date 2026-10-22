import HigherDimLQGContinuity.MomentsW2.Crossing
import HigherDimLQGMetric.DGZ.FieldTails

/-!
# Uniform coarse-field Gaussian tail for W2

The Borell bound is reused from the certified DGZ field estimates. This lemma isolates the
parameter-uniform conversion `ξ ≤ b` and the variable deviation threshold.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLFPP
open HigherDimLFPP.DGZ (cbox)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- A Gaussian lower tail for `ξ h_m`, uniform over all admissible `ξ ≤ b`. -/
theorem w2_coarse_tail (hκ : IsLFPPKernel κ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b μ ξ t : ℝ}, 0 < b → UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        DGZ.IsDyadicRealization κ P W H → ∀ m : ℕ, 1 ≤ m → 0 ≤ t →
          2 * b * (Real.sqrt (2 * d) * (m * Real.log 2) +
            C * Real.sqrt (m * Real.log 2) + C) ≤ t →
          P {ω | ∃ z ∈ cbox (0 : Rd d) R, t < -(ξ * H m z ω)} ≤
            ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (8 * b ^ 2 * (m * Real.log 2)))) := by
  obtain ⟨C, hC, htail⟩ := DGZ.exists_sup_cbox_gaussian_tail hκ hR
  refine ⟨C, hC, ?_⟩
  intro b μ ξ t hb hξ Ω _ P W H hH m hm ht hthreshold
  let v : ℝ := m * Real.log 2
  have hv : 0 < v := by
    dsimp [v]
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    exact mul_pos hm' (DGZ.log_two_pos_lt_one).1
  let base : ℝ := Real.sqrt (2 * d) * v + C * Real.sqrt v + C
  have hbase : 0 ≤ base := by dsimp [base]; positivity
  let u : ℝ := t / b - base
  have hu : t / (2 * b) ≤ u := by
    have hhalf : base ≤ t / (2 * b) :=
      (le_div_iff₀ (by positivity)).2 (by dsimp [base, v]; nlinarith only [hthreshold])
    have hsplit : t / b = 2 * (t / (2 * b)) := by field_simp
    dsimp [u]
    rw [hsplit]
    linarith only [hhalf]
  have hu0 : 0 ≤ u := (div_nonneg ht (by positivity)).trans hu
  have hgauss := htail hH.whiteNoise (a := (2 : ℝ)⁻¹ ^ m) (b := 1)
    (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
    (hH.band m) 0 hu0
  rw [DGZ.log_one_div_inv_two_pow, mul_one] at hgauss
  have hbaseu : Real.sqrt (2 * d) * v + C * Real.sqrt v + C + u = t / b := by
    dsimp [u, base]
    ring
  rw [← show v = (m : ℝ) * Real.log 2 from rfl, hbaseu] at hgauss
  have hsub : {ω | ∃ z ∈ cbox (0 : Rd d) R, t < -(ξ * H m z ω)} ⊆
      {ω | ∃ z ∈ cbox (0 : Rd d) R, t / b < |H m z ω|} := by
    intro ω hω
    obtain ⟨z, hz, hzt⟩ := hω
    refine ⟨z, hz, ?_⟩
    have hξ0 : 0 < ξ := hξ.base.xi_pos
    have hξb : ξ ≤ b := hξ.le_b
    have hx : H m z ω < 0 := by nlinarith only [hzt, ht, hξ0]
    rw [abs_of_neg hx]
    apply (div_lt_iff₀ hb).2
    nlinarith only [hzt, hξb, hx]
  have hsq : (t / (2 * b)) ^ 2 ≤ u ^ 2 :=
    (sq_le_sq₀ (div_nonneg ht (by positivity)) hu0).2 hu
  have hden : 0 < 2 * v := by positivity
  have hexp : 2 * Real.exp (-u ^ 2 / (2 * v)) ≤
      2 * Real.exp (-t ^ 2 / (8 * b ^ 2 * v)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [Real.exp_le_exp]
    have heq : (t / (2 * b)) ^ 2 / (2 * v) = t ^ 2 / (8 * b ^ 2 * v) := by
      field_simp
      ring
    calc
      -u ^ 2 / (2 * v) ≤ -(t / (2 * b)) ^ 2 / (2 * v) :=
        div_le_div_of_nonneg_right (neg_le_neg hsq) hden.le
      _ = -t ^ 2 / (8 * b ^ 2 * v) := by rw [neg_div, neg_div, heq]
  exact (measure_mono hsub).trans (hgauss.trans (ENNReal.ofReal_le_ofReal hexp))

end HigherDimLQGContinuity
