/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafDenseIAssembly
import BrownianMotion.StochasticIntegral.DoobLp

/-!
# Maximal control of continuous closed martingales

Doob's existing weak inequality bounds the running maximum by the L¹ norm
of the closing variable. Summable L¹ errors then give simultaneous eventual
control of consecutive processes on every compact time interval.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

/-- Doob's inequality with the closing variable in place of the terminal
martingale value. All sample paths are continuous in this lemma. -/
theorem closed_martingale_maximal_prob
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓓 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}
    (hX : Martingale X 𝓓 P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hclosed : ∀ t, X t =ᵐ[P] P[Z | 𝓓 t]) (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ ⨆ t : Iic T, ‖X t ω‖} ≤ ε⁻¹ * (∫ ω, ‖Z ω‖ ∂P) := by
  have hw := maximal_ineq_norm hX ε T
    (fun ω _ => (hc ω).continuousAt.continuousWithinAt)
  rw [smul_eq_mul] at hw
  have hi : (∫ ω, ‖X T ω‖ ∂P) ≤ ∫ ω, ‖Z ω‖ ∂P := by
    calc
      _ = ∫ ω, ‖P[Z | 𝓓 T] ω‖ ∂P :=
        integral_congr_ae ((hclosed T).mono fun _ h => congrArg norm h)
      _ ≤ _ := integral_norm_condExp_le Z
  have hh := hw.trans ((setIntegral_le_integral (hX.integrable T).norm
    (ae_of_all _ fun _ => norm_nonneg _)).trans hi)
  calc
    _ = ε⁻¹ * (ε * P.real {ω | ε ≤ ⨆ t : Iic T, ‖X t ω‖}) := by
      rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (inv_nonneg.2 hε.le)

/-- Summable maximal errors give pathwise control on every integer horizon.
The closing variables need only be integrable. -/
theorem ae_eventually_closed_increments_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓓 : Filtration ℝ≥0 mΩ} {X : ℕ → ℝ≥0 → Ω → ℝ} {Z : ℕ → Ω → ℝ}
    (hX : ∀ n, Martingale (X n) 𝓓 P)
    (hc : ∀ n ω, Continuous (fun t => X n t ω))
    (hZ : ∀ n, Integrable (Z n) P)
    (hclosed : ∀ n t, X n t =ᵐ[P] P[Z n | 𝓓 t])
    (herr : ∀ n, (∫ ω, ‖Z n ω - Z (n + 1) ω‖ ∂P) ≤ 2 * (1 / 4 : ℝ) ^ n) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ N →
      dist (X n t ω) (X (n + 1) t ω) ≤ (1 / 2 : ℝ) ^ n := by
  apply ae_all_iff.2
  intro N
  let A (n : ℕ) : Set Ω :=
    {ω | (1 / 2 : ℝ) ^ n ≤ ⨆ t : Iic (N : ℝ≥0), ‖X n t ω - X (n + 1) t ω‖}
  have hm (n : ℕ) : P.real (A n) ≤ 2 * (1 / 2 : ℝ) ^ n := by
    have he (t : ℝ≥0) :
        (fun ω => X n t ω - X (n + 1) t ω) =ᵐ[P] P[Z n - Z (n + 1) | 𝓓 t] := by
      filter_upwards [hclosed n t, hclosed (n + 1) t,
        condExp_sub (hZ n) (hZ (n + 1)) (𝓓 t)] with ω hn hn' hs
      exact (congrArg₂ (· - ·) hn hn').trans hs.symm
    refine (closed_martingale_maximal_prob ((hX n).sub (hX (n + 1)))
      (fun ω => (hc n ω).sub (hc (n + 1) ω)) he N (by positivity)).trans ?_
    calc
      _ ≤ ((1 / 2 : ℝ) ^ n)⁻¹ * (2 * (1 / 4 : ℝ) ^ n) := by
        exact mul_le_mul_of_nonneg_left (herr n) (by positivity)
      _ = _ := by
        rw [← inv_pow, mul_left_comm, ← mul_pow]
        norm_num
  have hs : Summable (fun n => P.real (A n)) :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) hm
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2)
  have hsum : (∑' n, P (A n)) ≠ ⊤ := by
    have he (n : ℕ) : P (A n) = ENNReal.ofReal (P.real (A n)) :=
      (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  intro t ht
  have hb : BddAbove (range fun s : Iic (N : ℝ≥0) =>
      ‖X n s ω - X (n + 1) s ω‖) := by
    have hi : (Iic (N : ℝ≥0)) = Icc 0 (N : ℝ≥0) := by
      ext s
      simp only [mem_Iic, mem_Icc, zero_le, true_and]
    have : CompactSpace (Iic (N : ℝ≥0)) :=
      isCompact_iff_compactSpace.1 (hi ▸ isCompact_Icc)
    exact (isCompact_range
      (((hc n ω).sub (hc (n + 1) ω)).norm.comp continuous_subtype_val)).bddAbove
  have hle := le_ciSup hb (⟨t, ht⟩ : Iic (N : ℝ≥0))
  exact (dist_eq_norm (X n t ω) (X (n + 1) t ω) ▸ hle).trans
    (lt_of_not_ge hn).le

end InteractingSLE.WFS
