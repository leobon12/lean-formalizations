import InteractingSLE.SLE8.TimeGrid
import QuantumZipper.Proofs.RS.BMModulus

/-!
# The localization events `Ω_M` have total probability one ((2.11))

SLE₈ note `source/sle8-continuity.pdf`, §2.2, p. 4: "The Brownian modulus of continuity gives
`ℙ(⋃_{M ≥ 1} Ω_M) = 1`." Here `Ω_M` is `DriverBound M (drive 8 B ω)` (from `TimeGrid.lean`), and the
modulus is QuantumZipper's `RS.bm_modulus`.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace InteractingSLE.SLE8

open QuantumZipper

/-- **`ℙ(⋃_M Ω_M) = 1`** for `W = √8 B` (SLE₈ note, p. 4). -/
theorem ae_exists_nat_driverBound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) :
    ∀ᵐ ω ∂P, ∃ M : ℕ, DriverBound M (drive 8 B ω) := by
  filter_upwards [RS.bm_modulus hB] with ω hω
  obtain ⟨C, hC⟩ := hω 1
  set W := drive 8 B ω with hWdef
  have hWc : Continuous W := drive_continuous (hBc ω)
  obtain ⟨S, hS⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image
    (continuous_abs.comp hWc).continuousOn
  have hS' : ∀ t ∈ Icc (0 : ℝ) 1, |W t| ≤ S := fun t ht => hS ⟨t, ht, rfl⟩
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS' 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨M, hM⟩ := exists_nat_ge (Real.sqrt 8 * |C| + 4 * S + S)
  have h8 : 0 ≤ Real.sqrt 8 * |C| := by positivity
  refine ⟨M, fun t ht => (hS' t ht).trans (by linarith), ?_⟩
  intro s t hs hst ht1
  set h := t - s with hh
  have hpos : 0 < h := sub_pos.2 hst
  have hh1 : h ≤ 1 := by linarith
  have hlog1 : 1 ≤ Real.log (Real.exp 1 / h) := by
    rw [Real.log_div (Real.exp_pos 1).ne' hpos.ne', Real.log_exp]
    linarith [Real.log_nonpos hpos.le hh1]
  have hsq0 : 0 ≤ h * Real.log (Real.exp 1 / h) := by positivity
  have hM0 : (0 : ℝ) ≤ M := by linarith
  rcases le_or_gt h (1 / 2) with hh2 | hh2
  · -- the Brownian modulus
    have hts : t.toNNReal = s.toNNReal + h.toNNReal := by
      rw [← Real.toNNReal_add hs hpos.le]; congr 1; ring
    have hB1 := hC s.toNNReal (by
      rw [Real.toNNReal_le_iff_le_coe]; push_cast; linarith) h.toNNReal
      (Real.toNNReal_pos.2 hpos) (by
        rw [Real.toNNReal_le_iff_le_coe]; push_cast; linarith)
    rw [Real.coe_toNNReal _ hpos.le, ← hts] at hB1
    have hlog : Real.log (1 / h) ≤ Real.log (Real.exp 1 / h) := by
      rw [Real.log_div (Real.exp_pos 1).ne' hpos.ne', Real.log_exp, one_div, Real.log_inv]
      have : Real.log h ≤ 0 := Real.log_nonpos hpos.le hh1
      linarith
    have hsqrt : Real.sqrt (h * Real.log (1 / h)) ≤ Real.sqrt (h * Real.log (Real.exp 1 / h)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog hpos.le)
    calc |W t - W s| = Real.sqrt 8 * |B t.toNNReal ω - B s.toNNReal ω| := by
          simp only [hWdef, drive]
          rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 8)]
      _ ≤ Real.sqrt 8 * (|C| * Real.sqrt (h * Real.log (Real.exp 1 / h))) := by
          gcongr
          exact hB1.trans (mul_le_mul (le_abs_self C) hsqrt (Real.sqrt_nonneg _) (abs_nonneg C))
      _ = (Real.sqrt 8 * |C|) * Real.sqrt (h * Real.log (Real.exp 1 / h)) := by ring
      _ ≤ M * Real.sqrt (h * Real.log (Real.exp 1 / h)) := by
          gcongr; linarith
  · -- long increments: the supremum bound
    have hhalf : 1 / 2 ≤ Real.sqrt (h * Real.log (Real.exp 1 / h)) := by
      rw [Real.le_sqrt (by norm_num) hsq0]
      nlinarith
    calc |W t - W s| ≤ |W t| + |W s| := abs_sub _ _
      _ ≤ S + S := add_le_add (hS' t ⟨by linarith, ht1⟩) (hS' s ⟨hs, by linarith⟩)
      _ ≤ 4 * S * Real.sqrt (h * Real.log (Real.exp 1 / h)) := by nlinarith
      _ ≤ M * Real.sqrt (h * Real.log (Real.exp 1 / h)) := by
          gcongr; linarith

end InteractingSLE.SLE8
