import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaleRatioSkC

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open SupercriticalLQGUniqueness.B2.Iface

 

theorem exists_rational_axiomV_of_DG20LimitSkC
    (hS : DG20Section4) (hSk : B2.DG20Lim.DG20LimitSkC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
        (∀ r : ℚ, ∀ hr : 0 < r,
          Tendsto (fun n => (r : ℝ) *
            (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos (ε (φ n)).property
                (Rat.cast_pos.mpr hr))⟩ : ℝ) /
            (m (ε (φ n)) : ℝ)) atTop
            (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
        ∃ Λ : ℝ, 1 < Λ ∧
          ∀ (δ r : ℚ) (hδ : 0 < δ), (δ : ℝ) < 1 → ∀ (hr : 0 < r),
            Λ⁻¹ * (δ : ℝ) ^ Λ ≤
              (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
                (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
            (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
                (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
              Λ * (δ : ℝ) ^ (-Λ) := by
  obtain ⟨φ, hφ, c, hratio, hb⟩ :=
    exists_rational_scale_ratio_bounds_of_DG20LimitSkC hS hSk ξ Q hQ m hm ε hε
  obtain ⟨C, hCpos, hC⟩ := hb 1 one_pos
  let a : ℝ := (ξ : ℝ) * Q
  let Λ : ℝ := max C (|a| + 2) + 1
  have hCΛ : C ≤ Λ := by dsimp [Λ]; linarith [le_max_left C (|a| + 2)]
  have hAΛ : |a| + 2 ≤ Λ := by dsimp [Λ]; linarith [le_max_right C (|a| + 2)]
  have hΛ1 : 1 < Λ := by linarith [abs_nonneg a]
  have hΛpos : 0 < Λ := lt_trans zero_lt_one hΛ1
  have hInv : Λ⁻¹ ≤ C⁻¹ := (inv_le_inv₀ hΛpos hCpos).2 hCΛ
  refine ⟨φ, hφ, c, hratio, Λ, hΛ1, ?_⟩
  intro δ r hδ hδ1 hr
  have hδpos : 0 < (δ : ℝ) := Rat.cast_pos.mpr hδ
  have hδle : (δ : ℝ) ≤ 1 := hδ1.le
  have hE1 : a + 1 ≤ Λ := by linarith [le_abs_self a]
  have hE2 : -Λ ≤ a - 1 := by linarith [neg_abs_le a]
  have hpow1 : (δ : ℝ) ^ Λ ≤ (δ : ℝ) ^ (a + 1) :=
    Real.rpow_le_rpow_of_exponent_ge hδpos hδle hE1
  have hpow2 : (δ : ℝ) ^ (a - 1) ≤ (δ : ℝ) ^ (-Λ) :=
    Real.rpow_le_rpow_of_exponent_ge hδpos hδle hE2
  have hbase := hC δ r hδ hδ1 hr
  constructor
  · calc
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤ C⁻¹ * (δ : ℝ) ^ (a + 1) :=
        mul_le_mul hInv hpow1 (Real.rpow_nonneg hδpos.le _)
          (inv_nonneg.mpr hCpos.le)
      _ ≤ _ := by simpa only [a] using hbase.1
  · calc
      _ ≤ C * (δ : ℝ) ^ (a - 1) := by simpa only [a] using hbase.2
      _ ≤ Λ * (δ : ℝ) ^ (-Λ) :=
        mul_le_mul hCΛ hpow2 (Real.rpow_nonneg hδpos.le _) hΛpos.le

end SupercriticalLQGUniqueness.B2.PfeAxioms
