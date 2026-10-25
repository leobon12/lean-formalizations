import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX9
import LQGMetric.Papers.CONF.S3L35




 



set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids

 
def mesh (K : ℕ) : ℝ := ((2 : ℝ) ^ (K + 10))⁻¹

 
def gridBox (K : ℕ) : Finset (ℤ × ℤ) :=
  LQGMetric.CONF.gridBox (mesh K) 3 0

 
def grid (K : ℕ) : Finset ℂ :=
  ((gridBox K).image fun k => (⟨(k.1 : ℝ) * mesh K, (k.2 : ℝ) * mesh K⟩ : ℂ)).filter
    fun z => ‖z‖ < 3

theorem mesh_pos (K : ℕ) : 0 < mesh K := by
  unfold mesh
  positivity

theorem mem_grid_iff (K : ℕ) (z : ℂ) :
    z ∈ grid K ↔ z ∈ LQGMetric.Blueprint.gridPts (mesh K) ∧ z ∈ ball 0 3 := by
  constructor
  · intro hz
    obtain ⟨hzi, hzn⟩ := Finset.mem_filter.mp hz
    obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp hzi
    constructor
    · exact ⟨a, b, rfl⟩
    · simpa only [mem_ball, dist_zero_right] using hzn
  · intro hz
    obtain ⟨k, hk, heq⟩ := LQGMetric.CONF.grid_ball_subset (mesh_pos K) 0 hz
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨k, hk, heq⟩
    · simpa only [mem_ball, dist_zero_right] using hz.2

theorem grid_card_le_box (K : ℕ) : (grid K).card ≤ (gridBox K).card := by
  exact (Finset.card_filter_le _ _).trans Finset.card_image_le

theorem mesh_inv (K : ℕ) : 3 / mesh K = (3 * 2 ^ (K + 10) : ℕ) := by
  have hp : (2 : ℝ) ^ (K + 10) ≠ 0 := by positivity
  simp only [mesh, div_inv_eq_mul]
  norm_cast

theorem gridBox_card (K : ℕ) :
    (gridBox K).card = (2 * (3 * 2 ^ (K + 10)) + 1) ^ 2 := by
  rw [gridBox, LQGMetric.CONF.gridBox_card, mesh_inv]
  simp only [Nat.ceil_natCast]

theorem grid_card_bound (K : ℕ) : (grid K).card ≤ 2 ^ (2 * K + 26) := by
  apply (grid_card_le_box K).trans
  rw [gridBox_card]
  have hp : 1 ≤ 2 ^ (K + 10) := by
    have h : 0 < 2 ^ (K + 10) := pow_pos (by omega : 0 < (2 : ℕ)) _
    omega
  have hb : 2 * (3 * 2 ^ (K + 10)) + 1 ≤ 2 ^ (K + 13) := by
    calc
      2 * (3 * 2 ^ (K + 10)) + 1 ≤ 8 * 2 ^ (K + 10) := by omega
      _ = 2 ^ (K + 13) := by
        rw [show K + 13 = (K + 10) + 3 by omega, pow_add]
        ring
  have hs := Nat.pow_le_pow_left hb 2
  calc
    (2 * (3 * 2 ^ (K + 10)) + 1) ^ 2 ≤ (2 ^ (K + 13)) ^ 2 := hs
    _ = 2 ^ (2 * K + 26) := by
      rw [← pow_mul]
      congr 1
      omega

 
theorem grid_union_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (K : ℕ) (good : ℂ → Set Ω) (ε : ℝ≥0∞)
    (hbad : ∀ z ∈ grid K, μ ((good z)ᶜ) ≤ ε) :
    μ ({ω | ∀ z ∈ grid K, ω ∈ good z}ᶜ) ≤ (grid K).card * ε := by
  classical
  have hset : {ω | ∀ z ∈ grid K, ω ∈ good z}ᶜ =
      ⋃ z ∈ grid K, (good z)ᶜ := by
    ext ω
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, mem_iUnion]
  rw [hset]
  calc
    μ (⋃ z ∈ grid K, (good z)ᶜ) ≤ ∑ z ∈ grid K, μ ((good z)ᶜ) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ grid K, ε := Finset.sum_le_sum hbad
    _ = (grid K).card * ε := by simp only [Finset.sum_const, nsmul_eq_mul]

 
theorem grid_rate_identity (K : ℕ) (hK : K % 2 = 0) (c₀ : ℝ) :
    (2 : ℝ) ^ (2 * K + 26) *
      (c₀ * Real.exp (-4 * ((K / 2 + 1 : ℕ) : ℝ))) =
      2 ^ 26 * c₀ * Real.exp (-4) * (4 * Real.exp (-2)) ^ K := by
  have hhalf : K / 2 + K / 2 = K := by omega
  have hexp : Real.exp (-4 * ((K / 2 + 1 : ℕ) : ℝ)) =
      Real.exp (-4) * (Real.exp (-2)) ^ K := by
    have harg : -4 * ((K / 2 + 1 : ℕ) : ℝ) = -4 + (K : ℝ) * (-2) := by
      have hh : ((K / 2 : ℕ) : ℝ) + ((K / 2 : ℕ) : ℝ) = K := by
        exact_mod_cast hhalf
      push_cast
      linarith
    rw [harg, Real.exp_add, Real.exp_nat_mul]
  rw [hexp]
  have hp : (2 : ℝ) ^ (2 * K + 26) = 2 ^ 26 * 4 ^ K := by
    rw [show 2 * K + 26 = 26 + 2 * K by omega, pow_add, pow_mul]
    norm_num
  rw [hp, mul_pow]
  ring

 
theorem grid_failure_rate {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (K : ℕ) (hK : K % 2 = 0) (good : ℂ → Set Ω)
    (c₀ : ℝ) (hc₀ : 0 ≤ c₀)
    (hbad : ∀ z ∈ grid K,
      μ ((good z)ᶜ) ≤ ENNReal.ofReal
        (c₀ * Real.exp (-4 * ((K / 2 + 1 : ℕ) : ℝ)))) :
    μ ({ω | ∀ z ∈ grid K, ω ∈ good z}ᶜ) ≤
      ENNReal.ofReal (2 ^ 26 * c₀ * Real.exp (-4) *
        (4 * Real.exp (-2)) ^ K) := by
  let a : ℝ := c₀ * Real.exp (-4 * ((K / 2 + 1 : ℕ) : ℝ))
  have ha : 0 ≤ a := mul_nonneg hc₀ (Real.exp_pos _).le
  calc
    μ ({ω | ∀ z ∈ grid K, ω ∈ good z}ᶜ) ≤
        (grid K).card * ENNReal.ofReal a := grid_union_bound μ K good _ hbad
    _ ≤ (2 ^ (2 * K + 26) : ℕ) * ENNReal.ofReal a := by
      gcongr
      exact grid_card_bound K
    _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * K + 26) * a) := by
      calc
        ((2 ^ (2 * K + 26) : ℕ) : ℝ≥0∞) * ENNReal.ofReal a =
            ENNReal.ofReal (((2 ^ (2 * K + 26) : ℕ) : ℝ) * a) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * K + 26) * a) := by norm_cast
    _ = ENNReal.ofReal (2 ^ 26 * c₀ * Real.exp (-4) *
        (4 * Real.exp (-2)) ^ K) := by
      congr 1
      exact grid_rate_identity K hK c₀


end SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids
