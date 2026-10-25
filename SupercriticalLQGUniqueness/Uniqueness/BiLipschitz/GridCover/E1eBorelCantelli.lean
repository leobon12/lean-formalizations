import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover.E1eGridGeometry
import Mathlib.Analysis.SpecificLimits.Basic




 


set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover

private def gridFailure {Ω : Type} (good : ℕ → ℂ → ℕ → Set Ω)
    (m n : ℕ) : Set Ω :=
  {ω | ∃ q ∈ meshBox m n, ∀ j ≤ n,
    ω ∉ good n (LQGMetric.GM.gridPt (meshStep n) q) j}

 
theorem e1e_grid_failure_bound {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (good : ℕ → ℂ → ℕ → Set Ω)
    (c : ℝ) (hc : 0 ≤ c)
    (hsite : ∀ n x,
      P {ω | ∀ j ≤ n, ω ∉ good n x j} ≤
        ENNReal.ofReal (c * (1 / 100000000 : ℝ) ^ n))
    (m n : ℕ) :
    P (gridFailure good m n) ≤
      ENNReal.ofReal
        ((8 * ((m : ℝ) + 1) + 5) ^ 2 * c * (1 / 10000 : ℝ) ^ n) := by
  have hsub : gridFailure good m n ⊆
      ⋃ q ∈ meshBox m n,
        {ω | ∀ j ≤ n, ω ∉ good n (LQGMetric.GM.gridPt (meshStep n) q) j} := by
    intro ω hω
    obtain ⟨q, hq, hbad⟩ := hω
    exact mem_biUnion hq hbad
  calc
    P (gridFailure good m n) ≤ P (⋃ q ∈ meshBox m n,
        {ω | ∀ j ≤ n, ω ∉ good n (LQGMetric.GM.gridPt (meshStep n) q) j}) :=
      measure_mono hsub
    _ ≤ ∑ q ∈ meshBox m n,
        P {ω | ∀ j ≤ n, ω ∉ good n (LQGMetric.GM.gridPt (meshStep n) q) j} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ meshBox m n,
        ENNReal.ofReal (c * (1 / 100000000 : ℝ) ^ n) := by
      exact Finset.sum_le_sum fun q _ => hsite n _
    _ = ENNReal.ofReal (((meshBox m n).card : ℝ) *
        (c * (1 / 100000000 : ℝ) ^ n)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      conv_rhs => rw [ENNReal.ofReal_mul (by positivity)]
      simp only [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal
        ((8 * ((m : ℝ) + 1) + 5) ^ 2 * c * (1 / 10000 : ℝ) ^ n) := by
      apply ENNReal.ofReal_le_ofReal
      have hcard := e1e_mesh_card_le m n
      have hpow : (10 : ℝ) ^ (4 * n) * (1 / 100000000 : ℝ) ^ n =
          (1 / 10000 : ℝ) ^ n := by
        calc
          (10 : ℝ) ^ (4 * n) * (1 / 100000000 : ℝ) ^ n
              = ((10 : ℝ) ^ 4 * (1 / 100000000 : ℝ)) ^ n := by
                rw [mul_pow, pow_mul]
          _ = (1 / 10000 : ℝ) ^ n := by norm_num
      have hnonneg : 0 ≤ c * (1 / 100000000 : ℝ) ^ n := by positivity
      have h := mul_le_mul_of_nonneg_right hcard hnonneg
      calc
        ((meshBox m n).card : ℝ) * (c * (1 / 100000000 : ℝ) ^ n)
            ≤ ((8 * ((m : ℝ) + 1) + 5) ^ 2 * (10 : ℝ) ^ (4 * n)) *
              (c * (1 / 100000000 : ℝ) ^ n) := h
        _ = (8 * ((m : ℝ) + 1) + 5) ^ 2 * c *
              ((10 : ℝ) ^ (4 * n) * (1 / 100000000 : ℝ) ^ n) := by ring
        _ = _ := by rw [hpow]

 
theorem e1e_grid_eventual {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (good : ℕ → ℂ → ℕ → Set Ω)
    (c : ℝ) (hc : 0 ≤ c)
    (hsite : ∀ n x,
      P {ω | ∀ j ≤ n, ω ∉ good n x j} ≤
        ENNReal.ofReal (c * (1 / 100000000 : ℝ) ^ n)) :
    ∀ᵐ ω ∂P, ∀ m : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ q ∈ meshBox m n,
        ∃ j ≤ n, ω ∈ good n (LQGMetric.GM.gridPt (meshStep n) q) j := by
  have hBC : ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∉ gridFailure good m n := by
    intro m
    have hsum : Summable (fun n : ℕ =>
        (8 * ((m : ℝ) + 1) + 5) ^ 2 * c * (1 / 10000 : ℝ) ^ n) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hsumTop : (∑' n, P (gridFailure good m n)) ≠ ∞ := by
      apply ne_top_of_le_ne_top hsum.tsum_ofReal_lt_top.ne
      exact ENNReal.tsum_le_tsum (fun n => e1e_grid_failure_bound P good c hc hsite m n)
    exact ae_eventually_notMem hsumTop
  filter_upwards [ae_all_iff.2 hBC] with ω hω
  intro m
  obtain ⟨n₀, hn₀⟩ := (Filter.eventually_atTop.1 (hω m))
  refine ⟨n₀, ?_⟩
  intro n hn q hq
  have hnot : ω ∉ gridFailure good m n := hn₀ n hn
  by_contra hno
  have hbad : ∀ j ≤ n, ω ∉ good n (LQGMetric.GM.gridPt (meshStep n) q) j := by
    intro j hj hmem
    exact hno ⟨j, hj, hmem⟩
  exact hnot ⟨q, hq, hbad⟩

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover
