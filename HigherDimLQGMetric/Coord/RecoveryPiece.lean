import HigherDimLQGMetric.Coord.RecoverySubdivision

/-!
# One-piece quantitative path recovery
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

/-- The weighted estimate in MA1 A6 for one old piece and one realized
replacement piece.  The two curves need no synchronized parametrization. -/
theorem recovery_piece_weighted_bound
    {X : Type*} [MetricSpace X]
    (ρ ρ' : X × X → ℝ) (w : X → ℝ)
    {L : Set X} {z : X} (hz : z ∈ L)
    (Q R : Icc (0 : ℝ) 1 →ᵇ X)
    (hQL : ∀ t, Q t ∈ L) (hRL : ∀ t, R t ∈ L)
    (hQ0 : Q 0 = z) (hR0 : R 0 = z)
    {ℓ e δ χ Ω M : ℝ}
    (hℓ : 0 ≤ ℓ) (he : 0 ≤ e) (heδ : e ≤ δ) (hℓδ : ℓ ≤ δ)
    (_hδ : 0 ≤ δ) (_hχ : 0 ≤ χ) (hΩ : 0 ≤ Ω) (hΩM : Ω ≤ M)
    (hpos : 0 ≤ w z) (hM : w z ≤ M)
    (hmod : ∀ u ∈ L, ∀ v ∈ L,
      ρ (u, v) ≤ 2 * δ → dist u v ≤ χ)
    (hmod' : ∀ u ∈ L, ∀ v ∈ L,
      ρ' (u, v) ≤ 2 * δ → dist u v ≤ χ)
    (hwosc : ∀ u ∈ L, ∀ v ∈ L,
      dist u v ≤ χ → |w u - w v| ≤ Ω)
    (hQlen : curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
      (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal ℓ)
    (hRlen : curveLengthWith (fun u v => ENNReal.ofReal (ρ' (u, v)))
      (Set.IccExtend zero_le_one R) 0 1 ≤ ENNReal.ofReal (ℓ + e)) :
    weightedLengthWith (fun u v => ENNReal.ofReal (ρ' (u, v))) w
        (Set.IccExtend zero_le_one R) 0 1 ≤
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
        (Set.IccExtend zero_le_one Q) 0 1 +
        ENNReal.ofReal (2 * Ω * ℓ + 2 * M * e) := by
  have hℓe : 0 ≤ ℓ + e := add_nonneg hℓ he
  have hℓ2 : ℓ ≤ 2 * δ := by linarith
  have hℓe2 : ℓ + e ≤ 2 * δ := by linarith
  have hQpoint (t : Icc (0 : ℝ) 1) : dist z (Q t) ≤ χ := by
    apply hmod z hz (Q t) (hQL t)
    rw [← hQ0]
    exact coordinate_distance_le_length_bound ρ Q (by linarith : 0 ≤ 2 * δ)
      (by rw [hQlen]; exact ENNReal.ofReal_le_ofReal hℓ2) t
  have hRpoint (t : Icc (0 : ℝ) 1) : dist z (R t) ≤ χ := by
    apply hmod' z hz (R t) (hRL t)
    rw [← hR0]
    exact coordinate_distance_le_length_bound ρ' R (by linarith : 0 ≤ 2 * δ)
      (hRlen.trans (ENNReal.ofReal_le_ofReal hℓe2)) t
  have hQweight (t : Icc (0 : ℝ) 1) : w z - Ω ≤ w (Q t) := by
    have h := hwosc z hz (Q t) (hQL t) (hQpoint t)
    linarith [(abs_le.mp h).2]
  have hRweight (t : Icc (0 : ℝ) 1) : w (R t) ≤ w z + Ω := by
    have h := hwosc z hz (R t) (hRL t) (hRpoint t)
    linarith [(abs_le.mp h).1]
  have hA : weightedLengthWith (fun u v => ENNReal.ofReal (ρ' (u, v))) w
      (Set.IccExtend zero_le_one R) 0 1 ≤
      ENNReal.ofReal ((w z + Ω) * (ℓ + e)) := by
    calc
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ' (u, v))) w
          (Set.IccExtend zero_le_one R) 0 1
          ≤ ENNReal.ofReal (w z + Ω) *
            curveLengthWith (fun u v => ENNReal.ofReal (ρ' (u, v)))
              (Set.IccExtend zero_le_one R) 0 1 :=
            weightedLengthWith_le_ofReal_mul_curveLengthWith (by
              intro t ht
              simpa only [Set.IccExtend_of_mem _ _ ht] using hRweight ⟨t, ht⟩)
      _ ≤ ENNReal.ofReal (w z + Ω) * ENNReal.ofReal (ℓ + e) :=
        mul_le_mul' le_rfl hRlen
      _ = ENNReal.ofReal ((w z + Ω) * (ℓ + e)) := by
        rw [ENNReal.ofReal_mul (add_nonneg hpos hΩ)]
  have hB : ENNReal.ofReal ((w z - Ω) * ℓ) ≤
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
        (Set.IccExtend zero_le_one Q) 0 1 := by
    have h := ofReal_mul_curveLengthWith_le_weightedLengthWith
      (δ := fun u v => ENNReal.ofReal (ρ (u, v)))
      (w := w) (P := Set.IccExtend zero_le_one Q) zero_le_one (by
        intro t ht
        simpa only [Set.IccExtend_of_mem _ _ ht] using hQweight ⟨t, ht⟩)
    rw [hQlen] at h
    simpa only [mul_comm (w z - Ω) ℓ, ENNReal.ofReal_mul hℓ,
      mul_comm (ENNReal.ofReal ℓ) (ENNReal.ofReal (w z - Ω))] using h
  exact weighted_recovery_piece_bound hpos hM hΩ hΩM hℓ he hA hB

end HigherDimLQGMetric
