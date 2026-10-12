import MeshOnly.MeshOnlySobolevBV
import MeshOnly.MeshOnlySobolevJump
import MeshOnly.MeshOnlyCellMass

/-! Conversion of the actual cell and facet measures to the finite real
weighted norms used by the heat equation. -/

open scoped BigOperators Classical ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

lemma meshOnlyFacetVolume_ne_top (v w : T.V) : T.meshOnlyFacetVolume v w ≠ ∞ := by
  by_cases hvw : T.adj v w
  · simpa only [meshOnlyFacetVolume, if_pos hvw] using T.toTilingData.facetVolume_ne_top hvw
  · simp [meshOnlyFacetVolume, hvw]

lemma meshOnlyFacetVolume_toReal (v w : T.V) :
    (T.meshOnlyFacetVolume v w).toReal = T.meshOnlyFacetArea v w := by
  by_cases hvw : T.adj v w
  · rw [meshOnlyFacetVolume, if_pos hvw, T.meshOnlyFacetArea_of_adj hvw]
  · simp [meshOnlyFacetVolume, meshOnlyFacetArea, conductanceReal, hvw]

lemma meshOnlyCellVariation_ne_top (R : Set T.V) [Fintype R] (c : R → ℝ) :
    T.meshOnlyCellVariation R c ≠ ∞ := by
  unfold meshOnlyCellVariation
  apply ENNReal.mul_ne_top (by norm_num)
  apply ENNReal.sum_ne_top.mpr
  intro v _
  apply ENNReal.sum_ne_top.mpr
  intro w _
  exact ENNReal.mul_ne_top (T.meshOnlyFacetVolume_ne_top v w) ENNReal.ofReal_ne_top

lemma meshOnlyCellVariation_toReal_square (R : Set T.V) [Fintype R] (u : R → ℝ) :
    (T.meshOnlyCellVariation R (fun v => u v ^ 2)).toReal = T.meshOnlySquareJump R u := by
  unfold meshOnlyCellVariation meshOnlySquareJump
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_sum (fun (v : R) _ => ENNReal.sum_ne_top.mpr fun (w : R) _ =>
      ENNReal.mul_ne_top (T.meshOnlyFacetVolume_ne_top v w) ENNReal.ofReal_ne_top)]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [ENNReal.toReal_sum (fun (w : R) _ =>
    ENNReal.mul_ne_top (T.meshOnlyFacetVolume_ne_top v w) ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro w _
  rw [ENNReal.toReal_mul, T.meshOnlyFacetVolume_toReal,
    ENNReal.toReal_ofReal (abs_nonneg _)]

/-- Exact real-valued Sobolev mass of the cell extension of the squared
function. The integration weight is the actual primal-cell volume. -/
lemma meshOnlyCellFunction_lintegral_square_toReal
    (R : Set T.V) [Fintype R] (u : R → ℝ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ‖T.meshOnlyCellFunction R (fun v => u v ^ 2) x‖ₑ ^ p ∂volume).toReal =
      ∑ v : R, (T.cell v).volume.toReal * (u v ^ 2) ^ p := by
  rw [T.meshOnlyCellFunction_lintegral_transform (by omega) R (fun v => u v ^ 2)
    (fun a => ‖a‖ₑ ^ p) (by simp [ENNReal.zero_rpow_of_pos hp])]
  rw [ENNReal.toReal_sum (fun (v : R) _ => ENNReal.mul_ne_top
    (T.meshOnly_cellVolume_ne_top v) (ENNReal.rpow_ne_top_of_nonneg hp.le (by simp)))]
  apply Finset.sum_congr rfl
  intro v _
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  simp [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (u v)),
    ENNReal.toReal_ofReal (sq_nonneg (u v))]

/-- Sobolev for squared vertex values in precisely the real raw-sum
normalization used by the Nash and energy arguments. -/
theorem meshOnly_sobolev_real_square {p : ℝ}
    (hp : Real.HolderConjugate ((n + 1 : ℕ) : ℝ) p)
    (R : Set T.V) [Fintype R] (u : R → ℝ)
    (hcell : ∀ v : R, u v ≠ 0 → (T.cell v).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v : R, u v ≠ 0 → ∀ w : T.V, T.adj v w → w ∈ R) :
    (∑ v : R, (T.cell v).volume.toReal * (u v ^ 2) ^ p) ≤
      (lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc (n + 1))) p : ℝ) *
        (((n + 1 : ℕ) : ℝ) * T.meshOnlySquareJump R u) ^ p := by
  have hsob := T.meshOnlyCellFunction_sobolev hp R (fun v => u v ^ 2)
    (fun v hv => hcell v (fun hz => hv (by simp [hz])))
    (fun v hv => hneighbors v (fun hz => hv (by simp [hz])))
  have hfin :
      (lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc (n + 1))) p : ℝ≥0∞) *
        ((n + 1 : ℝ≥0∞) * T.meshOnlyCellVariation R (fun v => u v ^ 2)) ^ p ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hp.symm.nonneg
        (ENNReal.mul_ne_top (by simp) (T.meshOnlyCellVariation_ne_top R _)))
  have h := ENNReal.toReal_mono hfin hsob
  rw [T.meshOnlyCellFunction_lintegral_square_toReal R u hp.symm.pos,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_mul,
    T.meshOnlyCellVariation_toReal_square] at h
  simpa only [ENNReal.coe_toReal,
    ENNReal.toReal_add (by simp : (n : ℝ≥0∞) ≠ ∞) (by simp : (1 : ℝ≥0∞) ≠ ∞),
    ENNReal.toReal_natCast,
    ENNReal.toReal_one, Nat.cast_add, Nat.cast_one] using h

end BouRabeeGwynne.OrthogonalTiling
