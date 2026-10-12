import MeshOnly.MeshOnlySobolevDerivative
import Mathlib.MeasureTheory.Group.LIntegral

/-! Tonelli's theorem for the actual facet convolution kernels. -/

open scoped BigOperators Classical ENNReal MeasureTheory Convolution
open MeasureTheory ContinuousLinearMap

namespace BouRabeeGwynne.OrthogonalTiling

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

/-- Actual Hausdorff facet volume, with nonedges explicitly zero. -/
noncomputable def meshOnlyFacetVolume (v w : T.V) : ℝ≥0∞ :=
  if T.adj v w then T.facetVolume v w else 0

lemma meshOnlyContactKernel_ofReal (ρ : Euc (n + 1) → ℝ)
    (hρ : Continuous ρ) (hnonneg : ∀ x, 0 ≤ ρ x)
    (x : Euc (n + 1)) {v w : T.V} (hvw : T.adj v w) :
    ENNReal.ofReal (T.meshOnlyContactKernel ρ x v w) =
      ∫⁻ y in T.facet v w, ENNReal.ofReal (ρ (x - y)) ∂μHE[n] := by
  have hK := T.toTilingData.facet_compact v w
  have hint : IntegrableOn (fun y => ρ (x - y)) (T.facet v w) (μHE[n]) :=
    (hρ.comp (continuous_const.sub continuous_id)).continuousOn.integrableOn_of_subset_isCompact
      hK hK.measurableSet Set.Subset.rfl (T.toTilingData.facetVolume_ne_top hvw)
  rw [meshOnlyContactKernel, if_pos hvw]
  exact ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun y => hnonneg (x - y))

lemma measurable_meshOnlyContactKernel_ofReal (ρ : Euc (n + 1) → ℝ)
    (hρ : Continuous ρ) (hnonneg : ∀ x, 0 ≤ ρ x) (v w : T.V) :
    Measurable (fun x => ENNReal.ofReal (T.meshOnlyContactKernel ρ x v w)) := by
  by_cases hvw : T.adj v w
  · letI : IsFiniteMeasure ((μHE[n]).restrict (T.facet v w)) :=
      isFiniteMeasure_restrict.mpr (T.toTilingData.facetVolume_ne_top hvw)
    simp_rw [T.meshOnlyContactKernel_ofReal ρ hρ hnonneg _ hvw]
    exact Measurable.lintegral_prod_right
      (f := fun x y : Euc (n + 1) => ENNReal.ofReal (ρ (x - y)))
      (ENNReal.continuous_ofReal.comp
        (hρ.comp (continuous_fst.sub continuous_snd))).measurable
  · simpa [meshOnlyContactKernel, hvw] using
      (measurable_const : Measurable (fun _ : Euc (n + 1) => (0 : ℝ≥0∞)))

/-- Integrating a normalized smoothing kernel over all translates of a
facet returns precisely that facet's Hausdorff volume. -/
theorem lintegral_meshOnlyContactKernel_ofReal (ρ : Euc (n + 1) → ℝ)
    (hρ : Continuous ρ) (hnonneg : ∀ x, 0 ≤ ρ x)
    (hnorm : ∫⁻ x, ENNReal.ofReal (ρ x) ∂volume = 1) (v w : T.V) :
    (∫⁻ x, ENNReal.ofReal (T.meshOnlyContactKernel ρ x v w) ∂volume) =
      T.meshOnlyFacetVolume v w := by
  by_cases hvw : T.adj v w
  · letI : IsFiniteMeasure ((μHE[n]).restrict (T.facet v w)) :=
      isFiniteMeasure_restrict.mpr (T.toTilingData.facetVolume_ne_top hvw)
    simp_rw [T.meshOnlyContactKernel_ofReal ρ hρ hnonneg _ hvw]
    rw [lintegral_lintegral_swap
      (f := fun x y : Euc (n + 1) => ENNReal.ofReal (ρ (x - y)))
      (ENNReal.continuous_ofReal.comp
        (hρ.comp (continuous_fst.sub continuous_snd))).measurable.aemeasurable]
    simp_rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (ρ x)), hnorm]
    simp [meshOnlyFacetVolume, hvw, TilingData.facetVolume]
  · simp [meshOnlyContactKernel, meshOnlyFacetVolume, hvw]

/-- The facet variation of the finite cellwise constant extension. -/
noncomputable def meshOnlyCellVariation (R : Set T.V) [Fintype R] (c : R → ℝ) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) * ∑ v : R, ∑ w : R,
    T.meshOnlyFacetVolume v w * ENNReal.ofReal |c w - c v|

/-- Every normalized nonnegative smooth mollification has total derivative
bounded by the actual facet variation. This is the tiling-specific analytic
input to endpoint Sobolev; it is proved from the exact cell jump formula. -/
theorem meshOnlyCellFunction_convolution_lintegral_fderiv_le
    (R : Set T.V) [Fintype R] (c : R → ℝ)
    (hcell : ∀ v : R, c v ≠ 0 → (T.cell v).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v : R, c v ≠ 0 → ∀ w : T.V, T.adj v w → w ∈ R)
    (ρ : Euc (n + 1) → ℝ) (hρ : ContDiff ℝ 1 ρ) (hcompact : HasCompactSupport ρ)
    (hnonneg : ∀ x, 0 ≤ ρ x)
    (hnorm : ∫⁻ x, ENNReal.ofReal (ρ x) ∂volume = 1) :
    (∫⁻ x, ‖fderiv ℝ (T.meshOnlyCellFunction R c ⋆[lsmul ℝ ℝ, volume] ρ) x‖ₑ ∂volume) ≤
      (n + 1 : ℝ≥0∞) * T.meshOnlyCellVariation R c := by
  have hK (x : Euc (n + 1)) (v w : R) := T.meshOnlyContactKernel_nonneg ρ hnonneg x v w
  have hm (v w : R) := T.measurable_meshOnlyContactKernel_ofReal ρ hρ.continuous hnonneg v w
  have hpoint (x : Euc (n + 1)) :
      ‖fderiv ℝ (T.meshOnlyCellFunction R c ⋆[lsmul ℝ ℝ, volume] ρ) x‖ₑ ≤
        (n + 1 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) * ∑ v : R, ∑ w : R,
          ENNReal.ofReal (T.meshOnlyContactKernel ρ x v w) * ENNReal.ofReal |c w - c v|) := by
    have hrow (v : R) : ENNReal.ofReal (∑ w : R,
        T.meshOnlyContactKernel ρ x v w * |c w - c v|) =
        ∑ w : R, ENNReal.ofReal (T.meshOnlyContactKernel ρ x v w) *
          ENNReal.ofReal |c w - c v| := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun (w : R) _ =>
        mul_nonneg (hK x v w) (abs_nonneg _))]
      apply Finset.sum_congr rfl
      intro w _
      exact ENNReal.ofReal_mul (hK x v w)
    have h := ENNReal.ofReal_le_ofReal
      (T.meshOnlyCellFunction_convolution_fderiv_bound R c hcell hneighbors
        ρ hρ hcompact hnonneg x)
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_sum_of_nonneg (fun v _ => Finset.sum_nonneg fun w _ =>
        mul_nonneg (hK x v w) (abs_nonneg _))] at h
    simp_rw [hrow] at h
    simpa only [ofReal_norm, ENNReal.ofReal_natCast, Nat.cast_add, Nat.cast_one,
      ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using h
  calc
    _ ≤ ∫⁻ x, (n + 1 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) * ∑ v : R, ∑ w : R,
        ENNReal.ofReal (T.meshOnlyContactKernel ρ x v w) * ENNReal.ofReal |c w - c v|) ∂volume :=
      lintegral_mono hpoint
    _ = (n + 1 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) * ∑ v : R, ∑ w : R,
        (∫⁻ x, ENNReal.ofReal (T.meshOnlyContactKernel ρ x v w) ∂volume) *
          ENNReal.ofReal |c w - c v|) := by
      rw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by norm_num)]
      congr 2
      rw [lintegral_finsetSum Finset.univ (fun v _ =>
        Finset.measurable_sum Finset.univ fun w _ => (hm v w).mul_const _)]
      apply Finset.sum_congr rfl
      intro v _
      rw [lintegral_finsetSum Finset.univ (fun w _ => (hm v w).mul_const _)]
      apply Finset.sum_congr rfl
      intro w _
      exact lintegral_mul_const _ (hm v w)
    _ = _ := by
      simp only [T.lintegral_meshOnlyContactKernel_ofReal ρ hρ.continuous hnonneg hnorm,
        meshOnlyCellVariation]

end BouRabeeGwynne.OrthogonalTiling
