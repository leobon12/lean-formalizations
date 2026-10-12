import MeshOnly.MeshOnlySobolevKernel
import MeshOnly.MeshOnlySobolevApproximation
import Mathlib.Analysis.SpecificLimits.Basic

/-! Endpoint BV Sobolev for the actual finite polyhedral-cell extension,
proved by normalized smooth convolution and Fatou's lemma. -/

open scoped BigOperators Classical ENNReal MeasureTheory Convolution Topology
open MeasureTheory ContinuousLinearMap Filter

namespace BouRabeeGwynne.MeshOnlySobolev

noncomputable def smoothingBump (d k : ℕ) : ContDiffBump (0 : Euc d) where
  rIn := 1 / ((k : ℝ) + 1)
  rOut := 2 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

lemma smoothingBump_rOut_tendsto (d : ℕ) :
    Tendsto (fun k => (smoothingBump d k).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [smoothingBump, mul_zero, mul_one_div] using h

lemma smoothingBump_rOut_le (d k : ℕ) :
    (smoothingBump d k).rOut ≤ 2 * (smoothingBump d k).rIn := by
  dsimp [smoothingBump]
  rw [mul_one_div]

lemma real_convolution_comm {d : ℕ} (f g : Euc d → ℝ) :
    f ⋆[lsmul ℝ ℝ, volume] g = g ⋆[lsmul ℝ ℝ, volume] f := by
  apply convolution_symm
  ext a b
  simp only [flip_apply, lsmul_apply, smul_eq_mul]

end BouRabeeGwynne.MeshOnlySobolev

namespace BouRabeeGwynne.OrthogonalTiling

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

/-- Actual polyhedral-cell BV Sobolev inequality. The only geometric
conditions are containment of active cells in the domain and inclusion of
their contact neighbors. No BV, Sobolev, Nash, or regularity premise is used. -/
theorem meshOnlyCellFunction_sobolev {p : ℝ}
    (hp : Real.HolderConjugate ((n + 1 : ℕ) : ℝ) p)
    (R : Set T.V) [Fintype R] (c : R → ℝ)
    (hcell : ∀ v : R, c v ≠ 0 → (T.cell v).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v : R, c v ≠ 0 → ∀ w : T.V, T.adj v w → w ∈ R) :
    (∫⁻ x, ‖T.meshOnlyCellFunction R c x‖ₑ ^ p ∂volume) ≤
      lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc (n + 1))) p *
        ((n + 1 : ℝ≥0∞) * T.meshOnlyCellVariation R c) ^ p := by
  let b (k : ℕ) := MeshOnlySobolev.smoothingBump (n + 1) k
  let ρ (k : ℕ) := (b k).normed (volume : Measure (Euc (n + 1)))
  let g (k : ℕ) := T.meshOnlyCellFunction R c ⋆[lsmul ℝ ℝ, volume] ρ k
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun k => g k x) atTop
      (𝓝 (T.meshOnlyCellFunction R c x)) := by
    have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (MeshOnlySobolev.smoothingBump_rOut_tendsto (n + 1))
      (Filter.Eventually.of_forall (MeshOnlySobolev.smoothingBump_rOut_le (n + 1)))
      (T.meshOnlyCellFunction_integrable R c).locallyIntegrable
    simpa only [g, ρ, b, MeshOnlySobolev.real_convolution_comm
      (T.meshOnlyCellFunction R c)] using h
  apply MeshOnlySobolev.sobolev_of_smooth_approximation hp
    (T.meshOnlyCellFunction R c) g
    (fun k => T.meshOnlyCellFunction_convolution_contDiff R c (ρ k)
      (b k).contDiff_normed (b k).hasCompactSupport_normed)
    (fun k => T.meshOnlyCellFunction_convolution_compact R c (ρ k)
      (b k).hasCompactSupport_normed)
    hlim
  intro k
  apply T.meshOnlyCellFunction_convolution_lintegral_fderiv_le R c hcell hneighbors
    (ρ k) (b k).contDiff_normed (b k).hasCompactSupport_normed (b k).nonneg_normed
  rw [← ofReal_integral_eq_lintegral_ofReal (b k).integrable_normed
    (Filter.Eventually.of_forall (b k).nonneg_normed), (b k).integral_normed]
  exact ENNReal.ofReal_one

end BouRabeeGwynne.OrthogonalTiling
