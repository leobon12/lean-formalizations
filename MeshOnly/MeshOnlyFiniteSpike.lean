import MeshOnly.MeshOnlyClockCrossing
import MeshOnly.MeshOnlySpikeProbability
import Mathlib.MeasureTheory.Measure.Real

/-! The high-error stopping region and the finite-time contradiction estimate.
The measure below is the actual absorbed volume-clock law, the same one as in
the heat survival and corrected-potential crossing estimates. -/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal

namespace BouRabeeGwynne

def meshOnlySpikeRegion {V : Type*} (f g ρ : V → ℝ) (α r : ℝ) : Set V :=
  {v | α / 2 < f v - g v ∧ ρ v < r}

/-- Weighted Chebyshev for the actual high-error region. -/
lemma meshOnly_spikeRegion_mass_le {V : Type*} [Fintype V]
    (m f g ρ : V → ℝ) (hm : ∀ v, 0 ≤ m v) {α : ℝ} (hα : 0 < α) (r : ℝ) :
    (∑ v, (meshOnlySpikeRegion f g ρ α r).indicator m v) ≤
      (4 / α ^ 2) * (∑ v, m v * (f v - g v) ^ 2) := by
  let C := meshOnlySpikeRegion f g ρ α r
  have hα2 : 0 < α / 2 := by positivity
  have hsum : (α / 2) ^ 2 * (∑ v, C.indicator m v) ≤
      ∑ v, m v * (f v - g v) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : v ∈ C
    · rw [Set.indicator_of_mem hv]
      have hgap : α / 2 < f v - g v := hv.1
      have hsq : (α / 2) ^ 2 ≤ (f v - g v) ^ 2 := by nlinarith
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq (hm v)
    · rw [Set.indicator_of_notMem hv, mul_zero]
      exact mul_nonneg (hm v) (sq_nonneg _)
  have hbound : (∑ v, C.indicator m v) ≤
      (∑ v, m v * (f v - g v) ^ 2) / (α / 2) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hα2)).mpr
    simpa only [mul_comm] using hsum
  have heq : (∑ v, m v * (f v - g v) ^ 2) / (α / 2) ^ 2 =
      (4 / α ^ 2) * (∑ v, m v * (f v - g v) ^ 2) := by
    field_simp
    <;> ring
  rw [heq] at hbound
  exact hbound

namespace FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
variable (N : FiniteConductanceNetwork V)

/-- A spike forces survival in the high-error region or crossing the local
ball at every finite Poisson horizon. The continuum oscillation hypothesis is
discharged using the common C² bound and a radius chosen before the data. -/
theorem poissonizedUniformizedLaw_spike_lower_bound (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (f g ρ : V → ℝ) {α H : ℝ} (hα : 0 < α)
    (hH : 0 ≤ H) (r : ℝ) (x : V)
    (hbase : -H ≤ g x) (hmax : ∀ w, f w ≤ H) (hspike : g x + α ≤ f x)
    (hsmall : ∀ w, ρ w < r → g w - g x ≤ α / 4)
    (hf : ∀ v ∈ meshOnlySpikeRegion f g ρ α r, N.laplacian f v = 0)
    (t : ℝ≥0) :
    let C := meshOnlySpikeRegion f g ρ α r
    let μ := N.poissonizedUniformizedLaw m hm C x t
    (α / 4) / (2 * H + 3 * α / 4) ≤
      (μ C).toReal + (μ {w | r ≤ ρ w}).toReal := by
  let C := meshOnlySpikeRegion f g ρ α r
  let μ := N.poissonizedUniformizedLaw m hm C x t
  let F := {w | r ≤ ρ w}
  change (α / 4) / (2 * H + 3 * α / 4) ≤ (μ C).toReal + (μ F).toReal
  have hmean : g x + α ≤ ∫ w, f w ∂μ := by
    rw [N.poissonizedUniformizedLaw_integral_of_harmonic m hm C f hf x t]
    exact hspike
  have hlow : ∀ᵐ w ∂μ, w ∉ C ∪ F → f w ≤ g x + 3 * α / 4 := by
    apply Filter.Eventually.of_forall
    intro w hw
    have hρ : ρ w < r := lt_of_not_ge (fun h => hw (Or.inr h))
    have herr : f w - g w ≤ α / 2 :=
      le_of_not_gt (fun h => hw (Or.inl ⟨h, hρ⟩))
    have hg := hsmall w hρ
    linarith
  have h := mesh_only_spike_probability_lower_bound μ (C ∪ F) f hα hH hbase
    hmean hmax hlow
  exact h.trans (measureReal_union_le C F)

end FiniteConductanceNetwork
end BouRabeeGwynne
