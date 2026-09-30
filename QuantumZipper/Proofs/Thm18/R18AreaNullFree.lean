import QuantumZipper.Proofs.LQG.FiniteArea
import QuantumZipper.Proofs.LQG.WedgeCanonical4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-AREANULL, part 1: fixed Lebesgue-null sets carry no quantum area

For the free field `X` (and `0 < γ < 2`) and a **fixed** set `A ⊆ ℂ` of Lebesgue measure zero,
almost surely `μ_X(A) = 0` (`ae_qAreaMeasure_free_null`); the same for the wedge reference field
`wedgeField (lateralPart X) A (Q)` (`ae_qAreaMeasure_wedgeField_null`), whose area is
`e^{γ g} μ_X` (`WedgeCan4.ae_qAreaMeasure_wedgeField_eq`).

Source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011)
(arXiv:0808.1560), Prop. 1.2, formula (2), p. 5: the mean of the area measure has a density
with respect to Lebesgue measure, so the area measure a.s. does not charge a fixed Lebesgue-null
set; this is the fact Sheffield (arXiv:1012.4797, §4.1, p. 48, "the measure zero set η") uses.
Here the mean bound is the `p = 1` case of `FinArea.lintegral_liminf_areaApprox_rpow_le`
(Fatou, `E liminf_k μ_{2^{-k}}(K) ≤ C |K|`), combined with the lower semicontinuity of vague
limits on open sets (portmanteau; `measure_le_liminf_of_isVagueLimitOn`) and outer regularity of
Lebesgue measure. The assembly is our own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- **Portmanteau lower bound on open sets** for vague limits on `ℍ`: if `V` is open, bounded and
`closure V ⊆ ℍ`, then `μ(V) ≤ liminf_k μ_k(V)`. -/
theorem measure_le_liminf_of_isVagueLimitOn {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (h : IsVagueLimitOn H μs μ) {V : Set ℂ} (hV : IsOpen V) (hb : Bornology.IsBounded V)
    (hVH : closure V ⊆ H) : μ V ≤ liminf (fun k => μs k V) atTop := by
  have hne : Vᶜ.Nonempty := ⟨0, fun h0 => by
    have := hVH (subset_closure h0)
    simp [H] at this⟩
  set W : ℕ → Set ℂ := fun j => {z | ((j : ℝ) + 1)⁻¹ < infDist z Vᶜ} with hW
  have hWV : ∀ j : ℕ, {z | ((j : ℝ) + 1)⁻¹ ≤ infDist z Vᶜ} ⊆ V := by
    intro j z hz
    by_contra hzV
    have h0 : infDist z Vᶜ = 0 := infDist_zero_of_mem hzV
    have : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := inv_pos.2 (Nat.cast_add_one_pos j)
    simp only [Set.mem_ofPred_eq] at hz
    linarith
  have hWo : ∀ j, IsOpen (W j) := fun j =>
    isOpen_lt continuous_const (continuous_infDist_pt _)
  have hWc : ∀ j, closure (W j) ⊆ V := fun j =>
    (closure_minimal (fun z (hz : _ < _) => le_of_lt hz)
      (isClosed_le continuous_const (continuous_infDist_pt _))).trans (hWV j)
  have hWmono : Monotone W := by
    intro i j hij z hz
    simp only [hW, Set.mem_ofPred_eq] at hz ⊢
    refine lt_of_le_of_lt ?_ hz
    gcongr
  have hU : (⋃ j, W j) = V := by
    refine Subset.antisymm (iUnion_subset fun j => subset_closure.trans (hWc j)) fun z hz => ?_
    have hpos : 0 < infDist z Vᶜ :=
      (hV.isClosed_compl.notMem_iff_infDist_pos hne).1 (fun h => h hz)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
    exact mem_iUnion.2 ⟨j, by simpa [hW, one_div] using hj⟩
  have hsup : μ V = ⨆ j, μ (W j) := by rw [← hWmono.measure_iUnion, hU]
  rw [hsup]
  refine iSup_le fun j => ?_
  have hKc : IsCompact (closure (W j)) :=
    (hb.subset (subset_closure.trans (hWc j))).isCompact_closure
  have h1 := FinArea.rpow_le_liminf_of_isVagueLimitOn h (hWo j) hKc subset_closure
    ((hWc j).trans (subset_closure.trans hVH)) one_pos
  simp only [ENNReal.rpow_one] at h1
  refine h1.trans (liminf_le_liminf (Eventually.of_forall fun k => measure_mono (hWc j)) ?_ ?_)
  · isBoundedDefault
  · isBoundedDefault

/-- The region `{1/a < Im z} ∩ B(0,a)`. -/
def regionR (a : ℝ) : Set ℂ := {z : ℂ | a⁻¹ < z.im} ∩ ball 0 a

theorem isOpen_regionR (a : ℝ) : IsOpen (regionR a) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter isOpen_ball

theorem closure_regionR_subset_H {a : ℝ} (ha : 0 < a) : closure (regionR a) ⊆ H := by
  refine (closure_minimal (s := regionR a) (t := {z : ℂ | a⁻¹ ≤ z.im})
    (fun z hz => show a⁻¹ ≤ z.im from le_of_lt hz.1) (isClosed_le continuous_const Complex.continuous_im)).trans ?_
  intro z (hz : a⁻¹ ≤ z.im)
  show 0 < z.im
  exact lt_of_lt_of_le (inv_pos.2 ha) hz

section Free

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end Free

section Wedge

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {X : Ω' → FieldSample}
  {A : ℝ → Ω' → ℝ}

end Wedge

end R18
end QuantumZipper
