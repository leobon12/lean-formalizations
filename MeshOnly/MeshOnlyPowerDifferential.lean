import MeshOnly.MeshOnlyPowerMollification
import MeshOnly.MeshOnlyPowerClosed
import Mathlib.Analysis.Convex.Measure

/-! Relating the actual interior-indicator displacement field to the closed
cell integrals in the geometric weak-curl identity. -/

open scoped Classical BigOperators MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

lemma meshOnly_cell_interior_ae_eq (v : T.V) :
    interior (T.cell v).carrier =ᵐ[volume] (T.cell v).carrier := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp ((T.cell v).convex.addHaar_frontier volume)]
    with x hx
  apply propext
  refine ⟨fun h => interior_subset h, fun h => ?_⟩
  by_contra hi
  exact hx ⟨subset_closure h, hi⟩

lemma meshOnlyDisplacementField_apply (R : Set T.V) [Fintype R]
    (i : Fin d) (x : Euc d) :
    T.meshOnlyDisplacementField R x i =
      ∑ v : R, (interior (T.cell v).carrier).indicator
        (fun y => 2 * (y i - T.pos v i)) x := by
  change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i)
    (∑ v : R, (interior (T.cell v).carrier).indicator
      (fun y => (2 : ℝ) • (y - T.pos v)) x) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hx : x ∈ interior (T.cell v).carrier
  · simp [Set.indicator_of_mem hx, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  · simp [Set.indicator_of_notMem hx]

/-- Continuous test integrals of the concrete displacement field are exactly
the finite geometric cell integrals. Cell boundaries disappear only through
their proved Haar-nullness. -/
lemma meshOnlyDisplacementField_integral_mul (R : Set T.V) [Fintype R]
    (i : Fin d) (χ : Euc d → ℝ) (hχ : Continuous χ) :
    (∫ x, χ x * T.meshOnlyDisplacementField R x i ∂volume) =
      2 * ∑ v : R, ∫ x in (T.cell v).carrier, χ x * (x i - T.pos v i) ∂volume := by
  let f : R → Euc d → ℝ := fun v x => χ x * (2 * (x i - T.pos v i))
  have hfun : (fun x => χ x * T.meshOnlyDisplacementField R x i) =
      fun x => ∑ v : R, (interior (T.cell v).carrier).indicator (f v) x := by
    funext x
    rw [T.meshOnlyDisplacementField_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hx : x ∈ interior (T.cell v).carrier <;> simp [hx, f]
  have hcont (v : R) : Continuous (f v) := by
    dsimp [f]
    fun_prop
  have hint (v : R) : Integrable ((interior (T.cell v).carrier).indicator (f v)) volume := by
    apply (integrable_indicator_iff isOpen_interior.measurableSet).mpr
    exact ((hcont v).continuousOn.integrableOn_compact (T.cell v).compact).mono_set interior_subset
  rw [hfun, integral_finsetSum Finset.univ
    (f := fun v : R => (interior (T.cell v).carrier).indicator (f v))
    (fun (v : R) _ => hint v)]
  have heq (v : R) :
      (∫ x, (interior (T.cell v).carrier).indicator (f v) x ∂volume) =
        2 * ∫ x in (T.cell v).carrier, χ x * (x i - T.pos v i) ∂volume := by
    rw [integral_indicator isOpen_interior.measurableSet,
      setIntegral_congr_set (T.meshOnly_cell_interior_ae_eq v)]
    have hf : f v = fun x => 2 * (χ x * (x i - T.pos v i)) := by
      funext x
      dsimp [f]
      ring
    rw [hf, integral_const_mul]
  simp_rw [heq]
  rw [Finset.mul_sum]

/-- Weak curl vanishes for the actual, globally defined displacement field. -/
theorem meshOnlyDisplacementField_weak_curl {n : ℕ} (T : OrthogonalTiling (n + 1))
    (i j : Fin (n + 1)) (R : Set T.V) [Fintype R]
    (φ : Euc (n + 1) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcell : ∀ v : R, (T.cell v).carrier ⊆ interior T.domain)
    (hcut : ∀ v : R, ∀ w : T.V, w ∉ R → T.adj v w →
      ∀ x ∈ T.facet v w, φ x = 0) :
    (∫ x, (fderiv ℝ φ x) (coordinateAxis i) * T.meshOnlyDisplacementField R x j ∂volume) =
    (∫ x, (fderiv ℝ φ x) (coordinateAxis j) * T.meshOnlyDisplacementField R x i ∂volume) := by
  rw [T.meshOnlyDisplacementField_integral_mul R j _
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const),
    T.meshOnlyDisplacementField_integral_mul R i _
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)]
  congr 1
  simpa only [mul_comm] using T.meshOnly_displacement_weak_curl i j R φ hφ hcell hcut

end BouRabeeGwynne.OrthogonalTiling
