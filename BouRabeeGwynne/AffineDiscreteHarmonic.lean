import BouRabeeGwynne.PolytopeGaussGreen

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

noncomputable section

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

/-- Each coordinate of the actual conductance-weighted edge sum vanishes.
This is the constant-field case of the proved contact flux theorem. -/
theorem sum_conductance_coordinate_edge_eq_zero_succ
    (i : Fin (n + 1)) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) (hv : (T.neighbors v).Finite) :
    (∑ w ∈ T.neighborFinset v hv,
      T.conductanceReal v w * (T.pos w - T.pos v) i) = 0 := by
  have hflux := T.sum_coordinate_contact_integral_eq_integral_fderiv i v hvD hv
    isOpen_univ (Set.subset_univ _) (f := fun _ => (1 : ℝ)) contDiffOn_const
  simp only [mul_one, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    integral_zero] at hflux
  calc
    _ = ∑ w ∈ T.neighborFinset v hv,
        ∫ _x in T.facet v w,
          (T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖ ∂μHE[n] := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [T.conductanceReal_of_adj ((T.mem_neighborFinset hv).mp hw), setIntegral_const]
      simp only [Measure.real, smul_eq_mul]
      change (T.facetVolume v w).toReal / ‖T.pos w - T.pos v‖ *
        (T.pos w - T.pos v) i =
        (T.facetVolume v w).toReal * ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖)
      ring
    _ = 0 := hflux

end

variable {d : ℕ} (T : OrthogonalTiling d)

/-- Zero conductance-weighted drift at every cell having an ambient collar. -/
theorem sum_conductance_edge_eq_zero
    (hd : 1 ≤ d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) (hv : (T.neighbors v).Finite) :
    (∑ w ∈ T.neighborFinset v hv,
      T.conductanceReal v w • (T.pos w - T.pos v)) = 0 := by
  cases d with
  | zero => omega
  | succ n =>
    apply PiLp.ext
    intro i
    change (PiLp.projₗ 2 (fun _ : Fin (n + 1) => ℝ) i : Euc (n + 1) →ₗ[ℝ] ℝ)
      (∑ w ∈ T.neighborFinset v hv,
        T.conductanceReal v w • (T.pos w - T.pos v)) = 0
    simpa only [map_sum, map_smul, PiLp.projₗ_apply, smul_eq_mul] using
      T.sum_conductance_coordinate_edge_eq_zero_succ i v hvD hv

/-- Every actual affine function of the marked positions is discrete harmonic. -/
theorem discreteLaplacian_affine_eq_zero
    (hd : 1 ≤ d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) (hv : (T.neighbors v).Finite)
    (L : Euc d →L[ℝ] ℝ) (c : ℝ) :
    T.discreteLaplacian (fun w => L (T.pos w) + c) v hv = 0 := by
  have h := congrArg L (T.sum_conductance_edge_eq_zero hd v hvD hv)
  simpa only [map_sum, map_smul, map_sub, map_zero, smul_eq_mul,
    discreteLaplacian, add_sub_add_right_eq_sub] using h

/-- The local affine harmonicity statement includes actual finite neighbor sums. -/
theorem discreteHarmonicOn_affine
    (hd : 1 ≤ d) (A : Set T.V)
    (hAD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (L : Euc d →L[ℝ] ℝ) (c : ℝ) :
    T.DiscreteHarmonicOn (fun w => L (T.pos w) + c) A := by
  intro v hv
  have hfinite := T.neighbors_finite v ((hAD v hv).trans interior_subset)
  exact ⟨hfinite, T.discreteLaplacian_affine_eq_zero hd v (hAD v hv) hfinite L c⟩

end BouRabeeGwynne.OrthogonalTiling
