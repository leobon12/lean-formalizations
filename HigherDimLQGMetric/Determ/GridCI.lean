import HigherDimLQGMetric.Determ.GridGeometry

/-!
# Product law for a finite shifted grid

For a normalized log-correlated field and a xi-additive metric, the encoded
open-cell internal distances are independent under the conditional metric law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] [Nonempty (ContMetric d)]
  {h : Ω → DistRd d} {D : Ω → ContMetric d} {ξ : ℝ}

omit [Nonempty (ContMetric d)] in
private theorem determ_grid_union_subtype {ε : ℝ} (θ : Fin d → ℝ)
    (S : Finset (Fin d → ℤ)) (T : Finset S) :
    (⋃ i ∈ T, determCube ε θ i.1) =
      ⋃ k ∈ T.image Subtype.val, determCube ε θ k := by
  ext x
  simp only [mem_iUnion, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨i.1, ⟨i, hi, rfl⟩, hx⟩
  · rintro ⟨k, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨i, hi, hx⟩

/-- The finite grid family has the conditional product law needed by resampling. -/
theorem determ_grid_condDistrib_pi (hh : IsNormalizedLGF h P)
    (hloc : IsXiAdditiveRd ξ P h D D) {ε : ℝ} (hε : 0 < ε)
    (θ : Fin d → ℝ) (S : Finset (Fin d → ℤ)) :
    ∀ᵐ g ∂P.map h,
      (condDistrib D h P g).map
          (fun D (i : S) => determ_enc (determCube ε θ i.1) D) =
        Measure.pi fun i : S =>
          (condDistrib D h P g).map (determ_enc (determCube ε θ i.1)) := by
  classical
  apply determ_condDistrib_pi hh hloc
    (fun i : S => determCube ε θ i.1)
    (fun i => determ_isOpen_cube ε θ i.1)
  · intro T
    have heq := determ_grid_union_subtype θ S T (ε := ε)
    change Bornology.IsBounded (⋃ i ∈ T, determCube ε θ i.1) ∧
      volume (frontier (⋃ i ∈ T, determCube ε θ i.1)) = 0
    rw [heq]
    exact determ_cubes_nice ε θ (T.image Subtype.val)
  · intro T j hj
    have heq := determ_grid_union_subtype θ S T (ε := ε)
    have hj' : j.1 ∉ T.image Subtype.val := by
      intro hmem
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
      have hij : i = j := Subtype.ext he
      exact hj (hij ▸ hi)
    simpa only [heq] using determ_cube_sep_finite hε θ
      (T.image Subtype.val) hj'

end HigherDimLQGMetric
