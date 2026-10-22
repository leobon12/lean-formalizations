import HigherDimLQGMetric.Determ.GridBoxFixed

/-!
# Resampling one cell

Equal dense encodings identify the internal metric on the open cell. The
compatibility relation records the length and two-sided Lipschitz properties
used when one coordinate of the product law is resampled.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

theorem determ_internal_eq_of_enc {D D' : ContMetric d}
    (hD : D.IsLength) (hD' : D'.IsLength)
    {S : Set (Rd d)} (hSo : IsOpen S) (he : determ_enc S D' = determ_enc S D) :
    ∀ u ∈ S, ∀ v ∈ S, D.internal S u v = D'.internal S u v := by
  let p := TopologicalSpace.denseSeq (Rd d × Rd d)
  have hEq : EqOn (fun q : Rd d × Rd d => D.internal S q.1 q.2)
      (fun q => D'.internal S q.1 q.2) (S ×ˢ S ∩ range p) := by
    rintro _ ⟨-, n, rfl⟩
    have he' := congrFun he n
    simp only [determ_enc] at he'
    simp only [D.internal_eq_chainInf hD hSo, D'.internal_eq_chainInf hD' hSo]
    exact he'.symm
  have h := hEq.of_subset_closure (D.continuousOn_internal hD hSo)
    (D'.continuousOn_internal hD' hSo) inter_subset_left
    ((TopologicalSpace.denseRange_denseSeq (Rd d × Rd d)).open_subset_closure_inter
      (hSo.prod hSo))
  exact fun u hu v hv => @h (u, v) ⟨hu, hv⟩

/-- Conditions used to bound one Efron–Stein resampling increment. -/
def DetermCompat (C ε : ℝ) (θ : Fin d → ℝ)
    (S : Finset (Fin d → ℤ)) (D D' : ContMetric d) (k : Fin d → ℤ) : Prop :=
  D'.IsLength ∧
    (∀ x y : Rd d, D'.1 (x, y) ≤ C ^ 2 * D.1 (x, y)) ∧
    (∀ x y : Rd d, D.1 (x, y) ≤ C ^ 2 * D'.1 (x, y)) ∧
    ∀ j ∈ S, j ≠ k → ∀ u ∈ determCube ε θ j, ∀ v ∈ determCube ε θ j,
      D.internal (determCube ε θ j) u v = D'.internal (determCube ε θ j) u v

/-- The finite vector of cell observations. -/
def determY (ε : ℝ) (θ : Fin d → ℝ) (S : Finset (Fin d → ℤ))
    (D : ContMetric d) : S → ℕ → ℝ≥0∞ :=
  fun i => determ_enc (determCube ε θ i.1) D

theorem determ_measurable_Y (ε : ℝ) (θ : Fin d → ℝ)
    (S : Finset (Fin d → ℤ)) : Measurable (determY ε θ S) :=
  Measurable.of_eval fun _ => determ_measurable_enc _

end HigherDimLQGMetric
