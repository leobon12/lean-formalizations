import BouRabeeGwynne.DiscreteHarmonicMeasure

/-!
# Exit-law toolkit for MR §6 ((75)–(79))

Dynkin's identity for BRG's discrete harmonic measure, and the support of the exit law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace BouRabeeGwynne.MeshRates

open MeasureTheory

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  (N : FiniteConductanceNetwork V)

/-- Dynkin's identity for the exit law (MR (55)–(56), (76), finite-network form): if `ΔF = c·m` on
`A` and `G` vanishes off `A` with `ΔG = -m` on `A`, then `∫ F dH_A(v) = F v + c·G v`. -/
theorem integral_discreteHarmonicMeasure_dynkin (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (m : V → ℝ) (c : ℝ) (F G : V → ℝ)
    (hF : ∀ v ∈ A, N.laplacian F v = c * m v) (hG : ∀ v ∈ A, N.laplacian G v = -m v)
    (hG0 : ∀ v, v ∉ A → G v = 0) (v : V) :
    ∫ w, F w ∂N.discreteHarmonicMeasure A hpos v = F v + c * G v := by
  have h1 : N.SolvesDirichlet A (F + c • G) (F + c • G) := by
    refine ⟨fun x hx => ?_, fun _ _ => rfl⟩
    rw [N.laplacian_add, N.laplacian_smul, hF x hx, hG x hx]; ring
  have h2 : N.SolvesDirichlet A G 0 := by
    refine ⟨fun x _ => ?_, fun x hx => (hG0 x hx).symm⟩
    simp [FiniteConductanceNetwork.laplacian]
  have e1 := N.integral_discreteHarmonicMeasure_of_solvesDirichlet A hpos haccess h1 v
  have e2 := N.integral_discreteHarmonicMeasure_of_solvesDirichlet A hpos haccess h2 v
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2
  rw [integral_add (Integrable.of_finite) (Integrable.of_finite), integral_const_mul, e2] at e1
  linarith

/-- The exit law from `v ∈ A` is carried by vertices outside `A` joined to `A` by an edge. -/
theorem discreteHarmonicMeasure_ae_exit (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    {v : V} (hv : v ∈ A) :
    ∀ᵐ w ∂N.discreteHarmonicMeasure A hpos v, w ∉ A ∧ ∃ u ∈ A, 0 < N.a u w := by
  classical
  set B : Set V := {w | ¬(w ∉ A ∧ ∃ u ∈ A, 0 < N.a u w)} with hB
  let g : V → ℝ := B.indicator 1
  let f : V → ℝ := fun w => if w ∈ A then 0 else g w
  have hf : N.SolvesDirichlet A g f := by
    refine ⟨fun x hx => ?_, fun w hw => by simp [f, hw]⟩
    unfold FiniteConductanceNetwork.laplacian
    refine Finset.sum_eq_zero fun w _ => ?_
    have hfx : f x = 0 := by simp [f, hx]
    rw [hfx, sub_zero]
    by_cases hw : w ∈ A
    · simp [f, hw]
    rcases (N.nonneg x w).lt_or_eq with h | h
    · have : w ∉ B := by simp only [hB, Set.mem_ofPred_eq, not_not]; exact ⟨hw, x, hx, h⟩
      simp [f, g, hw, this]
    · rw [← h, zero_mul]
  have e := N.integral_discreteHarmonicMeasure_of_solvesDirichlet A hpos haccess hf v
  have hfv : f v = 0 := by simp [f, hv]
  rw [hfv, integral_indicator_one (Set.toFinite B).measurableSet] at e
  rw [ae_iff]
  exact (measureReal_eq_zero_iff).mp e

end BouRabeeGwynne.MeshRates
