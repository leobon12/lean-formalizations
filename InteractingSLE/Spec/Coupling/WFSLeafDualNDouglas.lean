/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafDualNMeasure
import InteractingSLE.Spec.Coupling.WFSLeafMartMDouglas
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Douglas's L¹ separation theorem

Revuz--Yor, Chapter V, Theorem (4.4), printed p. 210: a variable whose mean is
preserved by every dominated probability perturbation preserving a linear
space containing the constants belongs to that space's L¹ closure.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.WFS

/-- Hahn--Banach separates a point from a closed real subspace by an annihilator. -/
theorem exists_annihilator_of_not_mem_closed_submodule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Submodule ℝ E) (hc : IsClosed (M : Set E)) {z : E} (hz : z ∉ M) :
    ∃ L : E →L[ℝ] ℝ, (∀ x ∈ M, L x = 0) ∧ 0 < L z := by
  obtain ⟨L, a, ha, hza⟩ := geometric_hahn_banach_closed_point M.convex hc hz
  have h0 : 0 < a := by simpa only [map_zero] using ha 0 M.zero_mem
  refine ⟨L, ?_, h0.trans hza⟩
  intro x hx
  by_contra hn
  have h := ha (((a + 1) / L x) • x) (M.smul_mem _ hx)
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hn] at h
  linarith only [h]

/-- Douglas's separation assertion in the exact form used by the WFS argument.
There are no functional-analytic or probabilistic theorem inputs. -/
theorem douglasL1SeparationStatement : DouglasL1SeparationStatement.{u} := by
  intro Ω mΩ P hP C hi h1 Z hZ hinv ε hε
  let T : C →ₗ[ℝ] Lp ℝ 1 P :=
    { toFun := fun f => (hi f f.property).toL1 f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let M := T.range
  let z := hZ.toL1 Z
  have hz : z ∈ M.topologicalClosure := by
    by_contra hn
    obtain ⟨L, hL, hLz⟩ := exists_annihilator_of_not_mem_closed_submodule
      M.topologicalClosure M.isClosed_topologicalClosure hn
    have hLC (f : Ω → ℝ) (hf : f ∈ C) : L ((hi f hf).toL1 f) = 0 :=
      hL _ (M.le_topologicalClosure ⟨⟨f, hf⟩, rfl⟩)
    have hLc : L (Lp.const 1 P (1 : ℝ)) = 0 := by
      have he := hLC (fun _ => 1) h1
      simpa only [Integrable.toL1, MemLp.toLp_const] using he
    obtain ⟨Q, hQ, hQP, hQf⟩ := exists_probability_of_l1_functional P L hLc
    let : IsProbabilityMeasure Q := hQ
    have he : (∫ x, Z x ∂Q) = ∫ x, Z x ∂P := hinv Q hQP fun f hf => by
      rw [hQf f (hi f hf), hLC f hf, zero_div, add_zero]
    rw [hQf Z hZ] at he
    have he0 : L z = 0 := by
      have hd : L z / (‖L‖ + 1) = 0 := by dsimp only [z]; linarith only [he]
      exact (div_eq_zero_iff).1 hd |>.resolve_right (by positivity)
    exact (ne_of_gt hLz) he0
  obtain ⟨y, hy, he⟩ := Metric.mem_closure_iff.1 hz ε hε
  obtain ⟨f, hf⟩ := hy
  refine ⟨f, f.property, ?_⟩
  have he' : ‖(hi f f.property).toL1 f - hZ.toL1 Z‖ < ε := by
    rw [dist_comm, dist_eq_norm, ← hf] at he
    exact he
  rw [← Integrable.toL1_sub _ _ (hi f f.property) hZ,
    L1.norm_of_fun_eq_integral_norm (Integrable.sub (hi f f.property) hZ)] at he'
  exact he'

end InteractingSLE.WFS
