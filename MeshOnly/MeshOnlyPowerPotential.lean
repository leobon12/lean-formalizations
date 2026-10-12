import MeshOnly.MeshOnlyPowerFlux
import MeshOnly.MeshOnlyPowerMollification
import MeshOnly.MeshOnlyPowerLocalization
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Convex.Topology

/-! Two analytic steps of the local-power construction: smooth closed forms have
normalized primitives with the required bound, and a continuous cellwise
primitive determines actual compatible weights. The weak closedness,
mollification, and limit passage connecting these steps are not asserted here. -/

open scoped Topology

namespace BouRabeeGwynne

/-- The smooth Poincaré step retains the uniform Lipschitz bound needed when
taking a limit of mollified forms. -/
theorem meshOnly_exists_smooth_normalized_primitive {d : ℕ}
    {S : Set (Euc d)} (hS : IsOpen S) (hconv : Convex ℝ S)
    (α : Euc d → Euc d →L[ℝ] ℝ) (hα : DifferentiableOn ℝ α S)
    (hclosed : ∀ a ∈ S, ∀ x y, fderiv ℝ α a x y = fderiv ℝ α a y x)
    (C : ℝ) (hbound : ∀ a ∈ S, ‖α a‖ ≤ C) (z : Euc d) :
    ∃ ψ : Euc d → ℝ, ψ z = 0 ∧
      (∀ a ∈ S, HasFDerivAt ψ (α a) a) ∧
      (∀ x ∈ S, ∀ y ∈ S, |ψ y - ψ x| ≤ C * ‖y - x‖) := by
  obtain ⟨f, hf⟩ := hconv.exists_forall_hasFDerivAt_of_fderiv_symmetric hS hα hclosed
  refine ⟨fun a => f a - f z, sub_self _, ?_, ?_⟩
  · exact fun a ha => (hf a ha).sub_const _
  · intro x hx y hy
    have h := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun a ha => (hf a ha).hasFDerivWithinAt) hbound hx hy
    simpa only [sub_sub_sub_cancel_right, Real.norm_eq_abs] using h

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- Equality of derivatives on the cell interior extends to the closed cell by
continuity. Thus weights are determined by the primitive at the marked points. -/
theorem power_cell_formula_of_primitive {S : Set (Euc d)}
    (hS : IsOpen S) (hconv : Convex ℝ S) (ψ : Euc d → ℝ)
    (hψ : ContinuousOn ψ S) (v : T.V) (hv : T.pos v ∈ S)
    (hderiv : ∀ x ∈ interior (T.cell v).carrier ∩ S,
      HasFDerivAt ψ (2 • innerSL ℝ (x - T.pos v)) x) :
    ∀ y ∈ (T.cell v).carrier ∩ S,
      ψ y = ‖y - T.pos v‖ ^ 2 + ψ (T.pos v) := by
  let g : Euc d → ℝ := fun y => ‖y - T.pos v‖ ^ 2 + ψ (T.pos v)
  have hg : ∀ x, HasFDerivAt g (2 • innerSL ℝ (x - T.pos v)) x :=
    fun x => (meshOnly_hasFDerivAt_sqDist (T.pos v) x).add_const _
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have heq : Set.EqOn ψ g (interior (T.cell v).carrier ∩ S) := by
    refine (isOpen_interior.inter hS).eqOn_of_fderiv_eq
      ((T.cell v).convex.interior.inter hconv).isPreconnected
      (fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt)
      (fun x _ => (hg x).differentiableAt.differentiableWithinAt)
      (fun x hx => (hderiv x hx).fderiv.trans (hg x).fderiv.symm)
      ⟨T.pos_mem_interior v, hv⟩ ?_
    simp [g]
  have hclosure : closure (interior (T.cell v).carrier) = (T.cell v).carrier := by
    rw [(T.cell v).convex.closure_interior_eq_closure_of_nonempty_interior
      (T.cell v).interior_nonempty, (T.cell v).compact.isClosed.closure_eq]
  exact heq.of_subset_closure (hψ.mono Set.inter_subset_right) hgcont.continuousOn
    (Set.inter_subset_inter_left S interior_subset)
    (fun y hy => hS.closure_inter ⟨hclosure.symm ▸ hy.1, hy.2⟩)

/-- Extraction of all local power equations and the Euclidean weight bound from
a continuous primitive. The primitive is an analytic input to this extraction
lemma, not an extra hypothesis in the mesh-only convergence theorem. -/
theorem exists_power_weights_of_primitive {S : Set (Euc d)}
    (hS : IsOpen S) (hconv : Convex ℝ S) (ψ : Euc d → ℝ)
    (hψ : ContinuousOn ψ S)
    (hderiv : ∀ v, ∀ x ∈ interior (T.cell v).carrier ∩ S,
      HasFDerivAt ψ (2 • innerSL ℝ (x - T.pos v)) x)
    (C : ℝ) (hlip : ∀ x ∈ S, ∀ y ∈ S, |ψ y - ψ x| ≤ C * ‖y - x‖) :
    ∃ ω : T.V → ℝ,
      (∀ v w, T.adj v w → T.pos v ∈ S → T.pos w ∈ S →
        (T.facet v w ∩ S).Nonempty → ω w - ω v = T.powerEdgeGap v w) ∧
      (∀ v w, T.pos v ∈ S → T.pos w ∈ S →
        |ω w - ω v| ≤ C * ‖T.pos w - T.pos v‖) := by
  refine ⟨fun v => -ψ (T.pos v), ?_, ?_⟩
  · intro v w hvw hv hw ⟨y, hy, hyS⟩
    have hfv := T.power_cell_formula_of_primitive hS hconv ψ hψ v hv
      (hderiv v) y ⟨hy.1, hyS⟩
    have hfw := T.power_cell_formula_of_primitive hS hconv ψ hψ w hw
      (hderiv w) y ⟨hy.2, hyS⟩
    rw [T.powerEdgeGap_eq hvw hy, powerGapAt]
    linarith
  · intro v w hv hw
    have h := hlip (T.pos v) hv (T.pos w) hw
    simpa only [neg_sub_neg, abs_sub_comm] using h

end OrthogonalTiling

end BouRabeeGwynne
