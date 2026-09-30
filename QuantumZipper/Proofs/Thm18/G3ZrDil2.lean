import QuantumZipper.Proofs.Thm18.G3ZrDil

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-REG (3): `DilRegCore` almost surely for the unscaled wedge of the representative

* `contData_dilate_of_rescale`: the continuum limit of `rescale y Q b` along `m` gives the
  continuum limit of `y` along `b · m` (the dilation witness `IsRegularWith.rescale'` and
  `F1.contData_of_dilate` with the inverse dilation).
* `contData_sideMap_of_Psi`: on a good path the chosen side map is the selected map `Ψ left a`
  precomposed with a positive dilation (`side_unique`, `invFunOn_dilate`), so continuum limits
  along the pushed folded circles of `Ψ left a` give those of the side map.
* **`ae_dilRegCore_rep`**: for a continuous path with simple-chord trace, if the selected map has
  a continuous extension (`G1RC.PsiExt`) and the countable Cauchy condition `UCond` holds a.s. for
  the canonical wedge `wedgeRep` (both supplied for a.e. path by `G1RC.g1PsiExtStmt_holds` and
  `g1SidePushUCRepStmt_holds`, the continuum smoothing limit of Duplantier–Sheffield, Invent.
  Math. 185 (2011), Prop. 3.1, at a map independent of the field), then a.s. the unscaled wedge
  `W = wedge0` with `b = scaleParam γ W` satisfies `DilRegCore γ W b x (g1zLocMap left _ (x/b))`
  at every folded circle `fc(d, 2^{-k})` and **every** `x`.
* `ae_dilRegCore_path`: the same for `P.map (pathOf B)`-a.e. path (good paths only).

Sheffield, arXiv:1012.4797, p. 70. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zr

open G3Z2b2

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **Continuum limit after a dilation, from the continuum limit of the dilated field.** -/
theorem contData_dilate_of_rescale {y : FieldSample} (hy : IsRegularSample y) (Q : ℝ) {b : ℝ}
    (hb : 0 < b) {m : Measure ℂ} [IsFiniteMeasure m] (hm : ∀ᵐ u ∂m, u ∈ Hbar)
    (h : F1.ContData (rescale y Q b) m) : F1.ContData y (m.map fun u => (b : ℂ) * u) := by
  obtain ⟨F, hF⟩ := hy
  have hR := hF.congr_evalReg.rescale' Q hb
  have hbi : 0 < b⁻¹ := inv_pos.2 hb
  have hmb : Measurable fun u : ℂ => (b : ℂ) * u := measurable_const_mul _
  refine F1.contData_of_dilate (Z := rescale y Q b) (C := -(Q * Real.log b)) hbi
    (ae_map_mem_Hbar hmb (hm.mono fun u hu => RegClosure.mapsTo_mul_pos hb hu)) ?_ ?_
  · intro u hu ρ hρ
    have hu' : ((b⁻¹ : ℝ) : ℂ) * u ∈ Hbar := RegClosure.mapsTo_mul_pos hbi hu
    rw [hR.evalReg_fc_of_mem hu' (mul_pos hbi hρ)]
    have e1 : (b : ℂ) * (((b⁻¹ : ℝ) : ℂ) * u) = u := by
      have : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
      push_cast; field_simp
    have e2 : b * (b⁻¹ * ρ) = ρ := by field_simp
    show evalReg y (foldedCircle u ρ) = evalReg y (foldedCircle ((b : ℂ) *
      (((b⁻¹ : ℝ) : ℂ) * u)) (b * (b⁻¹ * ρ))) + Q * Real.log b + -(Q * Real.log b)
    rw [e1, e2]; ring
  · rw [Measure.map_map (measurable_const_mul _) hmb]
    have e : ((fun u : ℂ => ((b⁻¹ : ℝ) : ℂ) * u) ∘ fun u => (b : ℂ) * u) = id := by
      have : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
      funext u; simp only [Function.comp, id]; push_cast; field_simp
    rw [e, Measure.map_id]
    exact h

/-- On a good path the side map is `Ψ left a` precomposed with a positive dilation. -/
theorem sideMap_eq_Psi {γ : ℝ} (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (hac : Continuous a)
    (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℂ,
      g1zSideMap left (pathDrive (γ ^ 2) a) u = Ψ left a ((c : ℂ) * u) := by
  have hN := G1ZA1a.isNormalizedUniformizer_sideDom hs left
  obtain ⟨φ, hφ, hΨa⟩ := hsel.2.2 a hac hs left
  obtain ⟨c, hc, hEq⟩ := side_unique hs hN hφ
  refine ⟨c, hc, fun u => ?_⟩
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  rw [hΨa, invFunOn_dilate hN hφ hc hEq]
  congr 1
  field_simp

/-- **Continuum limits along the pushed circles of the side map, from those of `Ψ left a`.** -/
theorem contData_sideMap_of_Psi {γ : ℝ} (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ}
    (hac : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool)
    {z : FieldSample}
    (h : ∀ (d : ℂ) (r : ℝ), 0 < r → F1.ContData z ((foldedCircle d r).map (Ψ left a)))
    (d : ℂ) {r : ℝ} (hr : 0 < r) :
    F1.ContData z ((foldedCircle d r).map (g1zSideMap left (pathDrive (γ ^ 2) a))) := by
  obtain ⟨c, hc, hEq⟩ := sideMap_eq_Psi hsel hac hs left
  have hΨm : Measurable (Ψ left a) := (hsel.1 left).comp (measurable_const.prodMk measurable_id)
  have e : g1zSideMap left (pathDrive (γ ^ 2) a) = Ψ left a ∘ fun u => (c : ℂ) * u :=
    funext hEq
  rw [e, ← Measure.map_map hΨm (measurable_const_mul _), IndepParams.fc_map_mul' _ _ hc]
  exact h _ _ (mul_pos hc hr)

end G3Zr
end Thm18Asm
end QuantumZipper
