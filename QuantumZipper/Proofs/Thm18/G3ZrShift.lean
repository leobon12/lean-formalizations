import QuantumZipper.Proofs.Thm18.G3Z2b2Two
import QuantumZipper.Proofs.Thm18.G1SSR2UC
import QuantumZipper.Proofs.Thm18.G1ZZ1Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-REG (1): the `RegShift` clauses of `G1FacReg` at every window point

For a regular field `y`, a measurable map `ψ : ℍ → ℍ` and real `b`, `x`, the continuum limit
`F1.ContData` of `y` along the pushed folded circles `ψ_* fc(d + b, r)` passes to the translated
field `translate y x` along the pushed circles of the shifted local map `w ↦ ψ(w + b) − x`
(`contData_translate_shift`: `evalReg (translate y x) (fc(u, ρ)) = evalReg y (fc(u + x, ρ))` on
`ℍ̄`, and a real translation of a folded circle is a folded circle). Hence `E1.RegShift`
(`regShift_translate_shift`, via `F1.regShift_of_contData`).

With `G1SidePushContStmt` (proved, `g1SidePushContStmt_holds`: the continuum smoothing limit at the
side map, Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1) this gives, almost surely,
the two `RegShift` clauses of `G3Z2b2.G1FacReg` at **every** point `x` of the side half-line
(`ae_g1FacReg_shift`), not only at boundary-measure-a.e. window points, so no Palm transfer is
needed for them. The curve maps are `w ↦ ψ(w + b) − x` with `ψ` the side map
(`g1zLocMap`), and the measurable maps `g3mapP` are these up to a domain dilation
(`g1zLocMap_eq_g3locM`), which maps folded circles to folded circles.

Sheffield, arXiv:1012.4797, pp. 69–71 (zoom through the local map). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zr

open G3Z2b2

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- Regularized circle values of a real translate of a regular field. -/
theorem evalReg_translate_fc {y : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F) (x : ℝ)
    {u : ℂ} (hu : u ∈ Hbar) {ρ : ℝ} (hρ : 0 < ρ) :
    evalReg (translate y (x : ℂ)) (foldedCircle u ρ) = evalReg y (foldedCircle (u + x) ρ) := by
  have hux : u + (x : ℂ) ∈ Hbar := RegClosure.mapsTo_add_real x hu
  rw [(hF.translate' x).evalReg_fc_of_mem hu hρ, hF.evalReg_fc_of_mem hux hρ]

theorem measurable_evalReg_fc_slice (z : FieldSample) (ρ : ℝ) :
    Measurable fun u : ℂ => evalReg z (foldedCircle u ρ) :=
  (AreaOffsets.measurable_evalReg_fc ρ).comp (f := fun u : ℂ => (z, u)) measurable_prodMk_left

theorem add_real_mem_H {w : ℂ} (hw : w ∈ H) (b : ℝ) : w + (b : ℂ) ∈ H := by
  show 0 < (w + (b : ℂ)).im
  have : 0 < w.im := hw
  simpa using this

theorem shift_mem_Hbar {ψ : ℂ → ℂ} (hψH : MapsTo ψ H H) {w : ℂ} (hw : w ∈ H) (b x : ℝ) :
    ψ (w + (b : ℂ)) - (x : ℂ) ∈ Hbar := by
  have h := hψH (add_real_mem_H hw b)
  have h' : 0 < (ψ (w + (b : ℂ))).im := h
  show 0 ≤ (ψ (w + (b : ℂ)) - (x : ℂ)).im
  simpa using h'.le

/-- **The continuum limit passes to the translated field along the shifted local map.** -/
theorem contData_translate_shift {y : FieldSample} (hy : IsRegularSample y) {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) (hψH : MapsTo ψ H H) (b x : ℝ) (d : ℂ) {r : ℝ} (hr : 0 < r)
    (h : F1.ContData y ((foldedCircle (d + b) r).map ψ)) :
    F1.ContData (translate y (x : ℂ))
      ((foldedCircle d r).map fun w => ψ (w + (b : ℂ)) - (x : ℂ)) := by
  obtain ⟨F, hF⟩ := hy
  obtain ⟨hint, L, hL⟩ := h
  set g : ℂ → ℂ := fun w => ψ (w + (b : ℂ)) - (x : ℂ) with hg
  have hgm : Measurable g := G1ZZ1.measurable_shift_map hψm b x
  have hpt : ∀ ρ : ℝ, 0 < ρ → ∀ w ∈ H, evalReg (translate y (x : ℂ)) (foldedCircle (g w) ρ) =
      evalReg y (foldedCircle (ψ (w + (b : ℂ))) ρ) := by
    intro ρ hρ w hw
    rw [evalReg_translate_fc hF x (shift_mem_Hbar hψH hw b x) hρ]
    simp
  have hbm : Measurable fun w : ℂ => w + (b : ℂ) := measurable_id.add_const _
  have hmapb : (foldedCircle d r).map (fun w : ℂ => w + (b : ℂ)) = foldedCircle (d + b) r :=
    IndepParams.fc_map_add_real d r b
  have hI : ∀ ρ : ℝ, 0 < ρ →
      Integrable (fun u => evalReg (translate y (x : ℂ)) (foldedCircle u ρ))
        ((foldedCircle d r).map g) ∧
      ∫ u, evalReg (translate y (x : ℂ)) (foldedCircle u ρ) ∂((foldedCircle d r).map g) =
        ∫ u, evalReg y (foldedCircle u ρ) ∂((foldedCircle (d + b) r).map ψ) := by
    intro ρ hρ
    have hae : (fun w => evalReg (translate y (x : ℂ)) (foldedCircle (g w) ρ)) =ᵐ[foldedCircle d r]
        fun w => evalReg y (foldedCircle (ψ (w + (b : ℂ))) ρ) :=
      (TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => hpt ρ hρ w hw
    have hi2 : Integrable (fun u => evalReg y (foldedCircle (ψ u) ρ)) (foldedCircle (d + b) r) :=
      (integrable_map_measure (measurable_evalReg_fc_slice y ρ).aestronglyMeasurable
        hψm.aemeasurable).1 (hint ρ hρ)
    have hi3 : Integrable (fun w => evalReg y (foldedCircle (ψ (w + (b : ℂ))) ρ))
        (foldedCircle d r) := by
      rw [← hmapb] at hi2
      exact (integrable_map_measure
        ((measurable_evalReg_fc_slice y ρ).comp hψm).aestronglyMeasurable hbm.aemeasurable).1 hi2
    refine ⟨(integrable_map_measure (measurable_evalReg_fc_slice _ ρ).aestronglyMeasurable
      hgm.aemeasurable).2 (hi3.congr hae.symm), ?_⟩
    rw [integral_map hgm.aemeasurable (measurable_evalReg_fc_slice _ ρ).aestronglyMeasurable,
      integral_congr_ae hae,
      integral_map hψm.aemeasurable (measurable_evalReg_fc_slice y ρ).aestronglyMeasurable]
    exact G1ZZ1.integral_fc_add_real (fun u => evalReg y (foldedCircle (ψ u) ρ)) d r b
  refine ⟨fun ρ hρ => (hI ρ hρ).1, L, hL.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
  exact ((hI ρ hρ).2).symm

/-- **`RegShift` of the translated field along the shifted local map.** -/
theorem regShift_translate_shift {y : FieldSample} (hy : IsRegularSample y) {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) (hψH : MapsTo ψ H H) (b x : ℝ) (d : ℂ) {r : ℝ} (hr : 0 < r)
    (h : F1.ContData y ((foldedCircle (d + b) r).map ψ)) :
    E1.RegShift (translate y (x : ℂ))
      ((foldedCircle d r).map fun w => ψ (w + (b : ℂ)) - (x : ℂ)) := by
  refine F1.regShift_of_contData (hy.translate' x) ?_
    (contData_translate_shift hy hψm hψH b x d hr h)
  have hgm := G1ZZ1.measurable_shift_map hψm b x
  refine (ae_map_iff hgm.aemeasurable (show MeasurableSet Hbar from measurableSet_le measurable_const Complex.measurable_im)).2 ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr] with w hw
  exact shift_mem_Hbar hψH hw b x

/-- The side map of a good path is measurable and maps `ℍ` into `ℍ`. -/
theorem sideMap_facts {γ : ℝ} {a : ℝ≥0 → ℝ} (hs : IsSimpleChord (pathTrace (γ ^ 2) a))
    (left : Bool) (hN : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) a) left)
      (uniformizer (sideDom (pathTrace (γ ^ 2) a) left))) :
    Measurable (g1zSideMap left (pathDrive (γ ^ 2) a)) ∧
      MapsTo (g1zSideMap left (pathDrive (γ ^ 2) a)) H H := by
  obtain ⟨-, -, hm, hD⟩ := G1.invFunOn_props (G1.isOpen_component hs left) hN
  refine ⟨hm, fun w hw => ?_⟩
  have h := hD hw
  cases left
  · exact rightComponent_subset_H _ h
  · exact leftComponent_subset_H _ h

theorem normalized_side {γ : ℝ} {a : ℝ≥0 → ℝ} (left : Bool)
    (hNl : IsNormalizedUniformizer (leftComponent (pathTrace (γ ^ 2) a))
      (uniformizer (leftComponent (pathTrace (γ ^ 2) a))))
    (hNr : IsNormalizedUniformizer (rightComponent (pathTrace (γ ^ 2) a))
      (uniformizer (rightComponent (pathTrace (γ ^ 2) a)))) :
    IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) a) left)
      (uniformizer (sideDom (pathTrace (γ ^ 2) a) left)) := by
  cases left
  · exact hNr
  · exact hNl

/-- **A.s., `RegShift` along the pushed circles of the curve maps, at every point `x`.** -/
theorem ae_regShift_locMap (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (left : Bool) :
    ∀ᵐ ω ∂P, ∀ (x : ℝ) (d : ℂ) (r : ℝ), 0 < r → E1.RegShift (translate (Y ω) (x : ℂ))
      ((foldedCircle d r).map (g1zLocMap left (pathDrive (γ ^ 2) (pathOf B ω)) x)) := by
  filter_upwards [g1SidePushContStmt_holds γ P B Y hS hIn left, hIn.1, hIn.2.2]
    with ω hc hgood hin
  obtain ⟨hsc, -, hNl, hNr⟩ := hin
  rw [sleTrace_eq_pathTrace] at hsc hNl hNr
  simp only [drive_eq_pathDrive] at hc
  obtain ⟨hm, hH⟩ := sideMap_facts hsc left (normalized_side left hNl hNr)
  intro x d r hr
  exact regShift_translate_shift hgood.1.1 hm hH
    (g1zBdryPre left (pathDrive (γ ^ 2) (pathOf B ω)) x) x d hr (hc _ r hr)

/-- **The two `RegShift` clauses of `G1FacReg` hold a.s. at every point of the side half-line.** -/
theorem ae_g1FacReg_shift (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (hsel : G1PsiSel γ Ψ)
    (left : Bool) :
    ∀ᵐ ω ∂P, ∀ x ∈ g1SideHalf left,
      (∀ (d : ℂ) (j : ℕ), E1.RegShift (translate (Y ω) (x : ℂ))
        ((foldedCircle d (radius j)).map (g3mapP Ψ left (Y ω, pathOf B ω, 1, x)))) ∧
      (∀ (d : ℂ) (j : ℕ), E1.RegShift (translate (Y ω) (x : ℂ))
        ((foldedCircle d (radius j)).map (g1zLocMap left (pathDrive (γ ^ 2) (pathOf B ω)) x))) := by
  have hB : IsBrownianReal B P := hS.2.2.1
  filter_upwards [ae_regShift_locMap γ P B Y hS hIn left, hIn.2.2, hB.cont] with ω hR hin hc
  obtain ⟨hsc, -, hNl, hNr⟩ := hin
  rw [sleTrace_eq_pathTrace] at hsc hNl hNr
  have hN := normalized_side left hNl hNr
  obtain ⟨hm, -⟩ := sideMap_facts hsc left hN
  obtain ⟨c, hcpos, hloc⟩ := g1zLocMap_eq_g3locM hsel hc hsc left hN
  intro x hx
  refine ⟨fun d j => ?_, fun d j => hR x d _ (radius_pos j)⟩
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcpos.ne'
  have hfun : g3mapP Ψ left (Y ω, pathOf B ω, 1, x) =
      (g1zLocMap left (pathDrive (γ ^ 2) (pathOf B ω)) x) ∘ (fun w => ((c⁻¹ : ℝ) : ℂ) * w) := by
    funext w
    simp only [Function.comp]
    rw [show g1zLocMap left (pathDrive (γ ^ 2) (pathOf B ω)) x (((c⁻¹ : ℝ) : ℂ) * w) =
      g3locM Ψ left (pathOf B ω, x, (c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * w)) from hloc x hx _]
    have hw : (c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * w) = w := by
      push_cast; field_simp
    rw [hw]
    show ((1 : ℝ) : ℂ) * g3locM Ψ left (pathOf B ω, x / 1, w) = _
    rw [div_one, Complex.ofReal_one, one_mul]
  have hlm : Measurable (g1zLocMap left (pathDrive (γ ^ 2) (pathOf B ω)) x) :=
    G1ZZ1.measurable_shift_map hm _ x
  rw [hfun, ← Measure.map_map hlm (measurable_const_mul _),
    IndepParams.fc_map_mul' _ _ (inv_pos.2 hcpos)]
  exact hR x _ _ (mul_pos (inv_pos.2 hcpos) (radius_pos j))

end G3Zr
end Thm18Asm
end QuantumZipper
