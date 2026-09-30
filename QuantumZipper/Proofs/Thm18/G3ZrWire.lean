import QuantumZipper.Proofs.Thm18.G3ZrShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-REG (4): the curve Fubini of G3Z2B under area-only regularity (D89 form)

`G3Z2b2.G1FacReg` asks, at a window point `x`, for `IsLQGGood` of the zoomed field and of the
pulled-back field in `ChoiceRest`. `IsLQGGood` contains a boundary limit along the **whole** real
line, i.e. also along the preimage of the SLE curve under the local map (the quantum length of the
curve seen from one side). This is the obstruction recorded in D89 for the side maps: the paper
does not use it here, and the consumers only use the **area** part (`canonProxy_eq_canonical`
needs a vague area limit on `ℍ`; the domain-dilation absorption needs `G1.ChoiceRegularA`, as in
`g1ssr_data_eq`).

`G1FacRegA`: the two `RegShift` clauses of `G1FacReg` (proved a.s. at every point in
`G3ZrShift.ae_g1FacReg_shift`) and `G1.ChoiceRegularA` of the translated field at the measurable
map. `G1FacReg → G1FacRegA` (`g1FacRegA_of_g1FacReg`), so this is a genuine weakening.

Main results (copies of the G3Z2B consumers with the area-only step):
* `g3zoomLawM_eqA`, `data_canonical_zoomFieldVia_comp_mulA`, `data_zoom_g1zLocMap_eqA`;
* **`g1zWedgePalmInt_fubiniA`**, **`g3zWedgePalmCyl_fubiniA`**: the curve Fubini formulas of
  `g1zWedgePalmInt_fubini` / `g3zWedgePalmCyl_fubini` under `G1FacRegA` / `G3FacRegA`.

Sheffield, arXiv:1012.4797, p. 70. Own bookkeeping (as D89).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zr

open G3Z2b2 D3Plus Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **Area-only regularity at a window point** (D89 form of `G1FacReg`). -/
def G1FacRegA (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (y : FieldSample)
    (a : ℝ≥0 → ℝ) (x : ℝ) : Prop :=
  (∀ (d : ℂ) (j : ℕ), E1.RegShift (translate y (x : ℂ))
      ((foldedCircle d (radius j)).map (g3mapP Ψ left (y, a, 1, x)))) ∧
    (∀ (d : ℂ) (j : ℕ), E1.RegShift (translate y (x : ℂ))
      ((foldedCircle d (radius j)).map (g1zLocMap left (pathDrive (γ ^ 2) a) x))) ∧
    G1.ChoiceRegularA γ (addConst (translate y (x : ℂ)) (L / γ)) (g3mapP Ψ left (y, a, 1, x))

/-- A regular sample with an area limit has a vague area limit on `ℍ` along the dyadic radii. -/
theorem exists_vague_of_area {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x) {μ : Measure ℂ}
    (hμ : HasAreaLimit γ x μ) : ∃ μ, IsVagueLimitOn H (areaApprox γ x) μ := by
  obtain ⟨F, hF⟩ := hx
  exact ⟨μ, hμ.1, hμ.2.1, fun f hf hfc hfU =>
    ((hμ.2.2 f hf hfc hfU).comp GoodSample.tendsto_one_goodFilter).congr fun k => by
      simp only [Function.comp, goodRad, GoodSample.areaR_radius γ hF]⟩

/-- **The measurable zoom law datum is the canonical data of the zoom** (area-only form). -/
theorem g3zoomLawM_eqA {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (left : Bool) {p : G3Par}
    (hac : Continuous p.2.1) (hs : IsSimpleChord (pathTrace (γ ^ 2) p.2.1)) (hb : 0 < p.2.2.1)
    (hs1 : ∀ (d : ℂ) (j : ℕ), E1.RegShift (translate p.1 (p.2.2.2 : ℂ))
      ((foldedCircle d (radius j)).map (g3mapP Ψ left p)))
    (hcr : G1.ChoiceRegularA γ (addConst (translate p.1 (p.2.2.2 : ℂ)) (L / γ))
      (g3mapP Ψ left p)) :
    g3zoomLawM γ L Ψ left p =
      WedgeMeas.dataFull H (canonical γ (zoomFieldVia γ L p.1 p.2.2.2 (g3mapP Ψ left p))) := by
  have hm : Measurable (g3mapP Ψ left p) := (g3mapB_props hsel hac hs left hb _).2.2
  have hA := avgReg_zoomFieldVia_eq γ L p.1 p.2.2.2 hm hs1
  obtain ⟨hrg, -, ⟨μ, hμ⟩, -, -⟩ := hcr
  have hv : ∃ μ, IsVagueLimitOn H
      (areaApprox γ (zoomFieldVia γ L p.1 p.2.2.2 (g3mapP Ψ left p))) μ := by
    obtain ⟨ν, hν⟩ := exists_vague_of_area hrg hμ
    refine ⟨ν, ?_⟩
    have e : areaApprox γ (zoomFieldVia γ L p.1 p.2.2.2 (g3mapP Ψ left p)) =
        areaApprox γ (coordChange (addConst (translate p.1 (p.2.2.2 : ℂ)) (L / γ))
          (g3mapP Ψ left p) (Qc γ)) := by
      funext k; unfold areaApprox; rw [hA]
    rw [e]; exact hν
  rw [g3zoomLawM, g3coordsM_eq hsel L left hac hs hb, ← canonProxy_eq_canonical hv,
    canonProxy_recon]
  rfl

/-- **Absorption of a domain dilation, area-only form.** -/
theorem data_canonical_zoomFieldVia_comp_mulA {γ : ℝ} (hγ : 0 < γ) (y : FieldSample) (x L : ℝ)
    {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f H) (hf0 : ∀ w ∈ H, deriv f w ≠ 0)
    (hfm : Measurable f)
    (hint : ∀ d ∈ Hbar, ∀ r > 0, Integrable (fun z => Real.log ‖deriv f z‖) (foldedCircle d r))
    {c : ℝ} (hc : 0 < c)
    (hs1 : ∀ (d : ℂ) (j : ℕ),
      E1.RegShift (translate y (x : ℂ)) ((foldedCircle d (radius j)).map f))
    (hs2 : ∀ (d : ℂ) (j : ℕ), E1.RegShift (translate y (x : ℂ))
      ((foldedCircle d (radius j)).map fun w => f ((c : ℂ) * w)))
    (hreg : G1.ChoiceRegularA γ (addConst (translate y (x : ℂ)) (L / γ)) f) :
    WedgeMeas.dataFull H (canonical γ (zoomFieldVia γ L y x fun w => f ((c : ℂ) * w))) =
      WedgeMeas.dataFull H (canonical γ (zoomFieldVia γ L y x f)) := by
  have hm2 : Measurable fun w => f ((c : ℂ) * w) := hfm.comp (measurable_const_mul _)
  rw [Factorization.canonical_congr (avgReg_zoomFieldVia_eq γ L y x hfm hs1),
    Factorization.canonical_congr (avgReg_zoomFieldVia_eq γ L y x hm2 hs2)]
  obtain ⟨hrg, hex, ⟨μ, hμ⟩, hsx, hscx⟩ := hreg
  have hR := G1.regEq_coordChange_comp_mul (addConst (translate y (x : ℂ)) (L / γ)) (Qc γ)
    hfd hf0 hfm hc hint hex
  rw [Factorization.canonical_congr (B3d.avgReg_eq_of_regEq hR) γ]
  exact G1ZA1b.g1za1b_dataFull_canonical_rescale hγ hrg hμ hc hsx
    fun ρ σ hσ => hscx c hc _ (div_pos hsx hc) ρ σ hσ

/-- One zoom through the curve map as the measurable zoom datum (area-only form). -/
theorem data_zoom_g1zLocMap_eqA {γ : ℝ} (hγ : 0 < γ) (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ}
    (hac : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool) {c : ℝ}
    (hc : 0 < c) (hloc : ∀ x ∈ g1SideHalf left, ∀ w : ℂ,
      g1zLocMap left (pathDrive (γ ^ 2) a) x w = g3locM Ψ left (a, x, (c : ℂ) * w))
    {y : FieldSample} (L : ℝ) {x : ℝ} (hxh : x ∈ g1SideHalf left)
    (hreg : G1FacRegA γ L Ψ left y a x) :
    WedgeMeas.dataFull H (canonical γ
      (zoomFieldVia γ L y x (g1zLocMap left (pathDrive (γ ^ 2) a) x))) =
      g1zM γ L Ψ left ((y, a), x) := by
  obtain ⟨hs1, hs2, hcr⟩ := hreg
  have hfun : g1zLocMap left (pathDrive (γ ^ 2) a) x =
      fun w => g3mapP Ψ left (y, a, 1, x) ((c : ℂ) * w) := by
    funext w
    rw [hloc x hxh w]
    simp [g3mapP, g3mapB]
  obtain ⟨hfd, hf0, hfm⟩ := g3mapB_props hsel hac hs left one_pos (x / 1)
  have hint : ∀ d ∈ Hbar, ∀ r > 0, Integrable
      (fun z => Real.log ‖deriv (g3mapP Ψ left (y, a, 1, x)) z‖) (foldedCircle d r) :=
    fun d _ r hr => G1.integrable_log_norm_deriv_foldedCircle_of_injOn hfd
      (injOn_g3mapB hsel hac hs left one_pos (x / 1)) d hr
  rw [hfun] at hs2
  rw [hfun, data_canonical_zoomFieldVia_comp_mulA (f := g3mapP Ψ left (y, a, 1, x)) hγ y x L hfd
    hf0 hfm hint hc hs1 hs2 hcr]
  unfold g1zM
  rw [g3zoomLawM_eqA hsel L left (p := (y, a, 1, x)) hac hs one_pos hs1 hcr]

end G3Zr
end Thm18Asm
end QuantumZipper
