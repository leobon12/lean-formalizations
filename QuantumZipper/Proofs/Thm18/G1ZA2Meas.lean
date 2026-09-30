import QuantumZipper.Proofs.Thm18.G1ZSplitDefs
import QuantumZipper.Proofs.Thm18.G1Z2MeasMain
import QuantumZipper.Proofs.Thm18.G1Z5SideCert
import QuantumZipper.Proofs.Thm18.G1ZMeasNode

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A2, part 1: the measurable formulas for the factorization `G1RerootFactorStmt`

Sheffield, arXiv:1012.4797, proof of Thm 1.8 (pp. 69–71); own bookkeeping (measurability).

On the path–data space `G1PathData = (ℝ≥0 → ℝ) × ((ℕ → ℝ) × (TestFun H → ℝ))` and for the
measurable selection `Ψ` of `G1PsiSel`:
* `xc` — the pulled-back field of the reconstructed wedge field along `Ψ left a`;
  `xh` — a `FieldSample`-valued measurable map with the same regularized averages;
* `SetS` — the measurable set where `xc` is regular and has the side certificate (so a side
  boundary limit, `sideLim_of_cert`);
* `exists_nuTilde` — a measurable Giry-valued map `ν̃` and a measurable set `E` of full measure with
  `ν̃ = g1SideNu (xc p)` on `E ∩ SetS` (the a.e. modification is made on the measurable set `SetS`,
  so the non-measurable condition "continuous simple path" is never needed for it);
* the measurable functionals `gFun`, `g0Fun` (canonical data read through the proxy).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA2

open D3Plus Factorization

/-- The pulled-back field of the reconstructed field along the selected map. -/
def xc (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (p : G1PathData) : FieldSample :=
  coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ)

/-- A field with the circle coordinates of `xc`, measurable as a `FieldSample`-valued map. -/
def xh (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (p : G1PathData) : FieldSample :=
  E1.fromC (CoordsFull.coordsFull (xc γ Ψ left p))

theorem measurable_coordsFull_xc {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) (i : ℕ) :
    Measurable fun p : G1PathData => CoordsFull.coordsFull (xc γ Ψ left p) i := by
  have hM : Measurable fun q : G1PathData × ℂ => Ψ left q.1.1 q.2 :=
    (hΨ.1 left).comp (measurable_fst.fst.prodMk measurable_snd)
  have hMd : Measurable fun q : G1PathData × ℂ => Real.log ‖deriv (Ψ left q.1.1) q.2‖ :=
    (hΨ.2.1 left).comp (measurable_fst.fst.prodMk measurable_snd)
  have hy : Measurable fun p : G1PathData => E1.fromC p.2.1 :=
    G1Meas.measurable_fromC'.comp measurable_snd.fst
  exact G1Meas.measurable_coordsFull_coordChange (ψ := fun p : G1PathData => Ψ left p.1)
    hy hM hMd (Qc γ) i

theorem measurable_xh {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) : Measurable (xh γ Ψ left) :=
  G1Meas.measurable_fromC'.comp (measurable_pi_iff.2 (measurable_coordsFull_xc hΨ left))

/-- The dyadic coordinates of `xc` are measurable in the path-data. -/
theorem measurable_coords_xc {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) : Measurable fun p : G1PathData => coords (xc γ Ψ left p) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hy : Measurable fun p : G1PathData => E1.fromC p.2.1 :=
    G1Meas.measurable_fromC'.comp measurable_snd.fst
  have hψ : Measurable fun q : G1PathData × ℂ => Ψ left q.1.1 q.2 :=
    (hΨ.1 left).comp (measurable_fst.fst.prodMk measurable_snd)
  have hψd : Measurable fun q : G1PathData × ℂ => Real.log ‖deriv (Ψ left q.1.1) q.2‖ :=
    (hΨ.2.1 left).comp (measurable_fst.fst.prodMk measurable_snd)
  show Measurable fun p : G1PathData =>
    evalReg (E1.fromC p.2.1) ((foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)).map
      (Ψ left p.1)) + Qc γ * ∫ z, Real.log ‖deriv (Ψ left p.1) z‖ ∂foldedCircle
        (dyadicIndex i).1 (radius (dyadicIndex i).2)
  exact (G1Meas.measurable_evalReg_map_param hy hψ _).add (measurable_const.mul
    (StronglyMeasurable.integral_prod_right' (f := fun q : G1PathData × ℂ =>
      Real.log ‖deriv (Ψ left q.1.1) q.2‖) hψd.stronglyMeasurable).measurable)

theorem avgReg_xh (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (p : G1PathData) :
    avgReg (xh γ Ψ left p) = avgReg (xc γ Ψ left p) :=
  CoordsFull.avgReg_congr_full (E1.coordsFull_fromC _)

/-- The good set: `xc` is regular and has the countable side certificate. -/
def SetS (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) : Set G1PathData :=
  {p | IsRegularSample (xc γ Ψ left p) ∧ G1Z5.SideCert γ left (xc γ Ψ left p)}

theorem measurableSet_SetS {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) : MeasurableSet (SetS γ Ψ left) :=
  (G1Meas.measurableSet_rc2 hΨ left).inter
    (G1Z5.measurableSet_sideCert_of_coords γ left (G := xc γ Ψ left)
      (measurable_coordsFull_xc hΨ left))

theorem vagueLimitOnR_of_sideLim {γ : ℝ} {left : Bool} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) {ν : Measure ℝ} (hν : G1Z2SideBdryLim γ left x ν) :
    IsVagueLimitOnR (g1SideHalf left) (bdryApprox γ x) ν :=
  ⟨hν.1, hν.2.1, fun f hf hfc hfS =>
    ((hν.2.2 f hf hfc hfS).comp GoodSample.tendsto_one_goodFilter).congr fun k => by
      simp only [Function.comp, goodRad, GoodSample.bdryR_radius γ hF k]⟩

/-- **A measurable version of the side boundary measure.** -/
theorem exists_nuTilde (μ : Measure G1PathData) {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hΨ : G1PsiSel γ Ψ) (left : Bool) :
    ∃ (ν : G1PathData → Measure ℝ) (E : Set G1PathData), Measurable ν ∧ MeasurableSet E ∧
      μ Eᶜ = 0 ∧ ∀ p ∈ E ∩ SetS γ Ψ left, g1SideNu γ left (xc γ Ψ left p) = ν p := by
  have hS := measurableSet_SetS hΨ left
  have hex : ∀ᵐ p ∂(μ.restrict (SetS γ Ψ left)), ∃ ν,
      IsVagueLimitOnR (g1SideHalf left) (bdryApprox γ (xc γ Ψ left p)) ν :=
    (ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => by
      obtain ⟨⟨F, hF⟩, hc⟩ := hp
      obtain ⟨ν, hν⟩ := G1Z5.sideLim_of_cert hF hc
      exact ⟨ν, vagueLimitOnR_of_sideLim hF hν⟩)
  obtain ⟨M, hMm, hae⟩ := g1z2_aemeasurable_sideNu (Z := xc γ Ψ left)
    (measurable_coords_xc hΨ left).aemeasurable hex
  have hae' := (ae_restrict_iff' hS).1 hae
  obtain ⟨E, hEm, hEp, hE0⟩ := LQGMeasAE.exists_measurableSet_subset_ae hae'
  exact ⟨M, E, hMm, hEm, hE0, fun p hp => hEp p hp.1 hp.2⟩

/-- The rerooting point read from a side measure. -/
def ptOf (left : Bool) (ℓ : ℝ) (ν : Measure ℝ) : ℝ :=
  if left then lenLeft ν ℓ else lenRight ν ℓ

theorem g1SidePt_eq_ptOf (γ : ℝ) (left : Bool) (x : FieldSample) (ℓ : ℝ) :
    g1SidePt γ left x ℓ = ptOf left ℓ (g1SideNu γ left x) := rfl

theorem measurable_ptOf (left : Bool) (ℓ : ℝ) : Measurable (ptOf left ℓ) := by
  cases left
  · have e : ptOf false ℓ = fun ν : Measure ℝ => lenRight ν ℓ := by
      funext ν; simp [ptOf]
    rw [e]
    exact Measurable.comp (g := fun q : Measure ℝ × ℝ => lenRight q.1 q.2)
      (f := fun ν : Measure ℝ => (ν, ℓ)) measurable_lenRight
      (measurable_id.prodMk measurable_const)
  · have e : ptOf true ℓ = fun ν : Measure ℝ => lenLeft ν ℓ := by
      funext ν; simp [ptOf]
    rw [e]
    exact Measurable.comp (g := fun q : Measure ℝ × ℝ => lenLeft q.1 q.2)
      (f := fun ν : Measure ℝ => (ν, ℓ)) measurable_lenLeft
      (measurable_id.prodMk measurable_const)

/-- The measurable rerooted functional. -/
def gFun (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (ℓ : ℝ) (R : ℕ)
    (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) (ν : G1PathData → Measure ℝ) (p : G1PathData) :
    ℝ≥0∞ :=
  Γ (locFieldFull R (canonProxy γ (translate (xh γ Ψ left p) ((ptOf left ℓ (ν p) : ℝ) : ℂ))))

theorem measurable_gFun {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ) (left : Bool)
    (ℓ : ℝ) (R : ℕ) {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ)
    {ν : G1PathData → Measure ℝ} (hν : Measurable ν) : Measurable (gFun γ Ψ left ℓ R Γ ν) := by
  have hpt : Measurable fun p => ptOf left ℓ (ν p) := (measurable_ptOf left ℓ).comp hν
  refine hΓ.comp (g1zMeas_measurable_locFieldFull (fun ν' _ => ?_) R)
  exact Measurable.comp (g := fun r : FieldSample × ℝ => canonProxy γ (translate r.1 (r.2 : ℂ)) ν')
    (f := fun p : G1PathData => (xh γ Ψ left p, ptOf left ℓ (ν p)))
    (g1zMeas_measurable_canonProxy_translate_apply γ ν') ((measurable_xh hΨ left).prodMk hpt)

/-- The measurable canonical data functional. -/
def g0Fun (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (p : G1PathData) :
    (ℕ → ℝ) × (TestFun H → ℝ) :=
  WedgeMeas.dataFull H (WedgeMeas.resc (Qc γ)
    (coords (xh γ Ψ left p), scaleProxy γ (xh γ Ψ left p)))

theorem measurable_g0Fun {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) : Measurable (g0Fun γ Ψ left) :=
  (WedgeMeas.measurable_dataFull_resc H (Qc γ)).comp
    ((measurable_coords.comp (measurable_xh hΨ left)).prodMk
      ((measurable_scaleProxy γ).comp (measurable_xh hΨ left)))

end G1ZA2
end Thm18Asm
end QuantumZipper
