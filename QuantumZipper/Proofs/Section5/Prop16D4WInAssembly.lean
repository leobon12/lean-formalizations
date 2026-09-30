import QuantumZipper.Proofs.Section5.Prop16D4WInClauses

/-!
# D4⁺ʷ inputs (part 8): assembly

`prop16D4WInputs_of_zoom`: the inputs `Prop16D4WInputsStmt` of D4⁺ʷ, with the unperturbed zoomed
field `x C p = zoomFree γ C 𝔥₀ X p = X ω(· + t) + C/γ + 𝔥₀(t)` and `V C p = (D ∪ (a,b)) − t`,
follow from

* `Prop16MixedFreeLocCouplingStmt` (domain Markov coupling of the mixed field with a free field;
  gives local niceness, hence `hloc`, `hsc0` and the local-area facts),
* `Prop16PalmZoomStmt` (input (1) of D4⁺ʷ, the Palm zoom: TV-local convergence of the canonical
  description of `zoomFree` to a `γ`-quantum wedge, with a.e.-measurable coordinates).

The area profile of the wedge is `ae_profileWeak_of_isQuantumWedge`. Consequently
(`theorem1_6_of_zoom`) Proposition 1.6 follows from these two statements.
Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25); own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Prop16Area.G TV Factorization

/-- **Input (1) of D4⁺ʷ (the Palm zoom)** for the unperturbed zoomed field `zoomFree`. -/
def Prop16PalmZoomStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W : Ω' → FieldSample),
      IsProbabilityMeasure P' ∧ IsQuantumWedge γ γ W P' ∧
      (∀ C, AEMeasurable (fun p => coords (canonicalOn γ (zoomFree γ C h0 X p)
        (zoomDomain D p.2))) (prop16Q γ h0 a b P X)) ∧
      ∀ R : ℕ, Tendsto (fun C => tvDist ((prop16Q γ h0 a b P X).map fun p =>
        locField R (canonicalOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)))
        (P'.map fun ω => locField R (W ω))) atTop (𝓝 0)

/-- **The inputs of D4⁺ʷ from the coupling and the Palm zoom.** -/
theorem prop16D4WInputs_of_zoom (hA : Prop16MixedFreeLocCouplingStmt)
    (hZoom : Prop16PalmZoomStmt) : Prop16D4WInputsStmt := by
  intro γ D c d a b h0 Ω _ P X hdat
  obtain ⟨Ω', _, P', W, hP', hW, hZm, hTV⟩ := hZoom γ D c d a b h0 P X hdat
  have hnice := prop16LocNiceStmt_of_coupling hA γ D c d a b h0 P X hdat
  have hlg : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω) :=
    hnice.mono fun _ h => h.isLocallyGoodOn
  have hν := prop16NuMeasStmt_of_loc (prop16LocGoodStmt_of_coupling hA) γ D c d a b h0 P X hdat
  obtain ⟨hγ, hγ2, -⟩ := id hdat
  have hsc0 := prop16_hsc0 hdat hν hnice
  have hWp := ae_profileWeak_of_isQuantumWedge hγ hγ2 hW
  have hWu := Wire2.isQuantumWedge_ae_unitArea hγ hγ2 hW.1 hW
  have hWm := aemeasurable_locField_wedge hγ hγ2 hW
  refine ⟨Ω', _, P', W, hP', hW, fun C p => zoomFree γ C h0 X p,
    fun C p => zoomNbhd D a b p.2, hZm, hTV, fun C => prop16_hloc hdat hν hlg C, hsc0,
    prop16_hgrow hdat hν hlg hWm ?_ hZm hTV hsc0, prop16_htight hdat hν hlg hWm hWp hZm hTV hsc0⟩
  filter_upwards [hWp, hWu] with ω h1 h2
  exact ⟨h1.1, h1.2, h2.2⟩

/-- **Proposition 1.6 from the coupling and the Palm zoom.** -/
theorem theorem1_6_of_zoom (hA : Prop16MixedFreeLocCouplingStmt)
    (hZoom : Prop16PalmZoomStmt) : theorem1_6 :=
  theorem1_6_of_coupling_tvw hA
    (prop16TVWeak_of_inputs (prop16NuMeasStmt_of_loc (prop16LocGoodStmt_of_coupling hA))
      (prop16D4WInputs_of_zoom hA hZoom))

end Prop16Asm

end QuantumZipper
