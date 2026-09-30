import QuantumZipper.Proofs.Section5.Prop16PalmZoom
import QuantumZipper.Proofs.Section5.Prop16D4WInSc0
import QuantumZipper.Proofs.Section5.Prop16LocGood

/-!
# Proposition 1.6, Palm zoom, node A: measurable canonical zoom coordinates (P16-PALM-AB)

`Prop16PalmMeasStmt` (node A of `Prop16PalmZoom.lean`) is proved from the local-goodness node
`Prop16LocGoodStmt` (`prop16PalmMeasStmt_of_loc`), hence from the domain Markov coupling node
`Prop16MixedFreeLocCouplingStmt` (`prop16PalmMeasStmt_of_coupling`, through
`prop16LocGoodStmt_of_coupling`).

Route: `palmCanonCoords = coords (canonicalOn γ (zoomFree …) (zoomDomain D t))`;
* the raw coordinates of `zoomFree` agree `prop16Q`-a.s. with those of the measurable version
  `addConst (zoomField γ C (X ω) t) (F t)`, `F` the measurable piecewise version of `t ↦ 𝔥₀(t)`
  equal to it on `(a,b)`, where `prop16Q` lives (the device of `aemeasurable_zoomFree_scale`);
* the local scale is a.e.-measurable (`aemeasurable_zoomFree_scale`, given `hloc` and the
  a.e.-measurability `prop16NuMeasStmt_of_loc` of the boundary kernel);
* `Prop16Area.aemeasurable_coords_canonicalOn` combines the two.

Own elementary argument (measurability plumbing; AGENT_GUIDE cost rule). No literature input.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Prop16Area.G Prop16Area.Meas TV Factorization

variable {Ω : Type} [MeasurableSpace Ω]

/-- The raw coordinates of the unperturbed zoomed field are a.e.-measurable under `prop16Q`. -/
theorem aemeasurable_coords_zoomFree_p16ab {γ : ℝ} {D : Set ℂ} {c d a b : ℝ} {h0 : ℂ → ℝ}
    {P : Measure Ω} {X : Ω → FieldSample} (hdat : Prop16Data γ D c d a b h0 P X)
    (hν : AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P) (C : ℝ) :
    AEMeasurable (fun p => coords (zoomFree γ C h0 X p)) (prop16Q γ h0 a b P X) := by
  classical
  have hdat' := hdat
  obtain ⟨-, -, -, -, -, -, hh0, -, hX, -, hfin⟩ := hdat'
  have hXm : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ := fun μ => hX.measurable_coord μ
  have hta : ∀ᵐ p ∂(prop16Q γ h0 a b P X), p.2 ∈ Ioo a b :=
    ae_prop16Law_of_ae (G := fun _ t => t ∈ Ioo a b) (aemeasurable_prop16Kernel' hν hfin)
      (fun ω => sFinite_prop16Nu γ h0 a b (X ω)) (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω))
      (ae_of_all _ fun _ _ ht => ht)
  set F : ℝ → ℝ := (Ioo a b).piecewise (fun s => h0 s) 0 with hF
  have hFm : Measurable F := by
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_Ioo
    exact hh0.comp Complex.continuous_ofReal.continuousOn fun s hs => Or.inr ⟨s, hs, rfl⟩
  have e0 : ∀ ω, ofFun (fun _ => (0 : ℝ)) + X ω = X ω := fun ω => by
    funext μ; simp [ofFun]
  have hZ : Measurable fun p : Ω × ℝ => coords (zoomField γ C (X p.1) p.2) := by
    have := measurable_coords_zoomField γ C (fun _ => (0 : ℝ)) hXm
    simpa only [e0] using this
  have hxc : Measurable fun p : Ω × ℝ => coords (addConst (zoomField γ C (X p.1) p.2) (F p.2)) := by
    refine measurable_pi_iff.2 fun i => ?_
    have e : (fun p : Ω × ℝ => coords (addConst (zoomField γ C (X p.1) p.2) (F p.2)) i) =
        fun p => coords (zoomField γ C (X p.1) p.2) i +
          F p.2 * ((foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)) univ).toReal := by
      funext p; rfl
    rw [e]
    exact ((measurable_pi_apply i).comp hZ).add ((hFm.comp measurable_snd).mul measurable_const)
  refine ⟨_, hxc, ?_⟩
  filter_upwards [hta] with p hp
  simp only [zoomFree, hF, Set.piecewise_eq_of_mem _ _ _ hp]

/-- **Node A (`Prop16PalmMeasStmt`) from the local-goodness node `Prop16LocGoodStmt`.** -/
theorem prop16PalmMeasStmt_of_loc (hloc : Prop16LocGoodStmt) : Prop16PalmMeasStmt := by
  intro γ D c d a b h0 Ω _ P X hdat C
  have hν := prop16NuMeasStmt_of_loc hloc γ D c d a b h0 P X hdat
  have hlg := hloc γ D c d a b h0 P X hdat
  exact aemeasurable_coords_canonicalOn γ (fun p => zoomFree γ C h0 X p)
    (fun p => zoomDomain D p.2) (aemeasurable_coords_zoomFree_p16ab hdat hν C)
    (aemeasurable_zoomFree_scale hdat hν hlg C)

/-- **Node A (`Prop16PalmMeasStmt`) from the domain Markov coupling node.** -/
theorem prop16PalmMeasStmt_of_coupling (hA : Prop16MixedFreeLocCouplingStmt) :
    Prop16PalmMeasStmt :=
  prop16PalmMeasStmt_of_loc (prop16LocGoodStmt_of_coupling hA)

end Prop16Asm

end QuantumZipper
