/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15Heights

/-!
# The canonical native mean is the original pocket's source extension

PROVE-SIDE-COLLAR2. Both source and native extensions are bounded
harmonic. Their boundary values agree away from the union of their
finite exceptional sets. Uniqueness identifies them on the whole
half-plane, then restores the source's original exception set.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H chiC)
open scoped NNReal Real

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.SideC13 Sec7.Aux119Heights Sec7.Aux2728Pocket Sec7.PocketStopSide

variable {Ω : Type} [MeasurableSpace Ω]

/-- The native flow mean has exactly the source wall heights and source
exception set. This discharges C14's `hNativeWord` for every ready test. -/
theorem canonicalInitialFlowMean_source_extension {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) :
    IsBoundedHarmonicExtension
      (chartData (d.leftWall j.seed ω) (d.rightWall ω)
        (fun s => sleLambda (16 / i.kappa) -
          (if s < StripSys.rt j.seed then π / 2 else rs136Theta2 (16 / i.kappa) i.rightWeight) * chiC (16 / i.kappa))
        (fun s => -sleLambda (16 / i.kappa) -
          (if s < 1 then -(π / 2) else rs136Theta1 (16 / i.kappa) i.leftWeight) * chiC (16 / i.kappa))
        (conjugateFlowChart ((j.target i d).baseChart ω)))
      (exSet (d.leftWall j.seed ω) (d.rightWall ω) {StripSys.rt j.seed} {1}
        (conjugateFlowChart ((j.target i d).baseChart ω)))
      (j.canonicalInitialFlowMean i d ω) := by
  have hF := j.isFlowChart_conjugate_of_ready hj hRc hLc hω
  obtain ⟨G, hG⟩ := exists_isBoundedHarmonicExtension_twoAngle hF
    (16 / i.kappa) (π / 2) (rs136Theta2 (16 / i.kappa) i.rightWeight)
    (-(π / 2)) (rs136Theta1 (16 / i.kappa) i.leftWeight) (StripSys.rt j.seed) 1
  let g : ℝ → ℝ := chartData (d.leftWall j.seed ω) (d.rightWall ω)
        (fun s => sleLambda (16 / i.kappa) -
          (if s < StripSys.rt j.seed then π / 2 else rs136Theta2 (16 / i.kappa) i.rightWeight) * chiC (16 / i.kappa))
        (fun s => -sleLambda (16 / i.kappa) -
          (if s < 1 then -(π / 2) else rs136Theta1 (16 / i.kappa) i.leftWeight) * chiC (16 / i.kappa))
        (conjugateFlowChart ((j.target i d).baseChart ω))
  let S₀ := exSet (d.leftWall j.seed ω) (d.rightWall ω) {StripSys.rt j.seed} {1}
    (conjugateFlowChart ((j.target i d).baseChart ω))
  let J := forceJumpSet ((j.target i d).marksL ω) ((j.target i d).marksR ω)
  let S := S₀ ∪ (fun x : ℝ => -x⁻¹) '' J
  have hSf : S.Finite := (Aux2728Pocket.IsFlowChart.finite_exSet hF (finite_singleton _) (finite_singleton _)).union
    ((Impl.forceJumpSet_finite (Ito.weightWord (j.target i d).rhoL (j.target i d).rhoR)
      ((j.target i d).marksL ω) ((j.target i d).marksR ω)).image _)
  obtain ⟨hM, hBound⟩ := j.canonicalInitialFlowMean_harmonic_bounded i d ω
  have hGS : IsBoundedHarmonicExtension g S G :=
    ⟨hG.1, hG.2.1, fun ξ hξ => hG.2.2 ξ (fun h => hξ (Or.inl h))⟩
  have hMS : IsBoundedHarmonicExtension g S (j.canonicalInitialFlowMean i d ω) := by
    refine ⟨hM, hBound, ?_⟩
    intro ξ hξ
    have hξ₀ : ξ ∉ S₀ := fun he => hξ (Or.inl he)
    have hx : -ξ⁻¹ ∉ J := by
      intro he
      apply hξ
      exact Or.inr ⟨-ξ⁻¹, he, by simp only [inv_neg, inv_inv, neg_neg]⟩
    have hLim := j.canonicalInitialFlowMean_tendsto i d ω hx
    have hHeight := j.chartData_eq_initialFlowAngles_of_ready hj hRc hLc hω hξ₀
    dsimp only [g]
    rw [hHeight]
    simpa only [Complex.ofReal_neg, Complex.ofReal_inv, inv_neg, inv_inv, neg_neg] using hLim
  have heq := Impl.eqOn_of_isBoundedHarmonicExtension hSf hGS hMS
  refine ⟨hM, hBound, ?_⟩
  intro ξ hξ
  exact (hG.2.2 ξ hξ).congr' (eventually_nhdsWithin_of_forall fun z hz => (heq hz).symm)

end InteractingSLE.Wire.Current.SideTest
