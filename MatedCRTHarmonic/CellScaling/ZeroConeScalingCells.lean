import MatedCRTHarmonic.IGLaw.OCurveScale
import MatedCRTHarmonic.CellScaling.JointScalingOFinal
import MatedCRTHarmonic.GMS4b.BundleAdapter
import MatedCRTHarmonic.GMS4b.UStarMoments

/-!
# Zero-cone cell observables at every mass mesh

The ε-cell diameter and degrees have their unit-mesh joint law. The frozen bundle's
`cellMoments` therefore supplies finite moments uniformly over ε, in the exact
`GMS4b` shape used by [18] Proposition 4.8.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling.ZeroConeScaling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The joint law of the ε-cell diameter and inner/outer degrees is its unit-cell law. -/
theorem cellLaw_holds
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) :
    P.map (fun ω => GMS4b.localTriple ε (η₀ ω)) =
      P.map (fun ω => GMS4b.localTriple 1 (η₀ ω)) :=
  GMS4b.theorem44_law_holds D.measurable_curves.2.2.1
    (IGLaw.IsMatingOfTreesCoupling.curveScaleInvariant D hγ) hε

/-- The unit-cell moment field of the frozen coupling, expressed in [18]'s local observables. -/
private theorem unitMoments
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    GMS4b.UnitCellMoments γ P η₀ := by
  have h0 : ∀ᵐ ω ∂P, η₀ ω 0 = 0 := by
    filter_upwards [D.areaParam₀, D.spaceFilling] with ω harea hspace
    rcases harea.1 with ⟨φ, hφ0, hηeq⟩
    rw [hηeq, hφ0, hspace.2.2.1]
  exact GMS4b.unitCellMoments_of_cellMoments h0 D.cellMoments

/-- [18] Theorem 4.4 in the form consumed by Proposition 4.8: at every ε > 0 each
moment equals its finite unit-mesh value; the inner-degree exponent is below `4/γ²`. -/
theorem cellMoments_uniform
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 2) :
    (∀ p : ℝ, 1 ≤ p → ∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, GMS4b.locDA ε (η₀ ω) 0 ^ p ∂P =
        ∫⁻ ω, GMS4b.locDA 1 (η₀ ω) 0 ^ p ∂P ∧
        ∫⁻ ω, GMS4b.locDA 1 (η₀ ω) 0 ^ p ∂P < ⊤) ∧
    (∀ p : ℝ, 1 ≤ p → p < 4 / γ ^ 2 → ∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, ((GMS4b.locDegIn ε (η₀ ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P =
        ∫⁻ ω, ((GMS4b.locDegIn 1 (η₀ ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P ∧
        ∫⁻ ω, ((GMS4b.locDegIn 1 (η₀ ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P < ⊤) ∧
    (∀ p : ℝ, 1 ≤ p → ∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, ((GMS4b.locDegOut ε (η₀ ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P =
        ∫⁻ ω, ((GMS4b.locDegOut 1 (η₀ ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P ∧
        ∫⁻ ω, ((GMS4b.locDegOut 1 (η₀ ω) 0 : ℕ∞) : ℝ≥0∞) ^ p ∂P < ⊤) ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ ω, 1 ≤ GMS4b.locDegIn ε (η₀ ω) 0) :=
  GMS4b.theorem44_holds D.measurable_curves.2.2.1
    (IGLaw.IsMatingOfTreesCoupling.curveScaleInvariant D hγ) (unitMoments D)

/-- The localized `u_*` moment used in Proposition 4.8 has a uniform finite bound. -/
theorem uStarMoments_uniform
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 2) :
    ∀ p : ℝ, 1 ≤ p → p < 4 / γ ^ 2 → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ε : ℝ, 0 < ε →
      ∫⁻ ω, GMS4b.locUStar ε (η₀ ω) 0 ^ p ∂P ≤ C :=
  GMS4b.theorem44_uStar_holds D.measurable_curves.2.2.1
    (IGLaw.IsMatingOfTreesCoupling.curveScaleInvariant D hγ) (unitMoments D)

end MatedCRTHarmonic.CellScaling.ZeroConeScaling
