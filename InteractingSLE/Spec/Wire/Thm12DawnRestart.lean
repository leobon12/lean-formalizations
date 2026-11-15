/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NightRestart
import InteractingSLE.Spec.Sec5.CfFinishSeparated

/-!
# The restart word reduction from strict separation of the raw marks

PROVE-WIRE-PARTA. Ordered erasure and inverse boundary-word classification are
proved by CfFinish. Only strict separation and the distinguished zero marks
remain as the geometric input; no force-word classification is assumed here.
-/

set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Wire.Dawn
open Sec5 Sec5.CfGiven Exist.Staged Exist.StagedLaw WholeField

/-- Raw chart marks contain their zero seeds and are strictly ordered almost surely. -/
def ChartSeparated {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (d : Night.ChartData Ω) : Prop :=
  ∃ (hL : 0 < d.nL) (hR : 0 < d.nR), ∀ᵐ ω ∂P,
    StrictAnti (d.left ω) ∧ StrictMono (d.right ω) ∧
      d.left ω ⟨0, hL⟩ = 0 ∧ d.right ω ⟨0, hR⟩ = 0

/-- The deterministic erasure and the classified word follow from raw separation. -/
theorem chartReduction_of_separated {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} (hκ : 0 < κ) (d : Night.ChartData Ω) (hs : ChartSeparated P d) :
    Night.ChartReduction κ P d := by
  rcases d with ⟨𝓕, nL, nR, rhoL, rhoR, left, right, driver, trace⟩
  rcases hs with ⟨hL, hR, hs⟩
  cases nL with
  | zero => simp at hL
  | succ nL =>
    cases nR with
    | zero => simp at hR
    | succ nR =>
      obtain ⟨kL, kR, eL, eR, _, _, heL, heR, hword⟩ :=
        CfFinish.exists_erasure_flowType_ae (div_pos (by norm_num) hκ : 0 < 16 / κ) rhoL rhoR hs
      exact ⟨kL + 1, kR + 1, eL.toEmbedding, eR.toEmbedding,
        eL.strictMono, eR.strictMono, heL, heR, hword⟩

def ConvertedSeparationOn (hBase : Night.PositiveChartBaseStatement.{u}) : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    ∀ (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J),
    ∀ (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤),
    ∀ hleft : (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ),
    ∀ hright : (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ),
    ∀ (θ₀ : ℝ) (hθ : θ₀ ∈ Icc (-(π / 2)) (π / 2)), ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ (hDm : Measurable D) (hDreg : ∀ ω,
      IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2)),
    ∀ (t₀ : ℝ≥0) (ht₀ : 0 < t₀) (η : Ω → ℝ≥0 → ℂ)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)),
let d := Classical.choose (hBase κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ hleft hright θ₀ hθ D hDm hDreg hD t₀ ht₀ η hη);
    ChartSeparated P d

/-- Source-setting strict separation supplies the previous word-reduction leaf. -/
theorem convertedReduction_of_separated (hBase : Night.PositiveChartBaseStatement.{u})
    (hs : ConvertedSeparationOn hBase) : Night.ConvertedReductionOn hBase := by
  intro κ b J Ω mΩ hSB P hP h W ζ hκ hκ4 hb hh hcf hζ hleft hright θ hθ D hDm hDreg hD s hs' η hη
  exact chartReduction_of_separated hκ _
    (hs κ b J P h W ζ hκ hκ4 hb hh hcf hζ hleft hright θ hθ D hDm hDreg hD s hs' η hη)

end InteractingSLE.Wire.Dawn
