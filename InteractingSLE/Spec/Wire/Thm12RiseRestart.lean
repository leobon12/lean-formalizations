/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12DawnExpanded
import InteractingSLE.Spec.Sec5.CfNextPositive

/-!
# Restart charts with their reduced word and image-field moments already proved

PROVE-WIRE-PARTA. CfNext constructs the positive-prefix chart with the exact
word classification and integrability. Locality is requested on those same
chosen objects; no identification with a previous existential choice is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Wire.Rise
open Sec5 Sec5.CfGiven Exist.Staged Exist.StagedLaw WholeField Restart Restart.DomainMarkov.K2

/-- The proved positive-time data, including the classified reduced word and moments. -/
def ChartReady {Ω : Type u} [MeasurableSpace Ω] (κ : ℝ) (P : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) (R : Ω → RecData) (η : Ω → ℝ≥0 → ℂ)
    (d : Night.ChartData Ω) : Prop :=
  Night.ChartBase κ P h R η d ∧
  (∀ᵐ ω ∂P, ∃ c : BoundaryWord,
    FCDet.IsFlowType (16 / κ) 0 c (d.left ω) (d.right ω) d.rhoL d.rhoR) ∧
  ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => imgField κ (R ω) (h ω) φ) P

def PositiveReadyStatement : Prop :=
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
    ∃ d, ChartReady κ P h (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) η d

/-- Clearance Part A and its restricted reference provide every positive-time
chart fact except the physical member identity. -/
theorem positiveReadyStatement (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) : PositiveReadyStatement.{u} := by
  intro κ b J Ω mΩ hSB P hP h W ζ hκ hκ4 hb hh hcf hζ hleft hright θ hθ D hDm hDreg hD s hs η hη
  obtain ⟨𝓐, nL, nR, rhoL, rhoR, left, right, V, γ, h𝒢, hxL, hxR, hxL0, hxR0,
    hxLa, hxRm, hV0, hVc, hVa, hthr, hword, hint, hchart, hpath⟩ :=
    CfNext.exists_reduced_chartConst_omega hA href hκ hκ4 hb hh.1 hcf hζ
      hleft hright hθ hDm hDreg hD hs hη
  exact ⟨⟨𝓐, nL, nR, rhoL, rhoR, left, right, V, γ⟩,
    ⟨h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hV0, hVc, hVa, hthr, hchart, hpath⟩,
    hword, hint⟩

def ReadyLocalOn (hBase : PositiveReadyStatement.{u}) : Prop :=
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
    HasSafeMembers P d.filtration univ (fun _ => ⊤) d.driver (fun ω => imgField κ ((fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) ω)
      (h ω))

/-- Assemble the full chart statement from physical locality on the newly
constructed reduced data and the separate zero-prefix chart. -/
theorem cfGivenChart_of_ready (hBase : PositiveReadyStatement.{u})
    (hLoc : ReadyLocalOn hBase) (hZero : Night.ZeroChartStatement.{u}) : CfGivenChartStatement.{u} := by
  intro κ b J Ω mΩ hSB P hP h W ζ hκ hκ4 hb hh hcf hζ hleft hright θ hθ D hDm hDreg hD s η hη
  by_cases hz : s = 0
  · subst s
    exact hZero κ b J P h W ζ hκ hκ4 hb hh hcf hζ hleft hright θ hθ D hDm hDreg hD η hη
  · have hs : 0 < s := lt_of_le_of_ne (zero_le : 0 ≤ s) (Ne.symm hz)
    let d := Classical.choose
      (hBase κ b J P h W ζ hκ hκ4 hb hh hcf hζ hleft hright θ hθ D hDm hDreg hD s hs η hη)
    obtain ⟨hbase, hword, hint⟩ := Classical.choose_spec
      (hBase κ b J P h W ζ hκ hκ4 hb hh hcf hζ hleft hright θ hθ D hDm hDreg hD s hs η hη)
    obtain ⟨h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hV0, hVc, hVa, hthr, hchart, hpath⟩ := hbase
    exact ⟨d.filtration, d.nL, d.nR, d.rhoL, d.rhoR, d.left, d.right, d.driver, d.trace,
      h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hV0, hVc, hVa, hthr, hword, hint, hchart,
      hLoc κ b J P h W ζ hκ hκ4 hb hh hcf hζ hleft hright θ hθ D hDm hDreg hD s hs η hη, hpath⟩

end InteractingSLE.Wire.Rise

namespace InteractingSLE.Wire

/-- The proved ready charts at universe zero, with A.1's two seed families as the only inputs. -/
theorem rise_positiveReady
    (hSeedG : ∀ κ, ZhanGT4.A1G3Calc.A1DualCouplingG3SeedGStatement κ)
    (hSeed : ∀ κ, ZhanGT4.A1EightSeed.A1DualCouplingEightSeedMStatement κ) :
    Rise.PositiveReadyStatement.{0} := by
  have hA := late_partAInputs (late_coreG3 (night_rectG3 (dawn_fieldG3 hSeedG)))
    (late_coreEight (night_rectEight hSeed))
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 hA
  exact Rise.positiveReadyStatement hA (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411)

end InteractingSLE.Wire
