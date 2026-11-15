/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71TMain
import InteractingSLE.Spec.Sec7.Lemma71R
import InteractingSLE.Spec.Sec7.Lemma71FixedChart
import InteractingSLE.Spec.Sec7.Lemma71PinMain

/-!
# Lemma 7.1's chain without `MidRealOffStatement`

Packet PROVE-LEMMA71T. With `midRealOffStatement` proved (`Lemma71TMain`), the reductions of PROVE-LEMMA71P/Q/R/S
no longer need the deterministic named input `Lemma71P.MidRealOffStatement`. This file states them without it:

* `middleLandingStatement` (`Lemma71Q.MiddleLandingStatement`, no hypotheses);
* (CS) `pocketCurveSideStatement`, `exists_isPocketChartData`, the pocket clause `pocketClauseStatement`
  (from the §4.2 reference `Lemma71H.Cond44ReferenceStatement`);
* Lemma 7.1's joint law `lemma71JointStatement` (from the three-curve space's inputs `Cond44ReferenceStatement`,
  `Prop55HalfPlaneStatement`, `Lemma613ContactStatement`);
* Proposition 7.4's input `lemma71FixedChartStatement` and Theorem 1.3's `lemma71PocketPinStatement`.

R43/R48: nothing here takes Theorem 1.2/1.3, `Theorem12ParamStatement` or `Theorem13Statement` as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71T

open QuantumZipper (chiC)
open MartChar Coupling Lemma71C Lemma71E Lemma71I Lemma71K Lemma71L Lemma71M Lemma71N Sec6 LocalSets

/-- PROVE-LEMMA71Q's geometric input `MiddleLanding`, with no hypotheses. -/
theorem middleLandingStatement : Lemma71Q.MiddleLandingStatement :=
  Lemma71P.middleLandingStatement_of_midRealOff midRealOffStatement

/-- (CS), the side limits of the middle curve, from the §4.2 reference. -/
theorem pocketCurveSideStatement (href : Lemma71H.Cond44ReferenceStatement.{u}) :
    Lemma71N.PocketCurveSideStatement.{u} :=
  Lemma71R.pocketCurveSideStatement_of_midRealOff href midRealOffStatement

/-- The pocket chart data of Lemma 7.1, from the §4.2 reference. -/
theorem exists_isPocketChartData (href : Lemma71H.Cond44ReferenceStatement.{u}) {κ θ₁ θ₂ a b : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
    (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a) (hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}
    (hpc : IsPocketConstruction P β α γ C c γ') :
    ∃ n : Ω → ℤ, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n ∧
      Lemma72B.IsPocketChartData κ θ₁ θ₂ P β α γ h
        (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
          (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P)
        γ' (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω))
        (fun ω => shiftLift (c ω) (n ω)) 0 (chiC κ) :=
  Lemma71R.exists_isPocketChartData_of_midRealOff href midRealOffStatement hκ hκ4 hθ₁ hθ₂ ha hb hS hpc

/-- The fixed-time pocket clause, from the §4.2 reference. -/
theorem pocketClauseStatement (href : Lemma71H.Cond44ReferenceStatement.{u}) :
    Lemma72E.PocketClauseStatement.{u} :=
  Lemma71R.pocketClauseStatement_of_midRealOff href midRealOffStatement

/-- Lemma 7.1's joint law, from the three-curve space's inputs. -/
theorem lemma71JointStatement (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hMD : Lemma71I.Lemma613ContactStatement.{u}) :
    Lemma72.Lemma71JointStatement.{u} :=
  Lemma71R.lemma71JointStatement_of_midRealOff href h55 hMD midRealOffStatement

/-- Proposition 7.4's input `Lemma71FixedChartStatement`, from the §4.2 reference. -/
theorem lemma71FixedChartStatement (href : Lemma71H.Cond44ReferenceStatement.{u}) :
    Prop74B.Lemma71FixedChartStatement.{u} :=
  Lemma71S.lemma71FixedChartStatement_of_midRealOff href midRealOffStatement

/-- Theorem 1.3's `Lemma71PocketPinStatement`, from the three-curve space's inputs. -/
theorem lemma71PocketPinStatement (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hMD : Lemma71I.Lemma613ContactStatement.{u}) :
    Lemma71F.Lemma71PocketPinStatement.{u} :=
  Lemma71S.lemma71PocketPinStatement_of_midRealOff href h55 hMD midRealOffStatement

end InteractingSLE.Sec7.Lemma71T

end
