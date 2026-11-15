/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71PWire
import InteractingSLE.Spec.Sec7.Lemma71QClause

/-!
# Lemma 7.1 reductions from the deterministic middle boundary statement

Packet PROVE-LEMMA71R. This file connects the deterministic Loewner boundary statement from PROVE-LEMMA71P to the
already proved reductions for (CS), `IsPocketChartData`, the fixed-time pocket clause, and Lemma 7.1's joint law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71R

open QuantumZipper (chiC)
open MartChar Coupling Lemma71C Lemma71E Lemma71I Lemma71K Lemma71L Lemma71M Lemma71N Sec6 LocalSets

/-- The side-limit statement (CS), conditional on the deterministic boundary fact and the §4.2 reference. -/
theorem pocketCurveSideStatement_of_midRealOff (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hoff : Lemma71P.MidRealOffStatement) : Lemma71N.PocketCurveSideStatement.{u} :=
  Lemma71Q.pocketCurveSideStatement_of_middleLanding href (Lemma71P.middleLandingStatement_of_midRealOff hoff)

/-- The pocket chart data conclusion, conditional on the deterministic boundary fact and the §4.2 reference. -/
theorem exists_isPocketChartData_of_midRealOff (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hoff : Lemma71P.MidRealOffStatement) {κ θ₁ θ₂ a b : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
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
  Lemma71Q.exists_isPocketChartData_of_middleLanding href
    (Lemma71P.middleLandingStatement_of_midRealOff hoff) hκ hκ4 hθ₁ hθ₂ ha hb hS hpc

/-- The fixed-time pocket clause, conditional on the deterministic boundary fact and the §4.2 reference. -/
theorem pocketClauseStatement_of_midRealOff (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hoff : Lemma71P.MidRealOffStatement) : Lemma72E.PocketClauseStatement.{u} :=
  Lemma71Q.pocketClauseStatement_of_middleLanding href (Lemma71P.middleLandingStatement_of_midRealOff hoff)

/-- Lemma 7.1's joint law, conditional on the deterministic boundary fact and its three named inputs. -/
theorem lemma71JointStatement_of_midRealOff (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hMD : Lemma71I.Lemma613ContactStatement.{u})
    (hoff : Lemma71P.MidRealOffStatement) : Lemma72.Lemma71JointStatement.{u} :=
  Lemma71Q.lemma71JointStatement_of_middleLanding href h55 hMD
    (Lemma71P.middleLandingStatement_of_midRealOff hoff)

end InteractingSLE.Sec7.Lemma71R

end
