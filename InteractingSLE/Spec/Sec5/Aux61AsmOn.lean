/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61AsmCover

/-!
# The assembled fibre cover in every small-gap window setting (Theorem 1.2's fibre leaf)

Packet PROVE-AUX61-ASSEMBLE. At the binders of `Aux61UnionK.GluedLocalCoverOn` (the θ-glued space of the
flow line and the counterflow, a rational restart time and window code, a rational counterflow time), explicit
data `AsmDataOn` and the named facts `AsmFactsOn` give `GluedLocalCoverOn`, hence the corrected dyadic fibre
cover `DyActFibreCoverOn (¬ IsLargeGap) RefWin` consumed by Theorem 1.2's Prop 5.1 (E1) route.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Asm

open Sec4 Sec5.Aux61Cov Sec5.Prop51G Sec5.Aux61Kernel Sec5.Cond44Ref Sec5.Aux61Act
open WangWu WholeField LocalSets Restart Exist.StagedLaw LocalExt Coupling LawUnique

universe u

/-- **The explicit assembly data in every small-gap window setting**, on the θ-glued space with its glued
measure. -/
def AsmDataOn : Type (u + 1) :=
  ∀ (t : ℚ) (_c : WinCode), ∀ _ht : 0 < t,
  ∀ κ : ℝ, ∀ (_hκ : 0 < κ) (_hκ4 : κ < 4), ∀ a b θ₁ θ₂ : ℝ, ∀ (_h12 : θ₁ < θ₂) (_hG : ¬ IsLargeGap κ θ₁ θ₂),
    ∀ (_hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    (_ha : sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a),
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      ∀ _hfl : IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ,
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        ∀ _hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂,
        ∀ _hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂,
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          ∀ _hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k,
          ∀ (s : ℚ) (_hs : 0 < s),
            AsmData.{u} (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
              ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))

/-- **The named facts in every small-gap window setting**, for the restart-window event. -/
def AsmFactsOn (D : AsmDataOn.{u}) : Prop :=
  ∀ (t : ℚ) (c : WinCode), ∀ ht : 0 < t,
  ∀ κ : ℝ, ∀ (hκ : 0 < κ) (hκ4 : κ < 4), ∀ a b θ₁ θ₂ : ℝ, ∀ (h12 : θ₁ < θ₂) (hG : ¬ IsLargeGap κ θ₁ θ₂),
    ∀ (hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    (ha : sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a),
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      ∀ hfl : IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ,
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        ∀ hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂,
        ∀ hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂,
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          ∀ hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k,
          ∀ (s : ℚ) (hs : 0 < s),
            AsmFacts (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
              ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
              (fun p => RestartWindowEvent (Prop411Q.cfDrv p.2) s (fun v : ℝ => η p.1 v.toNNReal) t c)
              (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

/-- **The fibre-local cover in every small-gap window setting** from the assembly data and facts. -/
theorem gluedLocalCoverOn_of_asm (D : AsmDataOn.{u}) (hF : AsmFactsOn D) :
    Aux61UnionK.GluedLocalCoverOn.{u} := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  exact localCover_of_asm (D t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hF t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

/-- **Theorem 1.2's fibre leaf**: the corrected dyadic fibre cover in every small-gap window setting, from the
assembly data and facts (consumed by `Aux61Act.fwdNoEastCrosscutTgtQOn_of_dyCover_refWin`). -/
theorem dyCover_of_asm (D : AsmDataOn.{u}) (hF : AsmFactsOn D) :
    DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) RefWin :=
  Aux61UnionK.dyCover_of_localCoverOn (gluedLocalCoverOn_of_asm D hF)

end InteractingSLE.Sec5.Aux61Asm
