/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LMeanRet
import InteractingSLE.Spec.Supplement.GW2SchedRuleSigma
import InteractingSLE.Spec.Supplement.GW2JointKernelProofC

/-!
# GW2's joint (Det) is GB6 at the dual parameter

Packet PROVE-GW2-FABLE. GB9, p. 525. GB6 (a counterflow read relative to a stopped flow prefix) and GW2's joint
(Det) (a flow line read relative to a stopped counterflow prefix) are exchanged by the substitution

`(κ, θ, h, flow line)  ↦  (16/κ, 0, h′, counterflow)`,

where `h′` is the infinity-source transport of `h`. This file proves the three facts that make the substitution
exact, and its first consequence:

* **`isChartTransport_dual`**: the transport relation is an involution — if `h′` is the transport of `h` with the
  coefficients of `κ`, then `h` is the transport of `h′` with the coefficients of `16/κ`;
* **`jointWordOfRec_specOffset`**: GW2's joint word (R62's offset `2πχ`) is GB6's conditional word at `16/κ` and
  angle `0`: `jointWordOfRec (specOffset κ) κ c′ r = gb6WordOfRec (16/κ) 0 c′ r`;
* `cfRec_eq_gb6Rec`: the two records are the same function;
* **`ae_eqOn_retMean_gw2`**: GW2's retained mean. For the stopped counterflow of `h′` (read in the flow's frame as
  the retained set `retSet s W ζ`, the inverted counterflow hull) and every local-set mean `g₁` of it for the
  centred flow-frame field: almost surely, every harmonic representative `w₁` of `g₁` satisfies
  `w₁ + 𝔥⁰ = G₀ ∘ Ψ − χ(κ) Im relLog` with `Ψ = relMap W s` the joint chart's forward map and `G₀` a bounded
  harmonic extension of the joint word. This is `Supp8.GB6LMean.ae_eqOn_retMean` at `16/κ` (it has no `κ < 4`
  hypothesis), read through the three facts above.

R48: Theorems 1.2–1.3 enter as hypotheses (through `Exist.Param12.hasFieldDeterminedHistories`); GW2 serves
Theorem 1.4 only. Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Fb

open Restart Exist.StagedLaw Supp8.GB6 Supp8.Q3Chain Supp8.GB6LineL GW2JointKernel GW2TipSystem LocalSets

/-! ### The transport relation is an involution -/

/-- **The infinity-source transport is an involution**: if `h′` is the transport of `h` with the coefficients
`(−1, −πχ(κ), χ(16/κ))`, then `h` is the transport of `h′` with the coefficients of the dual parameter `16/κ`. -/
theorem isChartTransport_dual {κ : ℝ} (hκ : 0 < κ) {h h' : DistOn upperHalfPlaneOpens}
    (hT : IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) h h') :
    IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC (16 / κ))) (chiC (16 / (16 / κ))) h' h := by
  have e := eq_returnField_of_isChartTransport_R hκ hT
  have h1 := Sec7.StripSysField.isChartTransport_returnField (Real.pi * chiC κ) (chiC κ) h
  rw [← e] at h1
  have e16 : 16 / (16 / κ) = κ := by field_simp
  rw [e16, Sec4.chiC_sixteen_div hκ, mul_neg, neg_neg]
  exact h1

/-! ### The joint word is GB6's conditional word at the dual parameter -/

/-- **GW2's joint word is GB6's conditional word at `16/κ` and angle `0`.** -/
theorem jointWordOfRec_specOffset {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (r : RecData) :
    jointWordOfRec (specOffset κ) κ c' r = gb6WordOfRec (16 / κ) 0 c' r := by
  unfold jointWordOfRec gb6WordOfRec
  rw [retA_add_specOffset hκ, retL, Sec4.chiC_sixteen_div hκ, mul_neg]

/-- The counterflow record of GW2 and the flow record of GB6 are the same function of a driver. -/
theorem cfRec_eq_gb6Rec {Ω : Type*} (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) :
    cfRec s W ζ ω = gb6Rec s W ζ ω := rfl

/-! ### The retained mean -/

/-- **GW2's retained mean** (GB9, p. 525: "the retained counterflow-side collars retain the own counterflow
germs"; the input `hind₁` of the union mean with the counterflow retained). Let `h` be the flow-frame field with data
`(b, J)`, `h′` its infinity-source transport, `(W, ζ)` a counterflow driver of `h′` with the data of the word `c′`,
`𝔥⁰` the bounded harmonic extension of the flow-frame data, and `g₁` a local-set mean of the retained set
`retSet s W ζ` (the inverted counterflow hull at `s`) for `h − 𝔥⁰`. Almost surely on `{s < ζ}`, every harmonic
representative `w₁` of `g₁` off the retained set satisfies `w₁ + 𝔥⁰ = G₀ ∘ Ψ − χ(κ) Im relLog` (`Ψ = relMap W s`) for
every bounded harmonic extension `G₀` of the joint word `jointWordOfRec (specOffset κ) κ c′ (cfRec s W ζ)`. -/
theorem ae_eqOn_retMean_gw2 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    {c' : BoundaryWord} (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (cfData κ b J)
      (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P) (s : ℝ≥0)
    {g₁ : Ω → DistOn upperHalfPlaneOpens}
    (hg₁ : IsLocalSetMean (retSet s W ζ) (WholeField.centredField h u₀) P g₁) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω →
      ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
          (cfData κ (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps)
          (cfJumps (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps) G₀ →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ retSet s W ζ ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ retSet s W ζ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + u₀ z)
            (fun z => G₀ (relMap (fun r : ℝ => W r.toNNReal ω) s z) -
              chiC κ * (Supp8.Q3Rel.relLog (fun r : ℝ => W r.toNNReal ω) s z).im)
            (H \ retSet s W ζ ω) := by
  have hk : (0 : ℝ) < 16 / κ := by positivity
  have e16 : 16 / (16 / κ) = κ := by field_simp
  have hG' : IsGFFWithBoundaryData P h' b' J' :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcf
  have hGc' : IsGFFWithBoundaryData P h' c'.fn c'.jumps := by
    rw [hc'J]
    exact WangWu.isGFFWithBoundaryData_congr (fun y hy => (hc'b y hy).symm) hG'
  have hcfc : IsFlowLineDriver (16 / κ) c'.fn c'.jumps 0 P h' W ζ :=
    (Exist.StagedLaw.isFlowLineDriver_congr_of_eqOn hb' c'.isPiecewiseConstantBoundaryData J' hc'b).2 hcf
  have hdet : LP.HasFieldDeterminedHistories.{u} (16 / κ) (flowLineXL c'.fn c'.jumps 0)
      (flowLineXR c'.fn c'.jumps 0) (flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0)
      (flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0) :=
    Exist.Param12.hasFieldDeterminedHistories h12 h13 hk (Theorem15.isOrderedForceWord_flowLine c'.fn c'.jumps 0)
  have hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC (16 / κ)))
      (chiC (16 / (16 / κ))) (h' ω) (h ω) := fun ω => isChartTransport_dual hκ (hT ω)
  have hu₀' : IsBoundedHarmonicExtension (cfData (16 / (16 / κ)) b J)
      (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀ := by
    rw [e16]
    exact hu₀
  have key := Supp8.GB6LMean.ae_eqOn_retMean (κ := 16 / κ) (θ := 0) hk hGc' hb hG hT' hcfc hdet hu₀' hh0 s hg₁
  simp only [e16] at key
  filter_upwards [key] with ω hω hs G₀ hG₀ w₁ hw₁ hrep
  rw [jointWordOfRec_specOffset hκ, cfRec_eq_gb6Rec] at hG₀
  exact hω hs G₀ hG₀ w₁ hw₁ hrep

end InteractingSLE.Theorem14.GW2Fb
