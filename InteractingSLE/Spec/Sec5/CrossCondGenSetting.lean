/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondTheta
import InteractingSLE.Spec.Exist.DetField
import InteractingSLE.Spec.Supplement.GW0

/-!
# The cross-conditioning setting with a merely admissible counterflow word

Packet PROVE-CROSSCOND-GEN. Here admissibility means the actual canonical counterflow word has
side partial sums strictly greater than `-2`, as in GW2. It does not mean the stronger
`Sec4.HasAdmissiblePartialSums`, whose lower bound is `k / 2 - 2`.

GW0 gives infinite lifetime under these strict `-2` bounds. Theorem 1.3, explicitly an input
per this packet's Theorem 1.4 scope, gives the complete continuous transient trace. Consequently
the decoded counterflow history is good without `CfThetaBounds`, including in the general-angle
glued setting. The original flow word is arbitrary; no `Cond44` assumption appears here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond.Gen

open WangWu LawUnique GlueCond Cond44Ref CfRegQ Prop411Q Theta Sec7.StripSysField

/-- The canonical counterflow word has every side partial sum strictly above `-2`.
Unlike the noncollision bounds, this permits contacts with the original boundary. -/
def CounterflowAdmissible (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) : Prop :=
  (∀ i : Fin (flowLineNL (counterflowData κ b) (counterflowJumps J) 0),
    -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i),
      flowLineRhoL (16 / κ) (counterflowData κ b) (counterflowJumps J) 0 0 l) ∧
  ∀ i : Fin (flowLineNR (counterflowData κ b) (counterflowJumps J) 0),
    -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i),
      flowLineRhoR (16 / κ) (counterflowData κ b) (counterflowJumps J) 0 0 l

/-- **Counterflow regularity from ordinary admissibility and Theorem 1.3.** The lifetime,
continuous driver and complete transient generating trace are obtained without barrier bounds. -/
theorem ae_counterflow_regular_of_admissible (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hadm : CounterflowAdmissible κ b J)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ W 0 ω = 0 ∧ Continuous (W · ω) ∧
      ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (W · ω) ⊤ γ ∧
        Tendsto (fun t => ‖γ t‖) atTop atTop := by
  obtain ⟨_, _, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hh hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  have hord := Theorem15.isOrderedForceWord_flowLine (counterflowData κ b) (counterflowJumps J) 0
  have hζ := Theorem14.GW0.ae_lifetime_eq_top_of_neg_two_lt hord
    (fun i _ => hadm.1 i) (fun i _ => hadm.2 i) hC.1
  have hκ' : 0 < 16 / κ := by positivity
  filter_upwards [hζ, h13 hκ' hord hC.1, hC.1.2.2.2.2] with ω hζω ⟨_, γ, hγ, hγtrans⟩ hp
  refine ⟨hζω, hp.1, ?_, γ, ?_, hγtrans hζω⟩
  · have hc := hp.2.2.2.1
    rw [hζω] at hc
    exact continuousOn_univ.1 (hc.mono fun _ _ => ENNReal.coe_lt_top)
  · rwa [hζω] at hγ

section Glued

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **General-angle counterflow regularity on its own space.** Only admissibility of the
counterflow's actual word is needed; the flow-side word need not satisfy (4.4). -/
theorem ae_cfReg_of_admissible (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ)
    (hadm : CounterflowAdmissible κ
      (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂) :
    ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous (W₂ · ω) ∧
      ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (W₂ · ω) ⊤ γ ∧
        Tendsto (fun t => ‖γ t‖) atTop atTop := by
  have hb := isPiecewiseConstant_forceData κ ρL ρR xL xR (-(θ * chiC κ))
  have hh : IsGFFWithBoundaryData P h (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) :=
    ⟨hC.2.1, hC.2.2.1⟩
  have hh' := isGFFWithBoundaryData_flowField_zero hh (-(θ * chiC κ))
  rw [← coe_forceJumpFinset] at hh'
  have hh₂ := isGFFWithBoundaryData_of_map_eq hh' (measurable_of_isCenteredCounterflowDriver hcf) hlaw
  exact ae_counterflow_regular_of_admissible h13 hκ hb hadm hh₂ hcf

/-- Good decoded counterflow histories under the strict `-2` partial-sum hypothesis. -/
theorem ae_cfHistory_mem_goodCfSet_of_admissible (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ)
    (hadm : CounterflowAdmissible κ
      (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂) :
    ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodCfSet := by
  filter_upwards [ae_cfReg_of_admissible h13 hκ hadm hC hcf hlaw]
    with ω ⟨hζ, hw0, hw, γ, hγ, _⟩
  exact cfHistory_mem_goodCfSet hζ hw hw0 hγ

end Glued

end InteractingSLE.Sec5.CrossCond.Gen
