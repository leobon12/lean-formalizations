/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A5ClearanceWire
import InteractingSLE.Spec.Sec5.CfLineRegQ
import InteractingSLE.Spec.Sec5.GlueCondHit
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRoute
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRouteStrip
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRouteQ

/-! # Part A clearance variants: regularity

Packet PROVE-WIRE-PARTA. The source proofs use only Aux. lemma 7 from Part A.
These variants replace the two-crosscut input by protected-ray clearance, using
the existing clearance and inverse-boundary API. All other hypotheses and conclusions
are those of the original consumers; the original declarations are unchanged.
-/

set_option autoImplicit false

section

/- Clearance variants of `Sec5/CfLineRegQ`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

open scoped NNReal ENNReal Real

open QuantumZipper (H chiC)

open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CfLineRegQ

open WangWu hiding ratPt exists_ratPt_dist_lt

open LawUnique Cond44Ref Prop411Q CfRegQ

section Word

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

end Word

section Cert

variable {nL nR : ℕ}

end Cert

/-- Clearance variant of `cfLineRegularQStatement_of_partA`; only Aux. lemma 7 is used from Part A. -/
theorem cfLineRegularQStatement_of_partA_of_clearance (hA : PartAInputsSixteenDivOfClearance) : Prop51Q.CfLineRegularQStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ hb ha Ω mΩ P _ h hh Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)) :=
    (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  obtain ⟨mL, mR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hadm, hE⟩ :=
    exists_seed_of_isCenteredCounterflowDriver hκ hb ha hh hcf hlaw
  have hk' : 0 < 16 / κ := by positivity
  have hF : IsOrderedForceWord (fun _ : Fin mL => (0 : ℝ)) (fun _ : Fin mR => (0 : ℝ)) :=
    ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  have h7 := aux7Statement_sixteen_div_of_partA_of_clearance.{u} hA hκ hκ4 _ _ σL σR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hF hadm hE
  have hne := ae_trace_ne_zero_of_seed hk' hadm hE (h7.mono fun _ h => h.2.2)
  have hΩ₂ : ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodRegSet := by
    filter_upwards [h7, hne, hE.2.2.2.2] with ω ⟨hζ, ⟨η, hη⟩, htr⟩ hneω hp
    have hw : Continuous fun t => W₂ t ω := by
      have h := hp.2.2.2.1
      rw [hζ] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    exact cfHistory_mem_goodRegSet hζ hw hp.1 hη (hneω η hη) (htr η hη)
  have hg := ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf) (measurable_cfHistory hX₂) hlaw k hk
    measurableSet_goodRegSet hΩ₂
  filter_upwards [hg] with p hp
  exact reg_of_mem_goodRegSet hp

/-- Clearance variant of `prop51QStatement_of_partA_of_cfAvoidLeft`; only Aux. lemma 7 is used from Part A. -/
theorem prop51QStatement_of_partA_of_cfAvoidLeft_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    (havoid : Prop51Q.CfAvoidLeftQStatement.{u}) : Prop51QStatement.{u} :=
  Prop51Q.prop51QStatement_of_cfAvoidLeft (cfLineRegularQStatement_of_partA_of_clearance hA) havoid

end InteractingSLE.Sec5.CfLineRegQ

end

end

section

/- Clearance variants of `Sec5/GlueCondHit`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric

open scoped NNReal ENNReal Real

open QuantumZipper (H chiC fwdHull)

open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.GlueCond

open WangWu hiding ratPt exists_ratPt_dist_lt continuousAt_negInv

open LawUnique Cond44Ref Prop411Q CfRegQ

open Sec4 (regPath regHull histStop)

section Word

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

end Word

section Hull

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

end Hull

section Bridge

variable {nL nR : ℕ}

end Bridge

section Cert

variable {nL nR : ℕ}

end Cert

section Trans

variable {nL nR : ℕ}

end Trans

/-- Clearance variant of `cfGlueAE_mem_goodTransSet`; only Aux. lemma 7 is used from Part A. -/
theorem cfGlueAE_mem_goodTransSet_of_clearance (hA : PartAInputsSixteenDivOfClearance) : CfGlueAE.{u} fun _ y => y ∈ goodTransSet := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hΩ₂ : ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodTransSet := by
    obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
      exists_admissible_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw
    have h7 := aux7Statement_sixteen_div_of_partA_of_clearance.{u} hA hκ hκ4 _ _ σL σR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hF' hadm hE
    filter_upwards [h7, hE.2.2.2.2, ae_trace_ne_real_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw]
      with ω ⟨hζ, ⟨η, hη⟩, htr⟩ hp hne
    have hw : Continuous fun t => W₂ t ω := by
      have := hp.2.2.2.1
      rw [hζ] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    exact cfHistory_mem_goodTransSet hζ hw hp.1 hη (fun t _ x hx => hne η hη t x hx) (htr η hη)
  exact ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf) (measurable_cfHistory hX₂) hlaw k hk
    measurableSet_goodTransSet hΩ₂

/-- Clearance variant of `ae_lemma45_sixteen_div`; only Aux. lemma 7 is used from Part A. -/
theorem ae_lemma45_sixteen_div_of_clearance (hA : PartAInputsSixteenDivOfClearance) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {mL mR : ℕ}
    {yL : Fin mL → ℝ} {yR : Fin mR → ℝ} {σL : Fin mL → ℝ} {σR : Fin mR → ℝ} {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hF : IsOrderedForceWord yL yR) (hadm : Sec4.HasAdmissiblePartialSums (16 / κ) σL σR yL yR)
    (hE : IsIntegratedSLEEvolution (16 / κ) yL yR σL σR P 𝓕 W VL VR B ζ) (hL : ∃ i, yL i = 0)
    (hR : ∃ i, yR i = 0) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
        (∀ t : ℝ≥0, ∀ x : ℝ, x ≠ 0 → η t ≠ x) ∧ Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain ⟨iL, hiL⟩ := hL
  obtain ⟨iR, hiR⟩ := hR
  have hk' : 0 < 16 / κ := by positivity
  filter_upwards [aux7Statement_sixteen_div_of_partA_of_clearance.{u} hA hκ hκ4 yL yR σL σR P 𝓕 W VL VR B ζ hF hadm hE,
    CfAvoidLeftQ.ae_trace_ne_pos hk' hF hadm hE, CfAvoidLeftQ.ae_trace_ne_neg hk' hF hadm hE]
    with ω ⟨hζ, hex, htr⟩ hRp hLn
  refine ⟨hζ, hex, fun η hη => ⟨fun t x hx => ?_, htr η hη⟩⟩
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · exact hLn η hη t iL x hneg (by rw [hiL]; exact hneg.le)
  · exact hRp η hη t iR x hpos (by rw [hiR]; exact hpos.le)

end InteractingSLE.Sec5.GlueCond

end

end

section

/- Clearance variants of `Supplement/CounterflowNoReturnRoute`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset

open scoped NNReal ENNReal Real

open QuantumZipper (chiC)

universe u

namespace InteractingSLE

namespace CfNoReturn

namespace Route

section Weights

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

end Weights

section Admissible

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

end Admissible

/-- Clearance variant of `counterflowNoReturnAdmStatement_of_partA`; only Aux. lemma 7 is used from Part A. -/
theorem counterflowNoReturnAdmStatement_of_partA_of_clearance (hA : Sec5.PartAInputsSixteenDivOfClearance) :
    CounterflowNoReturnAdmStatement.{u} :=
  counterflowNoReturnAdmStatement_of_aux7 fun _ hκ hκ4 => Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4

end Route

end CfNoReturn

end InteractingSLE

end

end

section

/- Clearance variants of `Supplement/CounterflowNoReturnRouteStrip`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function

open QuantumZipper (H Hbar chiC)

open LQGMetric (DistOn IsZeroBoundaryGFF)

open InteractingSLE.WangWu (negInv)

open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE

namespace Sec5

open Sec4

/-- Clearance variant of `stripCounterflow_trace_mem_H_of_stripGFF_of_partA`; only Aux. lemma 7 is used from Part A. -/
theorem stripCounterflow_trace_mem_H_of_stripGFF_of_partA_of_clearance (hA : PartAInputsSixteenDivOfClearance) {κ x₀ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hdata : IsProp411Data κ x₀ bL bU JL JU)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hG : IsStripGFF κ P h bL bU JL JU)
    (hcf : IsStripCounterflowDriver κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) P h W ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ∈ H :=
  stripCounterflow_trace_mem_H_of_stripGFF_of_aux7 hκ hκ4 (aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4) hdata hG hcf

end Sec5

namespace Sec7.StripPocketPath

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketLeftFrontier
  PocketCoupling StripSideHeightProb

open Exist.Staged (IsRegularDriver)

section NoReturn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

end NoReturn

end Sec7.StripPocketPath

end InteractingSLE

end

end

section

/- Clearance variants of `Supplement/CounterflowNoReturnRouteQ`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv chiC)

open LQGMetric (DistOn TestOn)

open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop49Exit

open WangWu hiding ratPt exists_ratPt_dist_lt

open WangWu.ImgWord CrossCond CrossCond.Word49 MartChar.RealFlow LawUnique Cond44Ref Prop411Q CfRegQ

section NoReturnAdm

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

end NoReturnAdm

section MainAdm

/-- Clearance variant of `prop49QExitStatement_of_partA`; only Aux. lemma 7 is used from Part A. -/
theorem prop49QExitStatement_of_partA_of_clearance (hA : PartAInputsSixteenDivOfClearance) : Prop49QExitStatement.{u} :=
  prop49QExitStatement_of_adm (CfNoReturn.Route.counterflowNoReturnAdmStatement_of_partA_of_clearance hA)

/-- Clearance variant of `prop411QStatement_of_lemma47Q_of_partA`; only Aux. lemma 7 is used from Part A. -/
theorem prop411QStatement_of_lemma47Q_of_partA_of_clearance (h47 : Lemma47QHitStatement.{u}) (hA : PartAInputsSixteenDivOfClearance) :
    Prop411QStatement.{u} :=
  prop411QStatement_of_lemma47Q_of_prop49Q cfRegQStatement h47 (prop49QExitStatement_of_partA_of_clearance hA)

end MainAdm

end InteractingSLE.Sec5.Prop49Exit

end

end
