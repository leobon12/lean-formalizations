/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma47AnglePass
/-!
# Lemma 4.7 at a relative angle: word entrance

The angle-independent stopped-data and Galmarino lemmas `marks47_inter` and
`marks47_avoid` discharge the measurability clauses. The existing killed-word
converse supplies a Brownian motion in the product filtration.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Sec5.Lemma47Angle
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q MartChar WholeField CrossCond.Theta
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
section Final

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The martingale clause of the counterflow's killed image word** (item D3, PROVE-CFRESTART4's hypothesis `hmart`),
given that almost every glued sample is good. -/
theorem isLocalMartingaleBefore_q_of_good_angle (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hae : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      IsGood47 W VL VR ζ p) {s : ℝ≥0} (hs : 0 < s) :
    ∀ z ∈ H, IsLocalMartingaleBefore (qFilt (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
        ((measurable_cfFieldT κ θ).comp hC.2.1)) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR) W VL VR ζ s
        (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))
      (fun p => min (QuantumZipper.swallowTime (wpath (qW W VL VR ζ s (glueGood47 (glueMeasure P k
          (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ)) p) z : WithTop ℝ≥0)
        (qT W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) p))
      (coupProc (16 / κ) (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR)
        (qW W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ))
        (qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ))
        (qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ)) z) :=
  isLocalMartingaleBefore_q_angle hκ hκ4 hF h44 hθb hC hcf hlaw k hk hae hs
    (fun r _ _ ht'0 ht't ht _ hA => marks47_inter _ _ ht isGood47_of_mem_glueGood47 (ae_mem_glueGood47 hae) r
      ht'0 ht't hA)
    (fun _ ht φ => marks47_avoid ht isGood47_of_mem_glueGood47 (ae_mem_glueGood47 hae) φ)

/-- **The word entrance of the counterflow's killed image word** (items D3 + D4): on `μ ⊗ P₀` there is a Brownian
motion of the product filtration driving, almost surely, the integrated `SLE_{16/κ}(ρ′)` equations of the killed image
word on `[0, qT)` (weights `iwL`, `iwR`), given that almost every glued sample is good. -/
theorem exists_isWordEntrance_q_angle (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hae : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      IsGood47 W VL VR ζ p) {s : ℝ≥0} (hs : 0 < s) :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (Bi : ℝ≥0 → (Ω × HistorySpace 0 0) × Ω₀ → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration (qFilt (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
        ((measurable_cfFieldT κ θ).comp hC.2.1)) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR) W VL VR ζ s
        (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ))
        𝓦) Bi ((glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)).prod P₀) ∧
      (∀ p, Continuous fun t => Bi t p) ∧
      ∀ᵐ p ∂((glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)).prod P₀),
        Sec7.Aux117.IsWordEntrance (16 / κ)
          (fun i => qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) i 0 p.1)
          (fun j => qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) j 0 p.1)
          (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR)
          (fun t => qW W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) t p.1)
          (fun i t => qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) i t p.1)
          (fun j t => qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) j t p.1) (fun t => Bi t p)
          (qT W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) p.1 : ℝ≥0∞) := by
  have hxo := isOrderedForceWord_qx_angle κ θ ρL ρR xL xR
  exact exists_isWordEntrance_of_mart47 hC.2.2.2.1 hxo.2.1 hxo.1 hxo.2.2.2 hxo.2.2.1 hs hae (by positivity)
    (isLocalMartingaleBefore_q_of_good_angle hκ hκ4 hF h44 hθb hC hcf hlaw k hk hae hs)

end Final
end InteractingSLE.Sec5.Lemma47Angle
