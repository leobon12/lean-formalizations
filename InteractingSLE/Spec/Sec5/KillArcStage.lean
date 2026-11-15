/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.KillArcSwallow
import InteractingSLE.Spec.Sec5.StagedRepStrict

/-!
# `KilledArcSwallowStatement` PROVED; Proposition 5.9's root stage without named inputs

Packet PROVE-KILLARC. PROVE-STAGED-REP's named deterministic input `StagedRep.KilledArcSwallowStatement` (Loewner
swallowing at the first real contact of a killed arc) is proved from `KillArc.killedArc_swallow`
(**`killedArcSwallowStatement`**), so the stopped representation `IsKilledStageRep` of Proposition 5.9's root stage on
the glued space (Proposition 4.9's killed image word, PROVE-STAGED-REP's `exists_isKilledStageRep_img`,
`exists_isKilledStageRep_img'`) holds with no named input: **`exists_isKilledStageRep_img_of_ae_strict`** (the
strict order of the image start as a hypothesis) and **`exists_isKilledStageRep_img_of_strict`** (strictly ordered
flow word).

R48: nothing here (or in the imported route) uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or
any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedRep

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord CrossCond.Word49 MartChar.RealFlow Prop49Exit LawUnique Cond44Ref Prop411Q
open Prop59Stage Prop59Nodes StagedKill StagedKCand

/-- **`KilledArcSwallowStatement` holds** (deterministic Loewner theory, `KillArc.killedArc_swallow`): when a killed
arc's capacity-time trace converges to a real point beyond the outermost mark of one side, the killed driver and the
killed marks have left limits at the terminal capacity and the driver meets that outermost mark. -/
theorem killedArcSwallowStatement : KilledArcSwallowStatement :=
  fun _γ _P hγ _n _m xL xR hxL _ hxR _ _T _x₀ hT hx hlim =>
    KillArc.killedArc_swallow hγ xL xR hxL hxR hT hx hlim

section ImgK

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The stopped representation of Proposition 5.9's root stage on the glued space**, with no named input:
PROVE-STAGED-REP's `exists_isKilledStageRep_img` with `KilledArcSwallowStatement` discharged
(`killedArcSwallowStatement`); the strict order of the image start is a hypothesis (`hstr`). -/
theorem exists_isKilledStageRep_img_of_ae_strict (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s)
    (hstr : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      StrictAnti (fun i => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) s ζ W) i 0 p) ∧
      StrictMono (fun j => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) s ζ W) j 0 p)) :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (Bi : ℝ≥0 → (Ω × HistorySpace 0 0) × Ω₀ → ℝ),
      IsKilledStageRep κ ((glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)).prod P₀)
        (cfPast s Ω₀) univ (jwL cL6 κ ρL) (jwR cR6 κ ρR) (Fin.last nL) (Fin.last nR)
        (fun p => ((0 : ℝ), fun i => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) i 0 p.1,
          fun j => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) j 0 p.1))
        (fun t p => imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) t p.1)
        (fun i t p => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) i t p.1)
        (fun j t p => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) j t p.1) Bi
        (fun p => (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) p.1 : ℝ≥0∞))
        (WholeField.prodFiltration (imgFilt (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W)) 𝓦) Bi :=
  exists_isKilledStageRep_img killedArcSwallowStatement hκ hκ4 hF h44 hC hcf hlaw k hk hs hstr

/-- **The stopped representation of Proposition 5.9's root stage on the glued space**, for a strictly ordered flow
word, with no named input: PROVE-STAGED-REP's `exists_isKilledStageRep_img'` with `KilledArcSwallowStatement`
discharged (`killedArcSwallowStatement`). -/
theorem exists_isKilledStageRep_img_of_strict (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) (hxLs : StrictAnti xL) (hxRs : StrictMono xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (Bi : ℝ≥0 → (Ω × HistorySpace 0 0) × Ω₀ → ℝ),
      IsKilledStageRep κ ((glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)).prod P₀)
        (cfPast s Ω₀) univ (jwL cL6 κ ρL) (jwR cR6 κ ρR) (Fin.last nL) (Fin.last nR)
        (fun p => ((0 : ℝ), fun i => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) i 0 p.1,
          fun j => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) j 0 p.1))
        (fun t p => imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) t p.1)
        (fun i t p => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) i t p.1)
        (fun j t p => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) j t p.1) Bi
        (fun p => (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) p.1 : ℝ≥0∞))
        (WholeField.prodFiltration (imgFilt (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W)) 𝓦) Bi :=
  exists_isKilledStageRep_img' killedArcSwallowStatement hκ hκ4 hF h44 hxLs hxRs hC hcf hlaw k hk hs

end ImgK

end InteractingSLE.Sec5.CrossCond.StagedRep
