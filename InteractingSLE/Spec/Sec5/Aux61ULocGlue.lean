/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ULocCore
import InteractingSLE.Spec.Sec5.CrossCondStagedTheta

/-!
# The counterflow hull with the flow hull at an enlarged stop, on the θ-glued space

Packet PROVE-AUX61-UNIONLOC, item (P1) of `planning/handoffs/PROVE-AUX61-CHARTLOC.md`, instantiated on the glued space
of `CrossCond.Theta` (the glued space of `Prop51G.GluedQ` and of `Aux61UnionK.GluedLocalCoverOn` at relative angle
`θ = θ₂ − θ₁ + π/2`, `Prop51GQ.cfField_flowField_eq_cfFieldT`): the root `IsOptionalHullCoupling` (the flow line's
driving coupling, with almost surely infinite lifetime), an independent centred counterflow of `h − θχ` glued through
its kernel `k` given the field.

* **`isHistoryAvoidanceLocal_unionAt_cfGlueT`** (Astra follow-up 4 §1.1, L84–L104): for every counterflow time `s`,
  every stop `T` of the initially enlarged filtration `σ(counterflow record at s) ∨ 𝓕^flow_t` (pulled-back Galmarino
  form, `IsEnlargedStopComap`) and every marks `ℳ` inside `σ(counterflow record at s) ∨ 𝓕^flow_∞`, the union
  `ℍ ∩ (K_s ∪ K̃_T)` of the counterflow hull `K_s` (`GlueCond.cfHullQ s`) and the flow hull at the stop (the regularized
  hull `PocketStopWallsFin.regHull`, equal to the Loewner hull of the flow driver almost surely) satisfies the
  history-marked avoidance criterion for `ℳ`, for the centred field `h − 𝔥₀`.

No determination of either curve by the field is used: the flow side is the frozen coupling's marked locality at its own
stopping times (`PocketStopWallsFin.isHistoryAvoidanceLocal_regHull`), the counterflow side its marked locality at the
deterministic time `s` (`CrossCond.Theta.isHistoryAvoidanceLocal_cfHullQT`), combined by the glue's conditional
independence (`WangWu.condIndepEv_glue_fst`) and `Aux61ULoc.isHistoryAvoidanceLocal_unionAt_comap`.

R48 / R77: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param`, or
Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Aux61ULoc

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ WholeField LocalSets CrossCond.Theta Coupling
open Sec7.PocketStopWallsFin (regHull regHull_mono measurableSet_disjoint_regHull
  measurableSet_disjoint_regHull_stopping isHistoryAvoidanceLocal_regHull)

section Glue

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}

/-- **The counterflow hull with the flow hull at an enlarged stop is history-marked local on the θ-glued space**
(Astra follow-up 4 §1.1; Proposition 3.7 with retained histories at a stop depending on both records). For every
counterflow time `s`, every marks `ℳ` and every stop `T` on the glued space such that `T` is a stop of the initially
enlarged filtration `σ(counterflow record at s) ∨ 𝓕^flow_t` with marks `ℳ` (pulled-back Galmarino form) and the marks
are events of `σ(counterflow record at s) ∨ 𝓕^flow_∞`, the set `ℍ ∩ (K_s ∪ K̃_T)` (on `{T < ∞}`; `ℍ` elsewhere)
satisfies the history-marked avoidance criterion for `ℳ` and the centred field `h − 𝔥₀`. The marks are bound after the
glued facts (a local `MeasurableSpace` on the product would shadow the product instance). -/
theorem isHistoryAvoidanceLocal_unionAt_cfGlueT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (s : ℝ≥0) :
    ∀ (ℳ : MeasurableSpace (Ω × HistorySpace 0 0)) (T : Ω × HistorySpace 0 0 → ℝ≥0∞),
      IsEnlargedStopComap ℳ ((stopSigma s).comap Prod.snd) (drivingFiltration P hC.2.2.2.1) Prod.fst T →
      (∀ M, MeasurableSet[ℳ] M → MeasurableSet[(stopSigma s).comap Prod.snd ⊔
        ⨆ r, (drivingFiltration P hC.2.2.2.1 r).comap Prod.fst] M) →
      @IsHistoryAvoidanceLocal (Ω × HistorySpace 0 0) ℳ Prod.instMeasurableSpace
        (unionAt (fun p => cfHullQ s p.2) (fun r p => regHull W ζ r p.1) T)
        (fun p => centredField h u₀ p.1)
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  have hX := hC.2.2.2.1
  have hX₀ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hh₂m := CfRegQ.measurable_of_isCenteredCounterflowDriver hcf
  have hXm₀ : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hXm : Measurable fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω)) := (measurable_cenTT κ θ u₀).comp hXm₀
  have hY₂m : Measurable (cfHistory W₂ ζ₂) := measurable_cfHistory hX₀
  have hX₂m : Measurable fun ω => cenTT κ θ u₀ (h₂ ω) := (measurable_cenTT κ θ u₀).comp hh₂m
  have hreg₂ := ae_cfRegT hκ hθb hC hcf hlaw
  have hf : (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) =
      fun p => centredField h u₀ p.1 := funext fun p => cenTT_cfFieldT κ θ u₀ (h p.1)
  -- the counterflow's record, transported along the law of `(h − θχ, history)`
  have hlaw₂ : μ.map (fun p : Ω × HistorySpace 0 0 => (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)), p.2)) =
      P₂.map (fun ω => (cenTT κ θ u₀ (h₂ ω), cfHistory W₂ ζ₂ ω)) := by
    have hT : Measurable fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenTT κ θ u₀ r.1, r.2) :=
      ((measurable_cenTT κ θ u₀).comp measurable_fst).prodMk measurable_snd
    have hpair : Measurable fun p : Ω × HistorySpace 0 0 => (cfFieldT κ θ (h p.1), p.2) :=
      (hXm₀.comp measurable_fst).prodMk measurable_snd
    have hpair₂ : Measurable fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω) := hh₂m.prodMk hY₂m
    rw [show (fun p : Ω × HistorySpace 0 0 => (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)), p.2)) =
        (fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenTT κ θ u₀ r.1, r.2)) ∘
          fun p => (cfFieldT κ θ (h p.1), p.2) from rfl,
      show (fun ω => (cenTT κ θ u₀ (h₂ ω), cfHistory W₂ ζ₂ ω)) =
        (fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenTT κ θ u₀ r.1, r.2)) ∘
          fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω) from rfl,
      ← Measure.map_map hT hpair, ← Measure.map_map hT hpair₂, hμ, glueMeasure_map_pair hXm₀ k, hlaw, hk]
  have hA₂ := isHistoryAvoidanceLocal_of_map_eq (𝔐 := stopSigma s) hX₂m hY₂m (hXm.comp measurable_fst)
    measurable_snd hlaw₂ (measurable_cfHullQ s) (stopSigma_le _)
    (isHistoryAvoidanceLocal_cfHullQT hcf hκ hreg₂ hu₀.1 s)
  have hA₂' : IsHistoryAvoidanceLocal ((stopSigma s).comap Prod.snd)
      (fun p : Ω × HistorySpace 0 0 => cfHullQ s p.2) (fun p => centredField h u₀ p.1) μ := by
    rw [← hf]
    exact hA₂
  -- the glue's conditional independence
  have hci := condIndepEv_glue_fst (μ := P) k hXm₀
  rw [← comap_cenTT_glue κ θ u₀ (fun ω => cfFieldT κ θ (h ω)), hf] at hci
  -- the flow side
  have hRC : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  have hμπ : μ.map Prod.fst = P := glueMeasure_fst k hXm₀
  have hh₀ : Measurable (centredField h u₀) := measurable_centredField hC.2.1 u₀
  have hA₂m : Measurable[(stopSigma s).comap Prod.snd, hittingSigma] fun p : Ω × HistorySpace 0 0 => cfHullQ s p.2 :=
    (measurable_image_negInv.comp (CrossCond.measurable_hullAt_stopSigma s)).comp (comap_measurable Prod.snd)
  intro ℳ T hT hS0
  exact @isHistoryAvoidanceLocal_unionAt_comap (Ω × HistorySpace 0 0) Ω mΩ P _ _ _ _ ℳ
    Prod.instMeasurableSpace μ _ (centredField h u₀) hh₀ Prod.fst measurable_fst hμπ
    measurable_fst.comap_le measurable_snd.comap_le (MeasurableSpace.comap_mono (stopSigma_le s)) hci
    (fun p => cfHullQ s p.2) hA₂m hA₂' (drivingFiltration P hX) hRC
    (fun t => MeasurableSpace.comap_mono ((drivingFiltration P hX).le t))
    (fun r ω => regHull W ζ r ω) (regHull_mono W ζ)
    (fun t U hU hUH => measurableSet_disjoint_regHull hC hκ hX hζ t U hU hUH)
    (fun τ hτ hfin U hU hUH => measurableSet_disjoint_regHull_stopping hC hκ hX hζ τ hτ hfin U hU hUH)
    (fun τ hτ hfin => isHistoryAvoidanceLocal_regHull hC hκ hu₀ hX hζ τ hτ hfin) T hT hS0

end Glue

end InteractingSLE.Sec5.Aux61ULoc
