/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedDepthMean

/-!
# Proposition 5.9 at depth `ℓ`: the staged conditional characteristic function on the glued space (S2, (SW3))

Packet PROVE-STAGED-DEPTH. The characteristic-function form of `ae_stage_meanIdent`: the conditional law of the field
given the staged prefix (to the end of piece `n` of a fixed schedule), the stopped counterflow and the marks is the
Gaussian law with the image stage word's mean in the counterflow chart and the Green covariance of the complement of
the union — Astra's (SW3) at a deterministic own time, the input of the chart clause of S3 (the staged analogue of
CROSSCOND-THETA's `ae_condExp_cfGlue_eq_cfFT`).

* **`ae_stage_charIdent`**.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the only named input is
`Theorem12ParamCond44Statement` (R74).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open QuantumZipper.RS (shiftDrive)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedDepth

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets
open ImgDrv MartChar MartChar.RealFlow Restart.RetAux79 Sec7.StripSysField GlueImg Word49 Theta StagedFinal
open Restart Exist.StagedLaw Exist.Staged Theorem14.GW2Schedule
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule StagedGlue StagedCand
open Sec7.Lemma71C (capClock)
open CrossCond.Staged (stageGood stageDrv catN cumT)

section Char

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {hs : Ω → DistOn upperHalfPlaneOpens} {us : ℂ → ℝ}

include h44 hκ hκ4 in
/-- **S2 in characteristic-function form** ((SW3) of Astra's follow-up 4 §3.1 at a fixed own time, for the image of
the staged prefix): under the hypotheses of `ae_stage_meanIdent`, almost surely on the same event the conditional
characteristic value of `h(φ)` given the germs of the union and the marks is
`exp(i ∫ (u_I ∘ f′_T ∘ Ψ − (θ_n − θ₀) χ − χ (arg f′_T′ ∘ Ψ + arg Ψ′)) φ) · exp(−½ G_{ℍ ∖ U}(φ, φ))`. -/
theorem ae_stage_charIdent (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hcs : ∀ ω, WholeField.centredField hs us ω = WholeField.centredField h u₀ ω)
    (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀) (hh : IsGFFWithBoundaryData P hs c₀.fn c₀.jumps)
    (hus : IsBoundedHarmonicExtension c₀.fn c₀.jumps us) (sc : Schedule)
    (hu₀s : ∀ z, u₀ z = us z + schedAngle (scheduleList sc) 0 * chiC κ)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P hs (scheduleSpec sc) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {n : ℕ} (hn : n + 1 ≤ schedL sc) {s : ℝ≥0} (hs0 : 0 < s) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u')
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s
        (fun _ => ⊤) (joinProc sc E) →
      ((cumT (schedD sc) n : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) (joinProc sc E)
        (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s
          (fun _ => ⊤) (joinProc sc E)) p →
      tsupport φ ⊆ H \ (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2) →
      ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧
        EqOn W' (chainDrv (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
            (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) p)
          (gPre s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
            (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) p))
          (Icc 0 (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
            (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) p)
            ((cumT (schedD sc) n : ℝ≥0) : ℝ))) ∧
        ∀ uI : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ
            (imgStageRhoL κ θ ρL (fun j => schedAngle (scheduleList sc) j - schedAngle (scheduleList sc) 0) n)
            (imgStageRhoR κ θ ρR (fun j => schedAngle (scheduleList sc) j - schedAngle (scheduleList sc) 0) n)
            (imgStageVL xL (cfDrv0 s p.2) s W' (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood
              (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) n : ℝ≥0) : ℝ))
              (fun m => capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
                (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                  (joinProc sc E)) p)
                (startT (recSeqT (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1)) m)) n)
            (imgStageVR xR (cfDrv0 s p.2) s W' (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood
              (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) n : ℝ≥0) : ℝ))
              (fun m => capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
                (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                  (joinProc sc E)) p)
                (startT (recSeqT (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1)) m)) n))
          (forceJumpSet
            (imgStageVL xL (cfDrv0 s p.2) s W' (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood
              (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) n : ℝ≥0) : ℝ))
              (fun m => capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
                (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                  (joinProc sc E)) p)
                (startT (recSeqT (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1)) m)) n)
            (imgStageVR xR (cfDrv0 s p.2) s W' (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood
              (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) n : ℝ≥0) : ℝ))
              (fun m => capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
                (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                  (joinProc sc E)) p)
                (startT (recSeqT (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1)) m)) n)) uI →
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
            fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
            germSigma (fun p : Ω × HistorySpace 0 0 =>
                recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)
              (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔
            ((inferInstance : MeasurableSpace (PastData (n + 1))).prod (stopSigma s)).comap
              (fun p : Ω × HistorySpace 0 0 => (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1, p.2))] p =
          Complex.exp (Complex.I * ((∫ z, ((uI (fwdMap W' (capClock (gCurve s (fun _ => ⊤) (joinProc sc E)
            (glueGood (glueMeasure P k
              (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) n : ℝ≥0) : ℝ)) (revChart (cfDrv0 s p.2) s z)) -
              (schedAngle (scheduleList sc) n - schedAngle (scheduleList sc) 0) * chiC κ) -
            chiC κ * ((logDerivFwd W' (capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
              (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) n : ℝ≥0) : ℝ)) (revChart (cfDrv0 s p.2) s z)).im +
              (logDerivPsi (cfDrv0 s p.2) s z).im)) * φ z : ℝ) : ℂ)) *
            ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov (H \ relClosureH
              (recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)) φ φ) :
              ℝ) : ℂ) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set 𝓖 : MeasurableSpace (Ω × HistorySpace 0 0) := germSigma (fun p : Ω × HistorySpace 0 0 =>
                recHull sc n (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1) ∪ cfHullQ s p.2)
              (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔
            ((inferInstance : MeasurableSpace (PastData (n + 1))).prod (stopSigma s)).comap
              (fun p : Ω × HistorySpace 0 0 => (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (n + 1) p.1, p.2)) with h𝓖
  set F : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens := fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))
    with hFdef
  -- the constant `e^{i ∫ 𝔥₀ φ}` is pulled out
  set c : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) with hc
  have e : (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) =
      c • fun p => Complex.exp (Complex.I * (F p φ : ℂ)) := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, hc, hFdef, cenTT_cfFieldT, ← Complex.exp_add]
    rw [show h p.1 - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ =
      WholeField.centredField h u₀ p.1 from rfl, WholeField.centredField_apply h hu₀.1 p.1 φ]
    congr 1
    push_cast
    ring
  have hpull := condExp_smul (μ := μ) c (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (F p φ : ℂ))) 𝓖
  rw [← e] at hpull
  have hmean := ae_stage_meanIdent h44 hκ hκ4 hC hθb hcf hlaw hk hu₀ hxL hxR hcs c₀ hc₀ hh hus sc hu₀s hE hreg hn hs0
    hu' φ
  have hside := ae_stage_sideS h44 hκ hκ4 hC hθb hcf hlaw hk hu₀ hcs c₀ hc₀ hh hus sc hE hreg hn s hu' φ
  filter_upwards [hpull, hmean, hside] with p hp hm ⟨w, _, hch, _⟩ hpE htP hφ
  obtain ⟨W', hW', hW'0, hEq, hmain⟩ := hm hpE htP hφ
  refine ⟨W', hW', hW'0, hEq, fun uI hu => ?_⟩
  rw [hp, Pi.smul_apply, smul_eq_mul, hch, ← hmain uI hu, hc, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Char

end InteractingSLE.Sec5.CrossCond.StagedDepth
