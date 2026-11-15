/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClausePocket
import InteractingSLE.Spec.Sec7.R7Aux131Word
import InteractingSLE.Spec.Sec7.RefWireAux131Side
import InteractingSLE.Spec.Sec7.R7LeavesExtremal

/-!
# Theorem 1.2's R.7: Aux. lemma 122's retained hypothesis (M) on every pocket test, from R.5 up to a constant phase

Packet PROVE-PHASECLAUSE. Theorem R.7 (`source/spec/p433-480.md` L1051–L1070, pp. 477–478) with Aux. lemmas 122, 131
(`source/spec/p385-432.md` L104–L131, L516–L548) and Astra's follow-up 5 §3.2 (R73, L456–L483).

PROVE-PHASE's named input `PhaseSide.R7PhaseMeansRemaining` asks, on every R.7 pocket test, for R.5 up to a lattice
phase `δ` (1) and Aux. lemma 122's retained hypothesis (M) for the same phase. This file proves (M) from (1) and the
constancy of the phase on the positive lifetime (follow-up 5 (3.2): "lattice-valued, hence constant on the positive
lifetime"), through the walls' marked union law that the counterflow configuration supplies
(`PocketStopMarked.pocketStopWallsLaw_stopHull0_marked`, STRIPSYS43) and the pocket geometry of Aux. lemma 131
(`R7Aux131.r7PocketStop_cfPocket`, `…Inf`):

* `TwoSeedPhaseConstInput(Inf)`: on every test, R.5 up to a phase `δ` with `δ_q = c` almost surely on the live event at
  every `q > 0`;
* **`twoSeedPhaseMeansInput_of_const`**, **`twoSeedPhaseMeansInputInf_of_const`**:
  `PhaseSide.TwoSeedPhaseMeansInput(Inf)` from it (`twoSeedPhaseMeansAt_of_stop`);
* `R7PhaseConstRemaining` (**named input**, replacing `PhaseSide.R7PhaseMeansRemaining`; the premises are the same) and
  **`r7PhaseMeansRemaining_of_const`**;
* **`r7ReferenceStatement_late_const`**: Theorem 1.2's R.7 reference with the side field from R.5 up to a constant
  phase.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PhaseClause

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ

universe u

/-! ### The named input on one walls' event -/

section Defs

variable {Ω : Type*}

/-- **R.5 up to a constant lattice phase on every test of a walls' event** (bounded change pocket): in a
walls-measurable chart branch, R.5's phase word with a phase `δ_q` (`PocketStopPhaseSideLimit`) and the constancy of the
phase on the positive relative lifetime (`δ_q = c` almost surely on the live event at every `q > 0`; follow-up 5 (3.2)).
-/
def TwoSeedPhaseConstInput (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[𝓦] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ) (c : Ω → ℝ),
        (∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A
          (travAll R L r η ψ) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
          (activeCompl A (travAll R L r η ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q) ∧
        ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → δ q ω = c ω

/-- **R.5 up to a constant lattice phase on every test of a walls' event** (pocket opening at the flow seed). -/
def TwoSeedPhaseConstInputInf (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[𝓦] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ) (c : Ω → ℝ),
        (∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A
          (travAllInf R L r η ψ) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
          (activeCompl A (travAllInf R L r η ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q) ∧
        ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → δ q ω = c ω

end Defs

/-! ### (M) on every test of a walls' event -/

section Wire

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PhaseSide.TwoSeedPhaseMeansInput` from R.5 up to a constant phase** (bounded change pocket): the walls' marked
union law at `T⁰(q)` is `PocketStopMarked.pocketStopWallsLaw_stopHull0_marked` (the walls are field-determined and
entrance-local flow lines of the counterflow's frozen coupling, as in `R7Aux131.twoSeedWallsInput_of_sideLimit`); the
pocket geometry is that of `R7Aux131.r7PocketStop_cfPocket`; then `twoSeedPhaseMeansAt_of_stop` on each test. -/
theorem twoSeedPhaseMeansInput_of_const [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ}
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤)
    (hin : TwoSeedPhaseConstInput κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀') :
    PhaseSide.TwoSeedPhaseMeansInput κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a', δ, c₀, hside, hconst⟩ := hin A hA hAG hPA ψ hψ hψm
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  -- the walls' marked union law at `T⁰(q)`
  have hwalls := fun q : ℝ≥0 => PocketStopMarked.pocketStopWallsLaw_stopHull0_marked hT' hTr hu₀ hh hC hκ hu₀' hX
    hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL (wallsSigma_le_drivingFiltration hX R L) hRm' hLm' hGm hG
    hA hAG (fun ω hω => hcfg ω (hAG hω)) (fun ω hω => hζG ω (hAG hω)) hψ hψm q
  -- the pocket geometry (as in `r7PocketStop_cfPocket`)
  have hdrive : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧
      travAll R L r η ψ ω u ∈ H ∧ M < ‖travAll R L r η ψ ω u‖ := fun ω hω =>
    (hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAll R L r η ψ ω u :=
    PocketTraversalMeasRand.traversalMeasStatement_of_measurable h𝓦 hRm' hLm' hGm hcfg hηm A (h𝓦 _ hA) hAG ψ hψ
      hψm
  have hpre : ∀ q : ℝ≥0, locPrefixSigma (wallsSigma P R L) A (travAll R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => (hdrive ω hω).1) hγm
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  have hP : ∀ ω ∈ A, Sec6.IsReversePocket (fun s : ℝ => W' s.toNNReal ω) (η ω) (cfPocket (R ω) (L ω) r)
      (cfArcR (R ω) (L ω) r) (cfArcL (R ω) (L ω) r) (cfBeta (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) := fun ω hω =>
    (hcfg ω (hAG hω)).conf.isReversePocket_of_counterflow
      (zero_notMem_closure_of_rightLo_pos (hcfg ω (hAG hω)).conf (hcfg ω (hAG hω)).bounded)
      (hcfg ω (hAG hω)).trace (hcfg ω (hAG hω)).continuous_W (hcfg ω (hAG hω)).W_zero (hcfg ω (hAG hω)).revR
      (hcfg ω (hAG hω)).revL (hcfg ω (hAG hω)).visR
  have hψ' : ∀ ω ∈ A, Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0)
      (cfArcR (R ω) (L ω) r 1) (ψ ω) := fun ω hω => by
    rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
    exact hψ ω hω
  exact ⟨n, hn, twoSeedPhaseMeansAt_of_stop (κ := κ) hκ h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm
    (fun ω hω => (hdrive ω hω).2)
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
    (fun q ω hω _ => isOpen_H_diff_fwdHull_ambTime (hP ω hω) (ψ ω) q)
    (fun q ω hω hq => image_inter_domain_ambTime (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)) (isZeroBoundaryGFF_centredField hC hu₀') hu₀'.1 hu₀'.2.1 hn
    (fun q => pocketStopUnionLaw_stopHull_of_stopHull0 hcfg hAG
      (pocketStopUnionLaw_cfPocket h𝓦 hRm' hLm' hGm hG hA hAG (hpre q) (hwalls q))) hside hconst⟩

/-- **`PhaseSide.TwoSeedPhaseMeansInputInf` from R.5 up to a constant phase** (pocket opening at the flow seed; as
`twoSeedPhaseMeansInput_of_const`, with `PocketStopMarked.pocketStopWallsLaw_stopHull0Inf_marked` and the geometry of
`R7Aux131.r7PocketStop_cfPocketInf`). -/
theorem twoSeedPhaseMeansInputInf_of_const [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ}
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤)
    (hin : TwoSeedPhaseConstInputInf κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀') :
    PhaseSide.TwoSeedPhaseMeansInputInf κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a', δ, c₀, hside, hconst⟩ := hin A hA hAG hPA ψ hψ hψm
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  -- the walls' marked union law at `T⁰(q)`
  have hwalls := fun q : ℝ≥0 => PocketStopMarked.pocketStopWallsLaw_stopHull0Inf_marked hT' hTr hu₀ hh hC hκ hu₀' hX
    hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL (wallsSigma_le_drivingFiltration hX R L) hRm' hLm' hGm hG
    hA hAG (fun ω hω => hcfg ω (hAG hω)) (fun ω hω => hζG ω (hAG hω)) hψ hψm q
  -- the pocket geometry (as in `r7PocketStop_cfPocket`)
  have hdrive : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧
      travAllInf R L r η ψ ω u ∈ H ∧ M < ‖travAllInf R L r η ψ ω u‖ := fun ω hω =>
    (hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAllInf R L r η ψ ω u := fun u hu =>
    measurable_travSubInf h𝓦 hRm' hLm' hGm hcfg hηm hAG hψ hψm hu
  have hpre : ∀ q : ℝ≥0, locPrefixSigma (wallsSigma P R L) A (travAllInf R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => (hdrive ω hω).1) hγm
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2
  have hP : ∀ ω ∈ A, Sec6.IsReversePocketInf (fun s : ℝ => W' s.toNNReal ω) (η ω) (cfPocket (R ω) (L ω) r)
      (cfArcRInf (R ω) (L ω) r) (cfArcLInf (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) :=
    fun ω hω => (hcfg ω (hAG hω)).isReversePocketInf
  have hψ' : ∀ ω ∈ A, Sec6.IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0) (ψ ω) :=
    fun ω hω => by
      rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
      exact hψ ω hω
  exact ⟨n, hn, twoSeedPhaseMeansAt_of_stop (κ := κ) hκ h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm
    (fun ω hω => (hdrive ω hω).2)
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
    (fun q ω hω _ => isOpen_H_diff_fwdHull_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (ψ ω) q)
    (fun q ω hω hq => image_inter_domain_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)) (isZeroBoundaryGFF_centredField hC hu₀') hu₀'.1 hu₀'.2.1 hn
    (fun q => pocketStopUnionLaw_stopHullInf_of_stopHull0Inf hcfg hAG
      (pocketStopUnionLaw_cfPocket h𝓦 hRm' hLm' hGm hG hA hAG (hpre q) (hwalls q))) hside hconst⟩

end Wire

/-! ### Every R.7 configuration -/

section Remaining

open R7Outer R7Leaves StripPocketConfig RefWire

/-- **R.5 up to a constant lattice phase on every R.7 configuration** (named input replacing
`PhaseSide.R7PhaseMeansRemaining`; heights `c`, `c′`): the premises are exactly those of
`PhaseSide.R7PhaseMeansRemaining` (hence of `Hsd.R7PhaseSideRemaining` and `R7ExtremalSideDet.side`); the conclusion
asks, on every pocket test, for R.5's phase word (1) with a phase that is constant on the positive relative lifetime
(follow-up 5 (3.2)), instead of (1) and Aux. lemma 122's retained hypothesis (M). -/
def R7PhaseConstRemaining (k rL rR c c' : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B →
    ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀' →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ' ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedPhaseConstInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedPhaseConstInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- **Aux. lemma 122's retained hypothesis on every R.7 configuration from R.5 up to a constant phase**: the walls'
data (field determination and entrance locality of the walls, the frozen coupling of the counterflow and its infinite
lifetime) are derived from the configuration as in `R7Leaves.r7PocketStop_extremal_of_config`, then
`twoSeedPhaseMeansInput(Inf)_of_const` on the two kinds of change pockets. -/
theorem r7PhaseMeansRemaining_of_const {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hconst : R7PhaseConstRemaining.{u} k rL rR c c') : PhaseSide.R7PhaseMeansRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hconst P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hk0 : 0 < k := by linarith
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
  obtain ⟨-, hT', hTr, hC⟩ := hD
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hΦαR, -, -, hΦαL, hΦ⟩ := hcfg.borel
  have hreg := hcfg.regular
  have hdetR := fun t => hdet_of_borel hΦαR (fun ω => (hΦ ω).1) hV.R_ae u₀ t
  have hdetL := fun t => hdet_of_borel hΦαL (fun ω => (hΦ ω).2.2.2) hV.L_ae u₀ t
  have hlocR := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αR
    (hreg.mono fun ω hω => hω.2.2.2.2.1) hu₀ hV.R_cont hV.R_zero hV.R_meas hV.R_ae
  have hlocL := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αL
    (hreg.mono fun ω hω => hω.2.2.2.2.2.2.2) hu₀ hV.L_cont hV.L_zero hV.L_meas hV.L_ae
  have hRm' := measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hLm' := measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hGp : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
  have hG0 : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)},
      IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
    intro ω hω
    exact hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  exact ⟨twoSeedPhaseMeansInput_of_const hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hGp (fun ω hω => hcfgP ω hω.1 hω.2)
      (fun ω hω => hζG ω hω.1) hs,
    twoSeedPhaseMeansInputInf_of_const hk0 hT' hTr hu₀.1 hh0 hC hu₀' hX hζ hV.R_cont hV.L_cont hV.R_zero
      hV.L_zero hV.R_meas hV.L_meas hdetR hdetL hlocR hlocL hV.η_meas hG0 hcfgI' (fun ω hω => hζG ω hω.1) hsI⟩

end Remaining

/-! ### Theorem 1.2's R.7 reference -/

section Late

open Wire Hsd R7Leaves RefWire R7Outer

/-- **Theorem 1.2's R.7 reference with the side field from R.5 up to a constant phase**:
`PhaseSide.r7ReferenceStatement_late_means` with `PhaseSide.R7PhaseMeansRemaining` replaced by `R7PhaseConstRemaining`
at the heights `c = πχ(16/k) ≥ 0`, `c′ = 0`, for the extremal pairs (`r7PhaseMeansRemaining_of_const`). The other inputs
are exactly those of `PhaseSide.r7ReferenceStatement_late_means`. -/
theorem r7ReferenceStatement_late_const
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hQ0 : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hlaws : Fig51CandLawsStatement
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)))
    (hconst : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7PhaseConstRemaining.{0} k rL rR (Real.pi * chiC (16 / k)) 0)
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR) :
    R7.R7ReferenceStatement.{0} :=
  PhaseSide.r7ReferenceStatement_late_means hRect hRectEight Ref0 hCover0 hAvoid0 hQ0 hlaws
    (fun k hk4 rL rR hL hR hmax => r7PhaseMeansRemaining_of_const hk4
      (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos (R7.sixteen_div_pos (by linarith)) (R7.sixteen_div_lt_four hk4)).le)
      le_rfl (hconst k hk4 rL rR hL hR hmax)) hOuter

end Late

end InteractingSLE.Sec7.PhaseClause
