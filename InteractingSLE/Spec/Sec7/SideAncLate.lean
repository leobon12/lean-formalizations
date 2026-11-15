/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideAncOrient
import InteractingSLE.Spec.Sec7.SideAncStop
import InteractingSLE.Spec.Sec7.PhaseContR7

/-!
# The late pockets of Theorems 1.2–1.3: zero phase by Aux. lemma 122

PROVE-SIDE-ANCHOR. The late (both-low) pockets of the wiring of Theorems 1.2–1.3 carry the three- and four-mark
words `(wordL1 | wordL2; wordR2)` of Lemma 7.25 (RS13.6) with seed weights `(r_L, r_R)`, both in `(−2, κ'/2 − 4)`,
`κ' = 16/κ` the counterflow parameter. Since `κ'/2 − 4 < κ' − 6`, the bounded sector (3.3) of follow-up 5 §3.2 holds:
"If `−2 < r_L, r_R < 2A − 2 = k − 6`, Aux. 122 forces zero phase." This file proves it on every late pocket test from
R.5 up to phase alone, through the walls' marked union law (`PocketStopMarked.pocketStopWallsLaw_stopHull0_marked`,
STRIPSYS43), the pocket geometry (as in `PhaseClause.twoSeedPhaseMeansInput_of_const`), the marks of an arbitrary
point-measurable Jordan coordinate (`SideAncOrient`) and `ae_phase_eq_zero_of_stop`.

## Main results

* `ae_phase_eq_zero_of_late`, `ae_phase_eq_zero_of_lateInf`: one late test, a general left word;
* `pocketStopSideLimit_zero_of_phase`: at time `0` the exposed interval is empty, so the phase is irrelevant;
* `PocketSidePhaseInput0`, `PocketSidePhaseInputInf0`: the late side input up to phase (R.5 up to phase, no zero
  phase, no anchor);
* **`pocketSideLimitInput0_of_phase`**, **`pocketSideLimitInputInf0_of_phase`**: the zero-phase side-limit inputs
  `PocketWordPerQ.PocketSideLimitInput0(Inf0)` from the phase inputs and the walls' data.

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

namespace InteractingSLE.Sec7.SideAnc

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 PocketWordPerQ PhaseClause

/-! ### The phase at time zero -/

section Zero

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
  {c : Ω → Chart} {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {K : Ω → Set ℂ}

/-- **At time `0` the phase is irrelevant**: with both seeds at `0` and the driver started at `0`, the exposed interval
is empty, so R.5 up to phase at `q = 0` is the canonical side limit. -/
theorem pocketStopSideLimit_zero_of_phase (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hseedL : ∀ ω, xL ω 0 = 0)
    (hseedR : ∀ ω, xR ω 0 = 0) {d : Ω → ℝ}
    (hside : PocketStopSide.PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u K d 0) :
    PocketStop.PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u K 0 := by
  intro g hg
  filter_upwards [hside.2 g hg] with ω hω hωA hl v hv hvr ξ hξ
  have h := hω hωA hl v hv hvr ξ hξ
  have hz := PhaseMart.geomLW_geomRW_zero_of_seed (T := fun ω : A => capLife (γ ω))
    (W := fun t (ω : A) => segDriver (γ ω) t) (xL := fun ω : A => xL ω) (xR := fun ω : A => xR ω)
    (ω := ⟨ω, hωA⟩) (fun ω => (hγ ω ω.2).segDriver_spec.1) (fun ω => (hγ ω ω.2).segDriver_spec.2.1)
    (fun ω => hseedL ω) (fun ω => hseedR ω) (PocketPhaseMeans.capLife_pos (hγ ω hωA))
  have hL : geomLW (fun t ω => segDriver (γ ω) t) xL 0 0 ω = 0 := hz.1
  have hR : geomRW (fun t ω => segDriver (γ ω) t) xR 0 0 ω = 0 := hz.2
  have hW0 : segDriver (γ ω) 0 = 0 := (hγ ω hωA).segDriver_spec.1
  rw [PhaseMart.phaseData_eq_of_le (vL := fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i 0 ω -
    segDriver (γ ω) 0) (vR := fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j 0 ω - segDriver (γ ω) 0)
    (by simp only [hL, hR, hW0, le_refl]) (d ω) 0] at h
  simpa only [PhaseSel.phaseData, zero_mul, add_zero] using h

end Zero

/-! ### One late pocket test -/

section Test

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Zero phase on one bounded late pocket test** (Aux. lemma 122 in the bounded sector (3.3)): for the counterflow
configuration of a bounded change pocket with the walls' data (as in `PhaseClause.twoSeedPhaseMeansInput_of_const`),
an arbitrary point-measurable Jordan coordinate `ψ`, a left word `ρL` with walls-measurable ordered marks `xL` and the
right word `wordR2` with its marks `marksRAll`, both seed weights in `(−2, 16/κ − 6)`, R.5 up to phase forces the
phase to vanish almost surely on the live event at every positive time. -/
theorem ae_phase_eq_zero_of_late [IsProbabilityMeasure P] {κ rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hrR : -2 < rR) (hrR' : rR < 16 / κ - 6)
    {κ' : ℝ} {nL' nR' : ℕ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ} {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL' → ℝ≥0 → Ω → ℝ} {VR : Fin nR' → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {A : Set Ω} (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G) (hPA : 0 < P A) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ)
    {nL : ℕ} {ρL : Fin (nL + 1) → ℝ} (hrL : -2 < ρL 0) (hrL' : ρL 0 < 16 / κ - 6) {xL : Ω → Fin (nL + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val (wallsSigma P R L)] fun ω : A => xL ω)
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hxLd : ∀ ω ∈ A, ∀ i : Fin nL, xL ω i.succ < 0)
    (hxLi : ∀ ω ∈ A, Antitone (xL ω)) {n : Ω → ℤ} (hn : Measurable[wallsSigma P R L] n) {a' : ℝ}
    {δ : ℝ≥0 → Ω → ℝ}
    (hside : ∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit (16 / κ) ρL (wordR2 κ (rs136Theta2 κ rR)) P A
      (travAll R L r η ψ) xL (marksRAll L r ψ)
      (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a' (centredField h'' u₀') u
      (activeCompl A (travAll R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q) :
    ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → δ q ω = 0 := by
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have h0 : ∀ ω ∈ A, (0 : ℂ) ∉ closure (changePocket (R ω) (L ω) r) := fun ω hω =>
    zero_notMem_closure_of_rightLo_pos (hcfg ω (hAG hω)).conf (hcfg ω (hAG hω)).bounded
  have hκ'' : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
  -- the walls' marked union law at `T⁰(q)`
  have hwalls := fun q : ℝ≥0 => PocketStopMarked.pocketStopWallsLaw_stopHull0_marked hT' hTr hu₀ hh hC hκ' hu₀' hX
    hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL (wallsSigma_le_drivingFiltration hX R L) hRm' hLm' hGm hG
    hA hAG (fun ω hω => hcfg ω (hAG hω)) (fun ω hω => hζG ω (hAG hω)) hψ hψm q
  -- the pocket geometry (as in `PhaseClause.twoSeedPhaseMeansInput_of_const`)
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
    (hcfg ω (hAG hω)).conf.isReversePocket_of_counterflow (h0 ω hω)
      (hcfg ω (hAG hω)).trace (hcfg ω (hAG hω)).continuous_W (hcfg ω (hAG hω)).W_zero (hcfg ω (hAG hω)).revR
      (hcfg ω (hAG hω)).revL (hcfg ω (hAG hω)).visR
  have hψ' : ∀ ω ∈ A, Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0)
      (cfArcR (R ω) (L ω) r 1) (ψ ω) := fun ω hω => by
    rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
    exact hψ ω hω
  have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ U ⊆ cfPocket (R ω) (L ω) r} := fun U hUo hUH =>
    measurableSet_subset_cfPocket hRm' hLm' hGm hG hA hAG hUo hUH
  -- the right marks: measurable, the seed at `0`, the change mark positive
  have hxRre := measurable_leftMark (mΩ := wallsSigma P R L) hψm hLm' hA hAG (fun ω hω => hG ω (hAG hω)) h0
  have hxRm : Measurable[MeasurableSpace.comap Subtype.val (wallsSigma P R L)]
      fun ω : A => marksRAll L r ψ ω :=
    @measurable_vec_two A (MeasurableSpace.comap Subtype.val (wallsSigma P R L)) _
      (measurable_sub_of_indicator subset_rfl hxRre)
  have hxRp : ∀ ω ∈ A, 0 < (ψ ω (cfPt (toDisc (Lemma71I.realPath (L ω)) (discTime r)))).re := fun ω hω =>
    (jordan_sides (hG ω (hAG hω)) (h0 ω hω) (hcfg ω (hAG hω)).oriented (hψ ω hω)).2 _
      (hG ω (hAG hω)).changeCorners.2.2.2.2.1
  -- the right seed weight
  have hρR : wordR2 κ (rs136Theta2 κ rR) 0 = rR := by
    simp only [wordR2, Matrix.cons_val_zero]
    exact cf95RhoR_rs136Theta2 hκ hκ4 rR
  refine ae_phase_eq_zero_of_stop (𝓦 := wallsSigma P R L) hκ'' hrL hrL' (by rw [hρR]; exact hrR)
    (by rw [hρR]; exact hrR') h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm (fun ω hω => (hdrive ω hω).2) hxLm hxRm
    hseedL (fun ω _ => by simp [marksRAll]) hxLd (fun ω hω j => ?_) hxLi
    (fun ω hω => monotone_vec_two (hxRp ω hω).le)
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm' hCin
    (fun q ω hω _ => isOpen_H_diff_fwdHull_ambTime (hP ω hω) (ψ ω) q)
    (fun q ω hω hq => image_inter_domain_ambTime (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)) (isZeroBoundaryGFF_centredField hC hu₀') hu hub hn
    (fun q => pocketStopUnionLaw_stopHull_of_stopHull0 hcfg hAG
      (pocketStopUnionLaw_cfPocket h𝓦 hRm' hLm' hGm hG hA hAG (hpre q) (hwalls q))) hside
  have hj : j.succ = (1 : Fin 2) := by fin_cases j; rfl
  rw [hj]
  simpa [marksRAll] using hxRp ω hω

/-- **Zero phase on one late pocket test opening at the flow seed** (as `ae_phase_eq_zero_of_late`, with the walls'
law and the geometry of `PhaseClause.twoSeedPhaseMeansInputInf_of_const` and an arbitrary point-measurable Jordan
coordinate at infinity). -/
theorem ae_phase_eq_zero_of_lateInf [IsProbabilityMeasure P] {κ rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hrR : -2 < rR) (hrR' : rR < 16 / κ - 6)
    {κ' : ℝ} {nL' nR' : ℕ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ} {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL' → ℝ≥0 → Ω → ℝ} {VR : Fin nR' → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {A : Set Ω} (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G) (hPA : 0 < P A) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ)
    {nL : ℕ} {ρL : Fin (nL + 1) → ℝ} (hrL : -2 < ρL 0) (hrL' : ρL 0 < 16 / κ - 6) {xL : Ω → Fin (nL + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val (wallsSigma P R L)] fun ω : A => xL ω)
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hxLd : ∀ ω ∈ A, ∀ i : Fin nL, xL ω i.succ < 0)
    (hxLi : ∀ ω ∈ A, Antitone (xL ω)) {n : Ω → ℤ} (hn : Measurable[wallsSigma P R L] n) {a' : ℝ}
    {δ : ℝ≥0 → Ω → ℝ}
    (hside : ∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit (16 / κ) ρL (wordR2 κ (rs136Theta2 κ rR)) P A
      (travAllInf R L r η ψ) xL (marksRAll L r ψ)
      (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a' (centredField h'' u₀') u
      (activeCompl A (travAllInf R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q) :
    ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → δ q ω = 0 := by
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hκ'' : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
  -- the walls' marked union law at `T⁰(q)`
  have hwalls := fun q : ℝ≥0 => PocketStopMarked.pocketStopWallsLaw_stopHull0Inf_marked hT' hTr hu₀ hh hC hκ' hu₀' hX
    hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL (wallsSigma_le_drivingFiltration hX R L) hRm' hLm' hGm hG
    hA hAG (fun ω hω => hcfg ω (hAG hω)) (fun ω hω => hζG ω (hAG hω)) hψ hψm q
  -- the pocket geometry (as in `PhaseClause.twoSeedPhaseMeansInput_of_const`)
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
  have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ U ⊆ cfPocket (R ω) (L ω) r} := fun U hUo hUH =>
    measurableSet_subset_cfPocket hRm' hLm' hGm hG hA hAG hUo hUH
  -- the right marks: measurable, the seed at `0`, the change mark positive
  have hxRre := measurable_leftMarkInf (mΩ := wallsSigma P R L) hψm hLm' hA hAG (fun ω hω => hG ω (hAG hω))
  have hxRm : Measurable[MeasurableSpace.comap Subtype.val (wallsSigma P R L)]
      fun ω : A => marksRAll L r ψ ω :=
    @measurable_vec_two A (MeasurableSpace.comap Subtype.val (wallsSigma P R L)) _
      (measurable_sub_of_indicator subset_rfl hxRre)
  have hxRp : ∀ ω ∈ A, 0 < (ψ ω (cfPt (toDisc (Lemma71I.realPath (L ω)) (discTime r)))).re := fun ω hω =>
    (jordanInf_sides (hG ω (hAG hω)) (hcfg ω (hAG hω)).seed (hcfg ω (hAG hω)).oriented (hψ ω hω)).2 _
      (hG ω (hAG hω)).changeCorners.2.2.2.2.1
  -- the right seed weight
  have hρR : wordR2 κ (rs136Theta2 κ rR) 0 = rR := by
    simp only [wordR2, Matrix.cons_val_zero]
    exact cf95RhoR_rs136Theta2 hκ hκ4 rR
  refine ae_phase_eq_zero_of_stop (𝓦 := wallsSigma P R L) hκ'' hrL hrL' (by rw [hρR]; exact hrR)
    (by rw [hρR]; exact hrR') h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm (fun ω hω => (hdrive ω hω).2) hxLm hxRm
    hseedL (fun ω _ => by simp [marksRAll]) hxLd (fun ω hω j => ?_) hxLi
    (fun ω hω => monotone_vec_two (hxRp ω hω).le)
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm' hCin
    (fun q ω hω _ => isOpen_H_diff_fwdHull_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (ψ ω) q)
    (fun q ω hω hq => image_inter_domain_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)) (isZeroBoundaryGFF_centredField hC hu₀') hu hub hn
    (fun q => pocketStopUnionLaw_stopHullInf_of_stopHull0Inf hcfg hAG
      (pocketStopUnionLaw_cfPocket h𝓦 hRm' hLm' hGm hG hA hAG (hpre q) (hwalls q))) hside
  have hj : j.succ = (1 : Fin 2) := by fin_cases j; rfl
  rw [hj]
  simpa [marksRAll] using hxRp ω hω

end Test

/-! ### The late word shapes: one live zero-phase time -/

section Shapes

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem shiftChart_zero (c : Chart) : shiftChart c 0 = c := by
  obtain ⟨f, g, l⟩ := c
  simp only [shiftChart, Int.cast_zero, mul_zero, sub_zero]

/-- **One live zero-phase time** from a zero phase at every fixed positive time (countably many times `1/(k+1)`). -/
theorem anchor_of_ae_zero {A : Set Ω} {γ : Ω → ℝ → ℂ} {δ : ℝ≥0 → Ω → ℝ}
    (h : ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → δ q ω = 0) :
    ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) → ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < capLife (γ ω) ∧ δ s ω = 0 := by
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂P, ω ∈ A → (((1 / ((k : ℝ) + 1)).toNNReal : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) →
      δ (1 / ((k : ℝ) + 1)).toNNReal ω = 0 := fun k => h _ (Real.toNNReal_pos.2 (by positivity))
  filter_upwards [ae_all_iff.2 hk] with ω hω hA hpos
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr0'
  have hlt : (((1 / ((k : ℝ) + 1)).toNNReal : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) :=
    lt_trans (ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe (by positivity)).2 hk)) hr
  exact ⟨_, Real.toNNReal_pos.2 (by positivity), hlt, hω k hA hlt⟩

/-- **The four-mark late word, bounded pocket**: R.5 up to phase in a walls-measurable chart branch forces
zero phase at every positive time (Aux. lemma 122 through `ae_phase_eq_zero_of_late`). -/
theorem late_zero_two [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hrL : -2 < rL) (hrL' : rL < 16 / κ - 6) (hrR : -2 < rR) (hrR' : rR < 16 / κ - 6)
    {κ' : ℝ} {nL' nR' : ℕ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ} {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL' → ℝ≥0 → Ω → ℝ} {VR : Fin nR' → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {A : Set Ω} (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G) (hPA : 0 < P A) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ)
    (hshape : ∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r))
    {n : Ω → ℤ} (hn : Measurable[wallsSigma P R L] n) {a' : ℝ} {δ : ℝ≥0 → Ω → ℝ}
    (hside : ∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit (16 / κ) (wordL2 κ (rs136Theta1 κ rL))
      (wordR2 κ (rs136Theta2 κ rR)) P A (travAll R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ)
      (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a' (centredField h'' u₀') u
      (activeCompl A (travAll R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q) :
    ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → δ q ω = 0 := by
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hρL : wordL2 κ (rs136Theta1 κ rL) 0 = rL := by
    simp only [wordL2, Matrix.cons_val_zero]
    exact cf95RhoL_rs136Theta1 hκ hκ4 rL
  have h0 : ∀ ω ∈ A, (0 : ℂ) ∉ closure (changePocket (R ω) (L ω) r) := fun ω hω =>
    zero_notMem_closure_of_rightLo_pos (hcfg ω (hAG hω)).conf (hcfg ω (hAG hω)).bounded
  have hneg : ∀ ω ∈ A, (ψ ω (cfPt (toDisc (Lemma71I.realPath (R ω)) (discTime 1)))).re < 0 := fun ω hω =>
    (jordan_sides (hG ω (hAG hω)) (h0 ω hω) (hcfg ω (hAG hω)).oriented (hψ ω hω)).1 _ (hshape ω hω)
  have hxLm : Measurable[MeasurableSpace.comap Subtype.val (wallsSigma P R L)]
      fun ω : A => marksL2All R ψ ω :=
    @measurable_vec_two A (MeasurableSpace.comap Subtype.val (wallsSigma P R L)) _
      (measurable_sub_of_indicator subset_rfl (measurable_rightMark (mΩ := wallsSigma P R L) hψm hRm' hA hAG
        (fun ω hω => hG ω (hAG hω)) h0 hshape))
  refine ae_phase_eq_zero_of_late hκ hκ4 hrR hrR' hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hηm hGm hcfg hζG hu hub hA hAG hPA hψ hψm
    (by rw [hρL]; exact hrL) (by rw [hρL]; exact hrL') hxLm (fun ω _ => by simp [marksL2All]) (fun ω hω i => ?_)
    (fun ω hω => antitone_vec_two (hneg ω hω).le) hn hside
  have hi : i.succ = (1 : Fin 2) := by fin_cases i; rfl
  rw [hi]
  simpa [marksL2All] using hneg ω hω

/-- **The three-mark late word, bounded pocket** (as `late_zero_two`). -/
theorem late_zero_one [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hrL : -2 < rL) (hrL' : rL < 16 / κ - 6) (hrR : -2 < rR) (hrR' : rR < 16 / κ - 6)
    {κ' : ℝ} {nL' nR' : ℕ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ} {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL' → ℝ≥0 → Ω → ℝ} {VR : Fin nR' → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {A : Set Ω} (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G) (hPA : 0 < P A) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ)
    {n : Ω → ℤ} (hn : Measurable[wallsSigma P R L] n) {a' : ℝ} {δ : ℝ≥0 → Ω → ℝ}
    (hside : ∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit (16 / κ) (wordL1 κ (rs136Theta1 κ rL))
      (wordR2 κ (rs136Theta2 κ rR)) P A (travAll R L r η ψ) marksL1All (marksRAll L r ψ)
      (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a' (centredField h'' u₀') u
      (activeCompl A (travAll R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q) :
    ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → δ q ω = 0 := by
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hρL : wordL1 κ (rs136Theta1 κ rL) 0 = rL := by
    simp only [wordL1, Matrix.cons_val_zero]
    exact cf95RhoL_rs136Theta1 hκ hκ4 rL
  exact ae_phase_eq_zero_of_late hκ hκ4 hrR hrR' hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hηm hGm hcfg hζG hu hub hA hAG hPA hψ hψm
    (by rw [hρL]; exact hrL) (by rw [hρL]; exact hrL') measurable_const (fun ω _ => rfl) (fun ω _ i => i.elim0)
    (fun ω _ => antitone_vec_one) hn hside

/-- **The four-mark late word, pocket opening at the flow seed** (as `late_zero_two`). -/
theorem late_zero_twoInf [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hrL : -2 < rL) (hrL' : rL < 16 / κ - 6) (hrR : -2 < rR) (hrR' : rR < 16 / κ - 6)
    {κ' : ℝ} {nL' nR' : ℕ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ} {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL' → ℝ≥0 → Ω → ℝ} {VR : Fin nR' → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {A : Set Ω} (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G) (hPA : 0 < P A) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ)
    (hshape : ∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r))
    {n : Ω → ℤ} (hn : Measurable[wallsSigma P R L] n) {a' : ℝ} {δ : ℝ≥0 → Ω → ℝ}
    (hside : ∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit (16 / κ) (wordL2 κ (rs136Theta1 κ rL))
      (wordR2 κ (rs136Theta2 κ rR)) P A (travAllInf R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ)
      (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a' (centredField h'' u₀') u
      (activeCompl A (travAllInf R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q) :
    ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → δ q ω = 0 := by
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hρL : wordL2 κ (rs136Theta1 κ rL) 0 = rL := by
    simp only [wordL2, Matrix.cons_val_zero]
    exact cf95RhoL_rs136Theta1 hκ hκ4 rL
  have hneg : ∀ ω ∈ A, (ψ ω (cfPt (toDisc (Lemma71I.realPath (R ω)) (discTime 1)))).re < 0 := fun ω hω =>
    (jordanInf_sides (hG ω (hAG hω)) (hcfg ω (hAG hω)).seed (hcfg ω (hAG hω)).oriented (hψ ω hω)).1 _
      (hshape ω hω)
  have hxLm : Measurable[MeasurableSpace.comap Subtype.val (wallsSigma P R L)]
      fun ω : A => marksL2All R ψ ω :=
    @measurable_vec_two A (MeasurableSpace.comap Subtype.val (wallsSigma P R L)) _
      (measurable_sub_of_indicator subset_rfl (measurable_rightMarkInf (mΩ := wallsSigma P R L) hψm hRm' hA hAG
        (fun ω hω => hG ω (hAG hω)) hshape))
  refine ae_phase_eq_zero_of_lateInf hκ hκ4 hrR hrR' hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR
    hdetL hlocR hlocL hηm hGm hcfg hζG hu hub hA hAG hPA hψ hψm
    (by rw [hρL]; exact hrL) (by rw [hρL]; exact hrL') hxLm (fun ω _ => by simp [marksL2All]) (fun ω hω i => ?_)
    (fun ω hω => antitone_vec_two (hneg ω hω).le) hn hside
  have hi : i.succ = (1 : Fin 2) := by fin_cases i; rfl
  rw [hi]
  simpa [marksL2All] using hneg ω hω

/-- **The three-mark late word, pocket opening at the flow seed** (as `late_zero_two`). -/
theorem late_zero_oneInf [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hrL : -2 < rL) (hrL' : rL < 16 / κ - 6) (hrR : -2 < rR) (hrR' : rR < 16 / κ - 6)
    {κ' : ℝ} {nL' nR' : ℕ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ} {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL' → ℝ≥0 → Ω → ℝ} {VR : Fin nR' → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {A : Set Ω} (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G) (hPA : 0 < P A) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ)
    {n : Ω → ℤ} (hn : Measurable[wallsSigma P R L] n) {a' : ℝ} {δ : ℝ≥0 → Ω → ℝ}
    (hside : ∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit (16 / κ) (wordL1 κ (rs136Theta1 κ rL))
      (wordR2 κ (rs136Theta2 κ rR)) P A (travAllInf R L r η ψ) marksL1All (marksRAll L r ψ)
      (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a' (centredField h'' u₀') u
      (activeCompl A (travAllInf R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q) :
    ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → δ q ω = 0 := by
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hρL : wordL1 κ (rs136Theta1 κ rL) 0 = rL := by
    simp only [wordL1, Matrix.cons_val_zero]
    exact cf95RhoL_rs136Theta1 hκ hκ4 rL
  exact ae_phase_eq_zero_of_lateInf hκ hκ4 hrR hrR' hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR
    hdetL hlocR hlocL hηm hGm hcfg hζG hu hub hA hAG hPA hψ hψm
    (by rw [hρL]; exact hrL) (by rw [hρL]; exact hrL') measurable_const (fun ω _ => rfl) (fun ω _ i => i.elim0)
    (fun ω _ => antitone_vec_one) hn hside

end Shapes

/-! ### The late side inputs up to phase -/

section Inputs

/-- **The late side input up to phase** (bounded change pocket): `PocketWordPerQ.PocketSideLimitInput0` with R.5 up to
a lattice phase (`PocketStopPhaseSideLimit`) in place of the canonical side limit — no zero phase, no anchor. -/
def PocketSidePhaseInput0 {Ω : Type*} (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
      ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        ∃ (n : Ω → ℤ) (a : ℝ) (δ : ℝ≥0 → Ω → ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSide.PocketStopPhaseSideLimit (16 / κ) (wordL2 κ (rs136Theta1 κ rL))
            (wordR2 κ (rs136Theta2 κ rR)) P A (travAll R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
            (activeCompl A (travAll R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q) ∧
      ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        ∃ (n : Ω → ℤ) (a : ℝ) (δ : ℝ≥0 → Ω → ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSide.PocketStopPhaseSideLimit (16 / κ) (wordL1 κ (rs136Theta1 κ rL))
            (wordR2 κ (rs136Theta2 κ rR)) P A (travAll R L r η ψ) marksL1All (marksRAll L r ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
            (activeCompl A (travAll R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q)

/-- **The late side input up to phase** (pocket opening at the flow seed). -/
def PocketSidePhaseInputInf0 {Ω : Type*} (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
      ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        ∃ (n : Ω → ℤ) (a : ℝ) (δ : ℝ≥0 → Ω → ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSide.PocketStopPhaseSideLimit (16 / κ) (wordL2 κ (rs136Theta1 κ rL))
            (wordR2 κ (rs136Theta2 κ rR)) P A (travAllInf R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
            (activeCompl A (travAllInf R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q) ∧
      ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        ∃ (n : Ω → ℤ) (a : ℝ) (δ : ℝ≥0 → Ω → ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSide.PocketStopPhaseSideLimit (16 / κ) (wordL1 κ (rs136Theta1 κ rL))
            (wordR2 κ (rs136Theta2 κ rR)) P A (travAllInf R L r η ψ) marksL1All (marksRAll L r ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
            (activeCompl A (travAllInf R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) (δ q) q)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The late side-limit input from R.5 up to phase** (bounded change pocket; Aux. lemma 122 in the bounded sector):
with the walls' data of `PocketStopMarked.pocketStopWallsInput0_of_sideLimit` and both seed weights in
`(−2, 16/κ − 6)`, the input up to phase gives `PocketWordPerQ.PocketSideLimitInput0` (drop-in for its `hside`). -/
theorem pocketSideLimitInput0_of_phase [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hrL : -2 < rL) (hrL' : rL < 16 / κ - 6) (hrR : -2 < rR) (hrR' : rR < 16 / κ - 6)
    {κ' : ℝ} {nL' nR' : ℕ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ} {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL' → ℝ≥0 → Ω → ℝ} {VR : Fin nR' → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : PocketSidePhaseInput0 κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u) :
    PocketSideLimitInput0 κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u := by
  intro A hA hAG hPA ψ hψ hψm
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
  obtain ⟨h2, h1⟩ := hin A hA hAG hPA ψ hψ hψm
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨n, a', δ, hn, hside⟩ := h2 hs
    refine ⟨n, a', hn, fun q => ?_⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ q) with hq0 | hqpos
    · subst hq0
      exact pocketStopSideLimit_zero_of_phase hγ (fun ω => by simp [marksL2All]) (fun ω => by simp [marksRAll])
        (hside 0)
    · exact PocketStopSide.pocketStopSideLimit_of_phase_eq_zero (hside q)
        (late_zero_two hκ hκ4 hrL hrL' hrR hrR' hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
        hlocR hlocL hηm hGm hcfg hζG hu hub hA hAG hPA hψ hψm hs hn hside q hqpos)
  · obtain ⟨n, a', δ, hn, hside⟩ := h1 hs
    refine ⟨n, a', hn, fun q => ?_⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ q) with hq0 | hqpos
    · subst hq0
      exact pocketStopSideLimit_zero_of_phase hγ (fun ω => rfl) (fun ω => by simp [marksRAll]) (hside 0)
    · exact PocketStopSide.pocketStopSideLimit_of_phase_eq_zero (hside q)
        (late_zero_one hκ hκ4 hrL hrL' hrR hrR' hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
        hlocR hlocL hηm hGm hcfg hζG hu hub hA hAG hPA hψ hψm hn hside q hqpos)

/-- **The late side-limit input from R.5 up to phase** (pocket opening at the flow seed). -/
theorem pocketSideLimitInputInf0_of_phase [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hrL : -2 < rL) (hrL' : rL < 16 / κ - 6) (hrR : -2 < rR) (hrR' : rR < 16 / κ - 6)
    {κ' : ℝ} {nL' nR' : ℕ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ} {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL' → ℝ≥0 → Ω → ℝ} {VR : Fin nR' → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {G : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : PocketSidePhaseInputInf0 κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u) :
    PocketSideLimitInputInf0 κ rL rR (wallsSigma P R L) P R L r η G (centredField h'' u₀') u := by
  intro A hA hAG hPA ψ hψ hψm
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
  obtain ⟨h2, h1⟩ := hin A hA hAG hPA ψ hψ hψm
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨n, a', δ, hn, hside⟩ := h2 hs
    refine ⟨n, a', hn, fun q => ?_⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ q) with hq0 | hqpos
    · subst hq0
      exact pocketStopSideLimit_zero_of_phase hγ (fun ω => by simp [marksL2All]) (fun ω => by simp [marksRAll])
        (hside 0)
    · exact PocketStopSide.pocketStopSideLimit_of_phase_eq_zero (hside q)
        (late_zero_twoInf hκ hκ4 hrL hrL' hrR hrR' hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR
        hdetL hlocR hlocL hηm hGm hcfg hζG hu hub hA hAG hPA hψ hψm hs hn hside q hqpos)
  · obtain ⟨n, a', δ, hn, hside⟩ := h1 hs
    refine ⟨n, a', hn, fun q => ?_⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ q) with hq0 | hqpos
    · subst hq0
      exact pocketStopSideLimit_zero_of_phase hγ (fun ω => rfl) (fun ω => by simp [marksRAll]) (hside 0)
    · exact PocketStopSide.pocketStopSideLimit_of_phase_eq_zero (hside q)
        (late_zero_oneInf hκ hκ4 hrL hrL' hrR hrR' hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR
        hdetL hlocR hlocL hηm hGm hcfg hζG hu hub hA hAG hPA hψ hψm hn hside q hqpos)

end Inputs

end InteractingSLE.Sec7.SideAnc
