/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlR7Walls
import InteractingSLE.Spec.Sec7.PocketStopMarkedInf
import InteractingSLE.Spec.Sec7.PocketStopSideEndGeometry

/-!
# The R.7 walls laws at `T⁰(q)` and at `T⁰(q) ∨ s` with stopped marks — pocket opening at the flow seed

Packet PROVE-R5-ENLARGED (continued). The seed-opening (`…Inf`) twins of `R5EnlR7Walls`, the same proofs with the
landed seed-opening stop `stopTimeMInf`, its Galmarino property (`isMarkedStop_stopTimeMInf`), its `hS0`
(`measurableSet_sup_iSup_of_locPrefixSigmaInf`), the hull identity `stopHull0Inf_eq_regHull`, the active domain
`PocketStopSide.activeDom_cfPocketInf_eq_stopHull` and `extHullSet_stopHull0Inf`:

* **`pocketStopWallsLaw_stopHull0Inf_markedStop`** — the current law (at `T⁰(q)`, hull `stopHull0Inf`);
* **`pocketStopWallsLaw_regHull_max_markedStopInf`** — the enlarged law (at `T⁰(q) ∨ s`);
* **`r7HasOldChartIncrementLawOnInf`** — clause 4 of `R5ClausesOn` on an R.7 test whose change pocket opens at the flow
  seed, with only the reference chart's `hfwd` (and pathwise chart facts) as inputs.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopMarked

open QuantumZipper (H)
open LQGMetric (DistOn)
open WangWu (negInv)
open WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C Lemma71I PocketCoord PocketJordan
  PocketMarks PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopWallsFin R5Enl

variable {Ω : Type*}

/-- **The R.7 walls–hull law at `T⁰(q)` with the stopped information of `T⁰(q)` as marks** (the current law of
Lemma R.5; `pocketStopWallsLaw_stopHull0Inf_marked` with the stopped records). -/
theorem pocketStopWallsLaw_stopHull0Inf_markedStop
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (h𝓦 : 𝓦 ≤ MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX 0)
    (hRm' : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm' : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hGm : MeasurableSet[𝓦] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A)
    (hAG : A ⊆ G) (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) (q : ℝ≥0) :
    PocketStopWallsLaw (markedStopSigma (drivingFiltration P hX) (fullHist ![R, L]) (stopTimeMInf A R L r η ψ q)) P A
      (travAllInf R L r η ψ) (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (stopHull0Inf R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q) (centredField h'' u₀') q := by
  classical
  have hc2 : ∀ i ω, Continuous ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := Fin.forall_fin_two.2 ⟨hRc, hLc⟩
  have h02 : ∀ i ω, (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω 0 = (0 : Fin 2 → ℂ) i :=
    Fin.forall_fin_two.2 ⟨hR0, hL0⟩
  have hm2 : ∀ i t, Measurable fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t := Fin.forall_fin_two.2 ⟨hRm, hLm⟩
  have hdet2 : ∀ i t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω) :=
    Fin.forall_fin_two.2 ⟨hdetR, hdetL⟩
  have hloc2 : ∀ i, Sec6.IsEntranceHistoryLocal ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i) (centredField h u₀) P :=
    Fin.forall_fin_two.2 ⟨hlocR, hlocL⟩
  have hΓe : (fun ω => negInv '' (range (R ω) ∪ range (L ω))) =
      fun ω => negInv '' ⋃ i, range ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := funext fun ω => by
    rw [iUnion_range_fin_two]
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  rw [hΓe]
  refine R5Enl.pocketStopWallsLaw_markedStopSigma (T := stopTimeMInf A R L r η ψ q) hC hκ' hu₀' hX hζ
    (measurable_fullHist hm2) (measurable_negInv_walls hc2 hm2)
    (fun U G hUH hG hd B hB => walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc2 h02 hm2 hdet2 hloc2 U G hUH hG hd B hB)
    (fun ω hω hl => ?_)
    (isMarkedStop_stopTimeMInf h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q)
    (fun M hM => measurableSet_sup_iSup_of_locPrefixSigmaInf h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q M hM)
  have hT : stopTimeMInf A R L r η ψ q ω = stopTime0Inf R L r η ψ q ω := by
    unfold stopTimeMInf
    exact ite_eq_left ⟨hω, hl⟩
  rw [hT]
  exact ⟨ENNReal.ofReal_lt_top, stopHull0Inf_eq_regHull (hcfg ω hω) (hζA ω hω) q⟩

/-- **The R.7 walls–hull law at `T⁰(q) ∨ s` with the stopped information of `T⁰(q) ∨ s` as marks** (the enlarged
law of Lemma R.5). -/
theorem pocketStopWallsLaw_regHull_max_markedStopInf
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (h𝓦 : 𝓦 ≤ MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX 0)
    (hRm' : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm' : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hGm : MeasurableSet[𝓦] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A)
    (hAG : A ⊆ G) (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) (q s : ℝ≥0) :
    PocketStopWallsLaw (markedStopSigma (drivingFiltration P hX) (fullHist ![R, L])
      (fun ω => max (stopTimeMInf A R L r η ψ q ω) (s : ℝ≥0∞))) P A (travAllInf R L r η ψ)
      (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (fun ω => regHull W' ζ' (max (stopTimeMInf A R L r η ψ q ω) (s : ℝ≥0∞)).toNNReal ω) (centredField h'' u₀') q := by
  classical
  have hc2 : ∀ i ω, Continuous ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := Fin.forall_fin_two.2 ⟨hRc, hLc⟩
  have h02 : ∀ i ω, (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω 0 = (0 : Fin 2 → ℂ) i :=
    Fin.forall_fin_two.2 ⟨hR0, hL0⟩
  have hm2 : ∀ i t, Measurable fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t := Fin.forall_fin_two.2 ⟨hRm, hLm⟩
  have hdet2 : ∀ i t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω) :=
    Fin.forall_fin_two.2 ⟨hdetR, hdetL⟩
  have hloc2 : ∀ i, Sec6.IsEntranceHistoryLocal ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i) (centredField h u₀) P :=
    Fin.forall_fin_two.2 ⟨hlocR, hlocL⟩
  have hΓe : (fun ω => negInv '' (range (R ω) ∪ range (L ω))) =
      fun ω => negInv '' ⋃ i, range ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := funext fun ω => by
    rw [iUnion_range_fin_two]
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  rw [hΓe]
  refine R5Enl.pocketStopWallsLaw_markedStopSigma_max (T := stopTimeMInf A R L r η ψ q) hC hκ' hu₀' hX hζ
    (measurable_fullHist hm2) (measurable_negInv_walls hc2 hm2)
    (fun U G hUH hG hd B hB => walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc2 h02 hm2 hdet2 hloc2 U G hUH hG hd B hB)
    s (fun ω hω hl => ?_)
    (isMarkedStop_stopTimeMInf h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q)
    (fun M hM => measurableSet_sup_iSup_of_locPrefixSigmaInf h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q M hM)
  have hT : stopTimeMInf A R L r η ψ q ω = stopTime0Inf R L r η ψ q ω := by
    unfold stopTimeMInf
    exact ite_eq_left ⟨hω, hl⟩
  rw [hT]
  exact ⟨ENNReal.ofReal_lt_top, rfl⟩

/-! ### Clause 4 of `R5ClausesOn` on an R.7 test (bounded change pocket) -/

section R7Inst

open PocketWordPerQ PocketTraversal PocketAdapt LocalSets R5Phase

variable {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c₀ : ℝ} {u₀ : ℂ → ℝ}
  {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- **R.5's enlarged-stop increment law on an R.7 test** (bounded change pocket; clause 4 of `R5ClausesOn` for the
reference at the original time `s`): from the walls' data of `R5Phase.pocketStopUnionLaw_ref` and
`pocketStopWallsLaw_stopHull0Inf_marked`, the base chart's facts, and the reference chart on an event `G'` of the
reference record with the forward-map measurability `hfwd` (the only measurability input left), for every pair
event `M ⊆ G'` on which `s ≤ T⁰(q)` and `q` is live. The current stop is `T⁰(q) = stopTimeMInf`, the enlarged stop
`T⁰(q) ∨ s`; all three marked laws and every record relation are derived here. -/
theorem r7HasOldChartIncrementLawOnInf
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c₀ (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω))
    {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (q s : ℝ≥0) {G' : Set Ω}
    (hG' : MeasurableSet[germSigma (liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (regHull W' ζ' s) 0) (centredField h'' u₀') ⊔ locPrefixSigma (refInfo P hX R L s) A (travAllInf R L r η ψ) 0] G')
    {old : Ω → Chart} (hOld : ∀ ω ∈ G', (old ω).IsConformal)
    (hfwd : ∀ z, Measurable[germSigma (liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (regHull W' ζ' s) 0) (centredField h'' u₀') ⊔ locPrefixSigma (refInfo P hX R L s) A (travAllInf R L r η ψ) 0]
      ((G' ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldDom : ∀ ω ∈ G', ((old ω).dom : Set ℂ) =
      H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω)
    {M : Set Ω} (hMG : M ⊆ G') (hME : ∀ ω ∈ M, (s : ℝ≥0∞) ≤ stopTimeMInf A R L r η ψ q ω)
    (hMlive : ∀ ω ∈ M, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (liveExt A (travAllInf R L r η ψ)
        (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0) (centredField h'' u₀') P gOld →
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAllInf R L r η ψ) c q) (centredField h'' u₀') P g →
        HasOldChartIncrementLawOn P M old (relChart c (travAllInf R L r η ψ) q) gOld g := by
  classical
  have hm2 : ∀ i t, Measurable fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t := Fin.forall_fin_two.2 ⟨hRm, hLm⟩
  have hh₀ := WholeField.isZeroBoundaryGFF_centredField hC hu₀'
  have h𝓦 := wallsSigma_le_drivingFiltration (P := P) hX R L
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hGpre := isMarkedStop_stopTimeMInf h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q
  have hS0pre : locPrefixSigma (wallsSigma P R L) A (travAllInf R L r η ψ) q ≤
      MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ ⨆ t, drivingFiltration P hX t :=
    fun M hM => measurableSet_sup_iSup_of_locPrefixSigmaInf h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q M hM
  have hT := isMarkedStop_bot_of hGpre
  have hmle : ∀ T : Ω → ℝ≥0∞, markedStopSigma (drivingFiltration P hX) (fullHist ![R, L]) T ≤ mΩ := fun T =>
    (markedStopSigma_le T).trans (sup_le (measurable_fullHist hm2).comap_le
      (iSup_le fun t => (drivingFiltration P hX).le t))
  -- the current law at `T⁰(q)`
  have hCurW := pocketStopWallsLaw_stopHull0Inf_markedStop hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm
    hdetR hdetL hlocR hlocL h𝓦 hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q
  have hpreC := (locPrefixSigma_markedStopSigma_le hGpre hS0pre).trans (hmle _)
  have hCur := pocketStopUnionLaw_cfPocket_markedStopSigma hX hRc hLc hRm hLm hT hGm hG hA hAG hpreC hCurW
  -- the enlarged law at `T⁰(q) ∨ s`
  have hEnlW := pocketStopWallsLaw_regHull_max_markedStopInf hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm
    hLm hdetR hdetL hlocR hlocL h𝓦 hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q s
  obtain ⟨hGmax, hS0max⟩ := isMarkedStop_locPrefixSigma_max hGpre hS0pre s
  have hpreE := (locPrefixSigma_markedStopSigma_le hGmax hS0max).trans (hmle _)
  have hEnl := pocketStopUnionLaw_cfPocket_markedStopSigma hX hRc hLc hRm hLm (isMarkedStop_bot_of hGmax) hGm hG
    hA hAG hpreE hEnlW
  -- the reference law at the original time `s`
  have hRef := R5Phase.pocketStopUnionLaw_ref hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hGm hG hA hAG hγ s
  have hA' : MeasurableSet[refInfo P hX R L s] A := R5Phase.wallsSigma_le_refInfo (P := P) hX R L s _ hA
  have hpreB : locPrefixSigma (refInfo P hX R L s) A (travAllInf R L r η ψ) 0 ≤ mΩ := by
    rw [PocketStopSide.locPrefixSigma_zero_of_driven hA' hγ]
    exact R5Phase.refInfo_le hX hRm hLm s
  have hBs := measurable_refSet_refInfo hC hκ' hX hζ hRc hLc hGm hG hA hAG hγ s
  -- pathwise facts
  have hTval : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      stopTimeMInf A R L r η ψ q ω = stopTime0Inf R L r η ψ q ω := fun ω hω hl => by
    unfold stopTimeMInf
    exact ite_eq_left ⟨hω, hl⟩
  have hTlt : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → stopTimeMInf A R L r η ψ q ω < ⊤ :=
    fun ω hω hl => by rw [hTval ω hω hl]; exact ENNReal.ofReal_lt_top
  have hS0eq : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      stopHull0Inf R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q ω =
        regHull W' ζ' (stopTimeMInf A R L r η ψ q ω).toNNReal ω := fun ω hω hl => by
    rw [hTval ω hω hl]
    exact stopHull0Inf_eq_regHull (hcfg ω hω) (hζA ω hω) q
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω => by
    rw [← hcdom ω hω]
    exact (c ω).dom.isOpen
  have hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      activeDom A (travAllInf R L r η ψ) c q ω =
        cfPocket (R ω) (L ω) r ∩ (H \ stopHull0Inf R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q ω) := by
    intro ω hω hl
    rw [PocketStopSide.activeDom_cfPocketInf_eq_stopHull (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω (hcfg ω hω)
      (hψ ω hω) (hc ω hω) (hcdom ω hω)
      (hceq ω hω) hl, inter_sdiff_eq_sdiff_extHullSet, inter_sdiff_eq_sdiff_extHullSet,
      extHullSet_stopHull0Inf (hcfg ω hω) q]
  refine R5Enl.hasOldChartIncrementLawOn_of_pocketLaws_stop hh₀ hT hγ hc hCo
    (fun ω _ => R5Phase.isOpen_H_diff_regHull W' ζ' s ω) (fun ω _ => R5Phase.isOpen_H_diff_regHull W' ζ' _ ω)
    (fun ω hω hl => by rw [hS0eq ω hω hl]; exact R5Phase.isOpen_H_diff_regHull W' ζ' _ ω) hact hpreB hRef hpreC
    hCur hpreE hEnl hBs ?_ ?_ ?_ hG' hOld hfwd hOldDom hMG hME hMlive
  · intro ω hω hl
    refine regHull_mono W' ζ' ω ?_
    have hne : max (stopTimeMInf A R L r η ψ q ω) (s : ℝ≥0∞) ≠ ⊤ := (max_lt (hTlt ω hω hl) ENNReal.coe_lt_top).ne
    simpa only [ENNReal.toNNReal_coe] using ENNReal.toNNReal_mono hne (le_max_right _ _)
  · intro ω hsT hω hl
    rw [hS0eq ω hω hl]
    refine regHull_mono W' ζ' ω ?_
    simpa only [ENNReal.toNNReal_coe] using ENNReal.toNNReal_mono (hTlt ω hω hl).ne hsT
  · intro ω hsT hω hl
    rw [hS0eq ω hω hl, max_eq_left hsT]

end R7Inst

end InteractingSLE.Sec7.PocketStopMarked
