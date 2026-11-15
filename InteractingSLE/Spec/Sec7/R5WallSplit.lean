/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5WallCover
import InteractingSLE.Spec.Sec7.R5EnlCollar

/-!
# R.5's split clause-5 cover for the R.7 reference family (ruling R86), and `R5Clauses(On)` from it

Packet PROVE-R5-WALL. For PROVE-R5-REFCHART's reference family on an R.7 change-pocket test (pair events
`refEvent`, charts `refChart`, references `refHull W' ζ'`, exceptional set `refExc ∪ X`) with the references' own
lifts:

* the **zero reference** of the family (`Denumerable.eqv ℚ 0`, original time `0`): its reference set is empty
  (`refHull_eqv_zero`), its chart is the relative chart at capacity `0` (`refChart_eqv_zero`) and its pair event
  contains the live test (`mem_refEvent_eqv_zero`) — the time-`0` reference of R86 (ii);
* **`r5Cover_ref_of_split`** (and `…Inf`): the full clause 5 from the hull cover `R5Ref.R7AmbientCoverHull` (R86 (i)),
  the initial heights `R7InitialHeights` (R86 (ii), through the zero reference) and the cover on the exposed
  coordinates landing outside the pocket (`exposedOuterSel`, the gap between the two halves of R86);
  `r5Cover_ref_of_liftWord_split` (and `…Inf`) with the hull cover from PROVE-R5-LIFT's `R7AmbientLiftWord`;
* **`r5Clauses_of_refCover`**, **`r5ClausesOn_of_refCover`** (and `…Inf`): `R5Phase.R5Clauses` /
  `R5Enl.R5ClausesOn` for the family from the cover, the finite exceptional set, the lattice phase and the (conditioned)
  increment laws (clause 3 is `R5Ref.refEvent_spec`).

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H Hbar fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Wall

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide
  PhaseSel Aux119Heights PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same PocketStopField
  PocketStopWalls PocketStopWallsFin PocketWordPerQ R5Ref R5Enl Aux29Cor
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*}

/-! ### The zero reference of the family -/

/-- The reference set of the zero reference is empty. -/
theorem refHull_eqv_zero (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) :
    refHull W' ζ' (Denumerable.eqv ℚ 0) = fun _ => ∅ := by
  change regHull W' ζ' (rationalOriginalTime (Denumerable.eqv ℚ 0)) = _
  rw [rationalOriginalTime_eqv_zero]
  exact regHull_zero W' ζ'

section Bounded

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω} {c : Ω → Chart}

/-- The chart of the zero reference is the relative chart at capacity `0` (bounded change pocket). -/
theorem refChart_eqv_zero {ω : Ω} (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) :
    refChart c R L r η ψ (Denumerable.eqv ℚ 0) ω = relChart c (travAll R L r η ψ) 0 ω := by
  simp only [refChart, rationalOriginalTime_eqv_zero, NNReal.coe_zero, visitCap_zero hcfg hψ, Real.toNNReal_zero]

/-- The pair event of the zero reference contains the live test (bounded change pocket). -/
theorem mem_refEvent_eqv_zero {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {q : ℝ≥0} {ω : Ω} (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hcfg : IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) :
    ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q (Denumerable.eqv ℚ 0) := by
  have h0 : (visitCap R L r η ψ ω (rationalOriginalTime (Denumerable.eqv ℚ 0))).toNNReal = 0 := by
    rw [rationalOriginalTime_eqv_zero, NNReal.coe_zero, visitCap_zero (W := fun ω (s : ℝ) => W' s.toNNReal ω)
      hcfg hψ, Real.toNNReal_zero]
  refine ⟨hω, hq, Or.inr rationalOriginalTime_eqv_zero, h0.le.trans (zero_le (a := q)), ?_⟩
  rw [refHull_eqv_zero, rationalOriginalTime_eqv_zero, NNReal.coe_zero,
    QuantumZipper.RS.fwdHull_zero_eq_empty hcfg.continuous_W]

end Bounded

section Inf

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω} {c : Ω → Chart}

/-- The chart of the zero reference is the relative chart at capacity `0` (pocket opening at the flow seed). -/
theorem refChartInf_eqv_zero {ω : Ω} (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) :
    refChartInf c R L r η ψ (Denumerable.eqv ℚ 0) ω = relChart c (travAllInf R L r η ψ) 0 ω := by
  simp only [refChartInf, rationalOriginalTime_eqv_zero, NNReal.coe_zero, visitCapInf_zero hcfg hψ,
    Real.toNNReal_zero]

/-- The pair event of the zero reference contains the live test (pocket opening at the flow seed). -/
theorem mem_refEventInf_eqv_zero {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {q : ℝ≥0} {ω : Ω} (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) :
    ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q (Denumerable.eqv ℚ 0) := by
  have h0 : (visitCapInf R L r η ψ ω (rationalOriginalTime (Denumerable.eqv ℚ 0))).toNNReal = 0 := by
    rw [rationalOriginalTime_eqv_zero, NNReal.coe_zero, visitCapInf_zero (W := fun ω (s : ℝ) => W' s.toNNReal ω)
      hcfg hψ, Real.toNNReal_zero]
  refine ⟨hω, hq, Or.inr rationalOriginalTime_eqv_zero, h0.le.trans (zero_le (a := q)), ?_⟩
  rw [refHull_eqv_zero, rationalOriginalTime_eqv_zero, NNReal.coe_zero,
    QuantumZipper.RS.fwdHull_zero_eq_empty hcfg.continuous_W]

end Inf

/-! ### The full clause 5 from the split cover -/

section Split

variable {κ : ℝ} {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ} {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a' k c' : ℝ} {u₀ : ℂ → ℝ} {𝓕₀ : Filtration ℝ≥0 mΩ}
  {W' : ℝ≥0 → Ω → ℝ} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- **R.5's full clause 5 for the reference family, from the split cover** (bounded change pocket; ruling R86):
the hull cover `R5Ref.R7AmbientCoverHull` at coordinates landing in the pocket, the initial heights through the zero
reference at the wall coordinates (exceptional set `X₀ ⊆ X`), and the cover on the exposed coordinates landing outside
the pocket. References `refHull W' ζ'`, own lifts, all marks at `0`. -/
theorem r5Cover_ref_of_split
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ : 0 < κ)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : ∀ ω i, xL ω i = 0) (hxR : ∀ ω j, xR ω j = 0) {a : ℝ} {δ : Ω → ℝ}
    {X X₀ : Ω → Set ℂ} {q : ℝ≥0}
    (hCov : R7AmbientCoverHull κ ρL ρR ρL' ρR' P A (travAll R L r η ψ) xL xR c a (fun ω => cfPocket (R ω) (L ω) r)
      W' ζ' VL VR δ (fun ω => refExc R L r η ψ q ω ∪ X ω)
      (refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChart c R L r η ψ) q)
    (hInit : R7InitialHeights κ ρL ρR P A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR c a
      (centredField h'' u₀') u₀' X₀) (hX₀ : ∀ ω, X₀ ω ⊆ X ω)
    (hOuter : R5Cover κ ρL ρR P A (travAll R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExc R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChart c R L r η ψ i ω).2.2)
      (refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChart c R L r η ψ) q
      (exposedOuterSel c (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q)) :
    R5Cover κ ρL ρR P A (travAll R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExc R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChart c R L r η ψ i ω).2.2)
      (refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChart c R L r η ψ) q
      (fun _ _ => True) := by
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω => ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1
  have hHull := r5Cover_hull hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm
    hG hA hAG hγ hc (p := fun i ω => (visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal)
    (fun _ _ hω => hω.2.2.2.1) hCov
  have hWall := r5Cover_wall (F := refHull W' ζ') (δ := δ) (X := fun ω => refExc R L r η ψ q ω ∪ X ω)
    (M := refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (old := refChart c R L r η ψ)
    hγ hc hcExt hxL hxR (refHull_eqv_zero W' ζ')
    (fun ω hω => refChart_eqv_zero (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hω) (hψ ω hω))
    (fun ω hω hq => mem_refEvent_eqv_zero hω hq (hcfg ω hω) (hψ ω hω))
    (fun ω => (hX₀ ω).trans subset_union_right) hInit
  exact R5Cover.of_three hHull hWall hOuter

/-- **R.5's full clause 5 for the reference family, from the split cover** (pocket opening at the flow seed;
ruling R86): the hull cover `R5Ref.R7AmbientCoverHull` at coordinates landing in the pocket, the initial heights
through the zero reference at the wall coordinates (exceptional set `X₀ ⊆ X`), and the cover on the exposed
coordinates landing outside the pocket. References `refHull W' ζ'`, own lifts, all marks at `0`. -/
theorem r5Cover_refInf_of_split
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ : 0 < κ)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : ∀ ω i, xL ω i = 0) (hxR : ∀ ω j, xR ω j = 0) {a : ℝ} {δ : Ω → ℝ}
    {X X₀ : Ω → Set ℂ} {q : ℝ≥0}
    (hCov : R7AmbientCoverHull κ ρL ρR ρL' ρR' P A (travAllInf R L r η ψ) xL xR c a (fun ω => cfPocket (R ω) (L ω) r)
      W' ζ' VL VR δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q)
    (hInit : R7InitialHeights κ ρL ρR P A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR c a
      (centredField h'' u₀') u₀' X₀) (hX₀ : ∀ ω, X₀ ω ⊆ X ω)
    (hOuter : R5Cover κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q
      (exposedOuterSel c (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q)) :
    R5Cover κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q
      (fun _ _ => True) := by
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω => ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1
  have hHull := r5Cover_hull hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm
    hG hA hAG hγ hc (p := fun i ω => (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal)
    (fun _ _ hω => hω.2.2.2.1) hCov
  have hWall := r5Cover_wall (F := refHull W' ζ') (δ := δ) (X := fun ω => refExcInf R L r η ψ q ω ∪ X ω)
    (M := refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (old := refChartInf c R L r η ψ)
    hγ hc hcExt hxL hxR (refHull_eqv_zero W' ζ')
    (fun ω hω => refChartInf_eqv_zero (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hω) (hψ ω hω))
    (fun ω hω hq => mem_refEventInf_eqv_zero hω hq (hcfg ω hω) (hψ ω hω))
    (fun ω => (hX₀ ω).trans subset_union_right) hInit
  exact R5Cover.of_three hHull hWall hOuter

/-- **R.5's full clause 5 for the reference family from the lift input** (bounded change pocket):
`r5Cover_ref_of_split` with
the hull cover supplied by PROVE-R5-LIFT's per-collar input `R5Ref.R7AmbientLiftWord` through
`R5Ref.r7AmbientCoverHull_of_liftWord` (the force processes follow the coupling's paths; infinite lifetime on the
test). -/
theorem r5Cover_ref_of_liftWord_split
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ : 0 < κ)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : ∀ ω i, xL ω i = 0) (hxR : ∀ ω j, xR ω j = 0) {a : ℝ} {δ : Ω → ℝ}
    {X X₀ : Ω → Set ℂ} {q : ℝ≥0}
    (hLW : R7AmbientLiftWord κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q)
    (hInit : R7InitialHeights κ ρL ρR P A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR c a
      (centredField h'' u₀') u₀' X₀) (hX₀ : ∀ ω, X₀ ω ⊆ X ω)
    (hOuter : R5Cover κ ρL ρR P A (travAll R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExc R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChart c R L r η ψ i ω).2.2)
      (refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChart c R L r η ψ) q
      (exposedOuterSel c (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q)) :
    R5Cover κ ρL ρR P A (travAll R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExc R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChart c R L r η ψ i ω).2.2)
      (refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChart c R L r η ψ) q
      (fun _ _ => True) :=
  r5Cover_ref_of_split hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG hA
    hAG hcfg hψ hc hcExt hxL hxR
      (r7AmbientCoverHull_of_liftWord hC.1.2.2.2.2 hcfg hψ hc hdom heq hζA hLW) hInit hX₀ hOuter

/-- **R.5's full clause 5 for the reference family from the lift input** (pocket opening at the flow seed):
`r5Cover_refInf_of_split` with
the hull cover supplied by PROVE-R5-LIFT's per-collar input `R5Ref.R7AmbientLiftWordInf` through
`R5Ref.r7AmbientCoverHull_of_liftWordInf` (the force processes follow the coupling's paths; infinite lifetime on the
test). -/
theorem r5Cover_refInf_of_liftWord_split
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ : 0 < κ)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : ∀ ω i, xL ω i = 0) (hxR : ∀ ω j, xR ω j = 0) {a : ℝ} {δ : Ω → ℝ}
    {X X₀ : Ω → Set ℂ} {q : ℝ≥0}
    (hLW : R7AmbientLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q)
    (hInit : R7InitialHeights κ ρL ρR P A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR c a
      (centredField h'' u₀') u₀' X₀) (hX₀ : ∀ ω, X₀ ω ⊆ X ω)
    (hOuter : R5Cover κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q
      (exposedOuterSel c (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q)) :
    R5Cover κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a (centredField h'' u₀') u₀'
      (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ') δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q
      (fun _ _ => True) :=
  r5Cover_refInf_of_split hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG hA
    hAG hcfg hψ hc hcExt hxL hxR
      (r7AmbientCoverHull_of_liftWordInf hC.1.2.2.2.2 hcfg hψ hc hdom heq hζA hLW) hInit hX₀ hOuter

end Split

/-! ### `R5Clauses` and `R5ClausesOn` for the reference family from the cover -/

section Clauses

/-- **`R5Clauses` for the reference family from the full cover** (bounded change pocket): the finite exceptional set
`refExc ∪ X`, the lattice phase, clause 3 (`R5Ref.refEvent_spec`), the increment laws for the
family and the full clause-5 cover (`R5Cover` on every coordinate, e.g. `r5Cover_ref_of_split`). -/
theorem r5Clauses_of_refCover [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
    {c : Ω → Chart} {F : ℕ → Ω → Set ℂ} {δ : Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hXf : ∀ ω, (X ω).Finite)
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hLaw : ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (F i) 0) h₀ P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A (travAll R L r η ψ) c q) h₀ P g →
      ∀ i, HasOldChartIncrementLaw P (refEvent A R L r W η ψ F q i) (refChart c R L r η ψ i)
        (relChart c (travAll R L r η ψ) q) (gB i) g)
    (hCover : R5Cover κ ρL ρR P A (travAll R L r η ψ) xL xR c a h₀ u (fun ω => cfPocket (R ω) (L ω) r) F δ
      (fun ω => refExc R L r η ψ q ω ∪ X ω) (fun i ω => (refChart c R L r η ψ i ω).2.2) (refEvent A R L r W η ψ F q)
      (refChart c R L r η ψ) q (fun _ _ => True)) :
    R5Clauses κ ρL ρR P A (travAll R L r η ψ) xL xR c a h₀ u (fun ω => cfPocket (R ω) (L ω) r) F δ
      (fun ω => refExc R L r η ψ q ω ∪ X ω) (fun i ω => (refChart c R L r η ψ i ω).2.2) (refEvent A R L r W η ψ F q)
      (refChart c R L r η ψ) q :=
  ⟨fun ω => (refExc_finite R L r η ψ q ω).union (hXf ω), hLattice, refEvent_spec hcfg hψ hc hdom heq F q, hLaw,
    r5Cover_true_iff.1 hCover⟩

/-- **`R5ClausesOn` for the reference family from the full cover** (bounded change pocket): the finite exceptional set
`refExc ∪ X`, the lattice phase, clause 3 (`R5Ref.refEvent_spec`), the conditioned increment laws for the
family and the full clause-5 cover (`R5Cover` on every coordinate, e.g. `r5Cover_ref_of_split`). -/
theorem r5ClausesOn_of_refCover [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
    {c : Ω → Chart} {F : ℕ → Ω → Set ℂ} {δ : Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hXf : ∀ ω, (X ω).Finite)
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hLaw : ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (F i) 0) h₀ P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A (travAll R L r η ψ) c q) h₀ P g →
      ∀ i, HasOldChartIncrementLawOn P (refEvent A R L r W η ψ F q i) (refChart c R L r η ψ i)
        (relChart c (travAll R L r η ψ) q) (gB i) g)
    (hCover : R5Cover κ ρL ρR P A (travAll R L r η ψ) xL xR c a h₀ u (fun ω => cfPocket (R ω) (L ω) r) F δ
      (fun ω => refExc R L r η ψ q ω ∪ X ω) (fun i ω => (refChart c R L r η ψ i ω).2.2) (refEvent A R L r W η ψ F q)
      (refChart c R L r η ψ) q (fun _ _ => True)) :
    R5ClausesOn κ ρL ρR P A (travAll R L r η ψ) xL xR c a h₀ u (fun ω => cfPocket (R ω) (L ω) r) F δ
      (fun ω => refExc R L r η ψ q ω ∪ X ω) (fun i ω => (refChart c R L r η ψ i ω).2.2) (refEvent A R L r W η ψ F q)
      (refChart c R L r η ψ) q :=
  ⟨fun ω => (refExc_finite R L r η ψ q ω).union (hXf ω), hLattice, refEvent_spec hcfg hψ hc hdom heq F q, hLaw,
    r5Cover_true_iff.1 hCover⟩

/-- **`R5Clauses` for the reference family from the full cover** (pocket opening at the flow seed): the finite
exceptional set
`refExcInf ∪ X`, the lattice phase, clause 3 (`R5Ref.refEventInf_spec`), the increment laws for the
family and the full clause-5 cover (`R5Cover` on every coordinate, e.g. `r5Cover_refInf_of_split`). -/
theorem r5Clauses_of_refInfCover [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
    {c : Ω → Chart} {F : ℕ → Ω → Set ℂ} {δ : Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hXf : ∀ ω, (X ω).Finite)
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hLaw : ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (F i) 0) h₀ P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A (travAllInf R L r η ψ) c q) h₀ P g →
      ∀ i, HasOldChartIncrementLaw P (refEventInf A R L r W η ψ F q i) (refChartInf c R L r η ψ i)
        (relChart c (travAllInf R L r η ψ) q) (gB i) g)
    (hCover : R5Cover κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a h₀ u (fun ω => cfPocket (R ω) (L ω) r) F δ
      (fun ω => refExcInf R L r η ψ q ω ∪ X ω) (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
        (refEventInf A R L r W η ψ F q)
      (refChartInf c R L r η ψ) q (fun _ _ => True)) :
    R5Clauses κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a h₀ u (fun ω => cfPocket (R ω) (L ω) r) F δ
      (fun ω => refExcInf R L r η ψ q ω ∪ X ω) (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
        (refEventInf A R L r W η ψ F q)
      (refChartInf c R L r η ψ) q :=
  ⟨fun ω => (refExcInf_finite R L r η ψ q ω).union (hXf ω), hLattice, refEventInf_spec hcfg hψ hc hdom heq F q, hLaw,
    r5Cover_true_iff.1 hCover⟩

/-- **`R5ClausesOn` for the reference family from the full cover** (pocket opening at the flow seed): the finite
exceptional set
`refExcInf ∪ X`, the lattice phase, clause 3 (`R5Ref.refEventInf_spec`), the conditioned increment laws for the
family and the full clause-5 cover (`R5Cover` on every coordinate, e.g. `r5Cover_refInf_of_split`). -/
theorem r5ClausesOn_of_refInfCover [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
    {c : Ω → Chart} {F : ℕ → Ω → Set ℂ} {δ : Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hXf : ∀ ω, (X ω).Finite)
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hLaw : ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (F i) 0) h₀ P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A (travAllInf R L r η ψ) c q) h₀ P g →
      ∀ i, HasOldChartIncrementLawOn P (refEventInf A R L r W η ψ F q i) (refChartInf c R L r η ψ i)
        (relChart c (travAllInf R L r η ψ) q) (gB i) g)
    (hCover : R5Cover κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a h₀ u (fun ω => cfPocket (R ω) (L ω) r) F δ
      (fun ω => refExcInf R L r η ψ q ω ∪ X ω) (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
        (refEventInf A R L r W η ψ F q)
      (refChartInf c R L r η ψ) q (fun _ _ => True)) :
    R5ClausesOn κ ρL ρR P A (travAllInf R L r η ψ) xL xR c a h₀ u (fun ω => cfPocket (R ω) (L ω) r) F δ
      (fun ω => refExcInf R L r η ψ q ω ∪ X ω) (fun i ω => (refChartInf c R L r η ψ i ω).2.2)
        (refEventInf A R L r W η ψ F q)
      (refChartInf c R L r η ψ) q :=
  ⟨fun ω => (refExcInf_finite R L r η ψ q ω).union (hXf ω), hLattice, refEventInf_spec hcfg hψ hc hdom heq F q, hLaw,
    r5Cover_true_iff.1 hCover⟩

end Clauses

end InteractingSLE.Sec7.R5Wall
