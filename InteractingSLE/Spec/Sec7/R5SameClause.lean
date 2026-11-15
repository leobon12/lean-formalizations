/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5SameRef

/-!
# R.5's cover clause on an R.7 test from the ambient heights and a pathwise cover

Packet PROVE-R5-SAMETIME. The fifth clause of `R5Phase.R5Clauses` (the cover: reference heights `b`, lift differences
`d` and the word identity) with the **ambient lifts** `liftB i ω = arg f′_{s_i}` (`ambLift`, `s_i` the `i`-th rational
original time) follows from `R5Same.ae_tendsto_harmRep_refHull` and a purely pathwise input:

* `ambLift` (def): the ambient lifts;
* `R7AmbientCover` (named input, pathwise — no local-set mean appears): for every current real coordinate off the jumps
  whose landing avoids `X`, a reference `i` with its pair event, collar and transition (as in `R5Clauses`), the physical
  point `z₀` of the counterflow hull inside the pocket reached by the current access (staying in the reference
  complement), the ambient image `x'` of the access off the ambient jumps at `s_i`, the limit `d` of "current lift −
  ambient lift", and the word identity `β_{s_i}(x') + χ d = phaseData(δ)(ξ) − a`;
* **`r5Clauses_cover_of_ambient`**: the fifth clause of `R5Clauses` with `liftB = ambLift W'`.

Conditional helper with a distinct name; it replaces no source theorem. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Same

open LocalSets WholeField Aux119Heights PocketStopField PocketStopWalls PocketStopWallsFin PocketCoupling PocketStop
  PocketWordPerQ PocketCoord PocketJordan PocketStopSide PocketTraversal Lemma71C R5Phase PocketUnionPt PhaseSel

variable {Ω : Type*}

/-- **The ambient lifts** at the rational original times: `arg f′_{s_i}` for the counterflow driver. -/
def ambLift (W' : ℝ≥0 → Ω → ℝ) (i : ℕ) (ω : Ω) (z : ℂ) : ℝ :=
  (logDerivFwd (fun t : ℝ => W' t.toNNReal ω) (Wire.Current.SideTest.rationalOriginalTime i) z).im

/-- **The pathwise remainder of R.5's cover on an R.7 test** (named input; no local-set mean or conditional law
appears). The data are those of `R5Clauses` at relative capacity `q`; the references are `refHull W' ζ'`. -/
def R7AmbientCover [MeasurableSpace Ω] (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ) (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ)
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart) (a : ℝ) (C : Ω → Set ℂ)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ)
    (δ : Ω → ℝ) (X : Ω → Set ℂ) (M : ℕ → Set Ω) (old : ℕ → Ω → Chart) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
      (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
    extendFrom H (relChart c γ q ω).2.1 ξ ∉ X ω →
    ∃ (i : ℕ) (x r x' d : ℝ) (z₀ : ℂ), let s := Wire.Current.SideTest.rationalOriginalTime i;
      ω ∈ M i ∧ 0 < r ∧
      (old i ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (relChart c γ q ω).dom ∧
      Tendsto (fun z => (old i ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      z₀ ∈ C ω ∩ refHull W' ζ' i ω ∧
      Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 z₀) ∧
      (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c γ q ω).2.1 y ∈ H \ liveExt A γ C (refHull W' ζ' i) 0 ω) ∧
      x' ∉ forceJumpSet (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ))
        (𝓝 (x' : ℂ)) ∧
      Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
          ambLift W' i ω ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
      forceBoundaryData κ ρL' ρR' (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) x' + chiC κ * d =
        phaseData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)
          (δ ω) ξ - a

/-- **`R5Clauses` on an R.7 test with the ambient lifts**: the first four clauses (finite exceptional sets, lattice,
reference charts, increment laws) and the pathwise cover `R7AmbientCover` give `R5Clauses` with `liftB = ambLift W'`;
the reference heights are `R5Same.ae_tendsto_harmRep_refHull`. The walls' data are those of
`R5Phase.pocketStopUnionLaw_ref`. -/
theorem r5Clauses_of_ambient {κ : ℝ} {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ} {ρL' : Fin mL → ℝ}
    {ρR' : Fin mR → ℝ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a' k c' : ℝ} {u₀ : ℂ → ℝ} {𝓕₀ : Filtration ℝ≥0 mΩ}
    {W' : ℝ≥0 → Ω → ℝ} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}
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
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ} {δ : Ω → ℝ} {X : Ω → Set ℂ} {M : ℕ → Set Ω}
    {old : ℕ → Ω → Chart} {q : ℝ≥0}
    (hXf : ∀ ω, (X ω).Finite)
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hOld : ∀ i, ∀ ω ∈ M i, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧ (old i ω).IsConformal ∧
      ((relChart c γ q ω).dom : Set ℂ) ⊆ (old i ω).dom ∧
      ((old i ω).dom : Set ℂ) = H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω)
    (hLaw : ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0)
        (centredField h'' u₀') P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) (centredField h'' u₀') P g →
      ∀ i, HasOldChartIncrementLaw P (M i) (old i) (relChart c γ q) (gB i) g)
    (hCov : R7AmbientCover κ ρL ρR ρL' ρR' P A γ xL xR c a (fun ω => cfPocket (R ω) (L ω) r) W' ζ' VL VR δ X M
      old q) :
    R5Clauses κ ρL ρR P A γ xL xR c a (centredField h'' u₀') u₀' (fun ω => cfPocket (R ω) (L ω) r)
      (refHull W' ζ') δ X (ambLift W') M old q := by
  refine ⟨hXf, hLattice, hOld, hLaw, fun gB hgB => ?_⟩
  have hH := ae_tendsto_harmRep_refHull hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hGm hG hA hAG hγ hgB
  filter_upwards [hH, hCov] with ω hHω hcovω hωA hlive ξ hξ hXξ
  obtain ⟨i, x, r', x', d, z₀, hM, hr, hcol, htr, hz₀, hinv, hev, hx', hfx, hd, hword⟩ :=
    hcovω hωA hlive ξ hξ hXξ
  exact ⟨i, x, r', _, d, hM, hr, hcol, htr, hHω hωA i z₀ hz₀ _ (ξ : ℂ) x' hx' hinv hev hfx, hd, hword⟩

end InteractingSLE.Sec7.R5Same
